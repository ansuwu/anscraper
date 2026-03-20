#!/usr/bin/env python3
"""
Canadian Deal Scraper
Automatically checks Canadian websites for deals >= 50% off retail price.
Edit sites.json to add/remove/modify websites and change the minimum discount.

Sites with "type": "browser" use Playwright (headless Chromium) to bypass
anti-bot blocking. All other sites use fast plain HTTP requests.

Features:
  - Pagination: scrapes ALL pages of each site's sale section
  - Deal history: tracks seen deals so only NEW ones trigger notifications
  - Discord webhook: sends formatted deal alerts for new deals only
"""

import json
import re
import sys
import os
import time
import csv
import hashlib
import argparse
from datetime import datetime, timedelta
from pathlib import Path
from urllib.parse import urljoin, urlparse, parse_qs, urlencode, urlunparse

# Fix Windows console encoding for Unicode output
if sys.platform == "win32":
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")
    os.environ.setdefault("PYTHONIOENCODING", "utf-8")

from dataclasses import dataclass
from concurrent.futures import ThreadPoolExecutor, as_completed

import requests
from bs4 import BeautifulSoup

# Playwright is optional – only needed for "browser" type sites
try:
    from playwright.sync_api import sync_playwright
    PLAYWRIGHT_AVAILABLE = True
except ImportError:
    PLAYWRIGHT_AVAILABLE = False

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

SITES_FILE = Path(__file__).parent / "sites.json"
HISTORY_FILE = Path(__file__).parent / "seen_deals.json"
USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/125.0.0.0 Safari/537.36"
)
REQUEST_TIMEOUT = 20   # seconds per request
BROWSER_TIMEOUT = 15   # seconds to wait for browser page load
MAX_WORKERS = 6        # parallel threads for HTTP sites
DEFAULT_MAX_PAGES = 10 # default pagination cap per site


@dataclass
class Deal:
    site: str
    title: str
    original_price: float
    sale_price: float
    discount_percent: float
    url: str
    image_url: str = ""

    def __str__(self):
        return (
            f"[{self.discount_percent:.0f}% OFF] {self.title}\n"
            f"  Was ${self.original_price:.2f} → Now ${self.sale_price:.2f}\n"
            f"  Site: {self.site}\n"
            f"  Link: {self.url}"
        )


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def load_config() -> dict:
    if not SITES_FILE.exists():
        print(f"ERROR: {SITES_FILE} not found. Please create it first.")
        sys.exit(1)
    with open(SITES_FILE, "r", encoding="utf-8") as f:
        return json.load(f)


def get_session() -> requests.Session:
    s = requests.Session()
    s.headers.update({
        "User-Agent": USER_AGENT,
        "Accept-Language": "en-CA,en;q=0.9",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    })
    return s


def fetch_page(session: requests.Session, url: str) -> BeautifulSoup | None:
    try:
        resp = session.get(url, timeout=REQUEST_TIMEOUT)
        resp.raise_for_status()
        return BeautifulSoup(resp.text, "html.parser")
    except requests.RequestException as e:
        print(f"  ⚠ Failed to fetch {url}: {e}")
        return None


def parse_price(text: str) -> float | None:
    if not text:
        return None
    # Extract the first dollar amount from the text (e.g. "$127.97" from "$150.00$127.97")
    m = re.search(r"\$?\s*(\d{1,6}(?:[,]\d{3})*(?:\.\d{2})?)", text.strip())
    if not m:
        return None
    cleaned = m.group(1).replace(",", "")
    try:
        val = float(cleaned)
        return val if val > 0 else None
    except (ValueError, TypeError):
        return None


def calc_discount(original: float, sale: float) -> float:
    if original <= 0:
        return 0.0
    return ((original - sale) / original) * 100


def extract_prices_from_element(el) -> tuple[float | None, float | None]:
    original = None
    sale = None

    # Data attributes
    for attr in ("data-original-price", "data-was-price", "data-regular-price",
                 "data-compare-at-price", "data-msrp"):
        val = el.get(attr) or ""
        p = parse_price(val)
        if p and p > 0:
            original = p
            break
    for attr in ("data-sale-price", "data-current-price", "data-price",
                 "data-final-price"):
        val = el.get(attr) or ""
        p = parse_price(val)
        if p and p > 0:
            sale = p
            break

    if original and sale:
        return original, sale

    # Strikethrough = original, other = sale
    strikethrough = el.select_one(
        "[style*='line-through'], s, strike, del, "
        ".was-price, .original-price, .regular-price, .old-price, "
        ".price-was, .price--compare, .price-original, .compare-at-price, "
        ".price-regular, .list-price, .price__was, .price-crossed"
    )
    current = el.select_one(
        ".sale-price, .special-price, .current-price, .now-price, "
        ".price-now, .price--sale, .price-sale, .price-current, "
        ".price-final, .price__now, .offer-price, .promo-price, "
        ".price-reduced"
    )

    if strikethrough:
        # Use direct text of the element to avoid concatenating child prices
        strike_text = strikethrough.string or strikethrough.get_text(separator=" ")
        original = original or parse_price(strike_text)
    if current:
        current_text = current.string or current.get_text(separator=" ")
        sale = sale or parse_price(current_text)

    if original and sale:
        return original, sale

    # All price-like strings: largest = original, smallest = sale
    # Skip dollar amounts in savings/rewards/shipping/percentage context
    skip_words = ("save", "earn", "reward", "cashback", "money", "shipping",
                  "off)", "coupon", "credit", "bonus", "free", "deposit",
                  "% off", "percent", "up to")
    price_texts = el.find_all(string=re.compile(r"\$\s*\d+[\d,.]*"))
    prices = []
    for pt in price_texts:
        # Check surrounding text for non-price context
        parent_text = pt.parent.get_text().lower() if pt.parent else ""
        if any(w in parent_text for w in skip_words):
            continue
        # Skip if the text itself contains a percentage (e.g. "Save 19% ($180.00)")
        full_text = pt.strip() if isinstance(pt, str) else str(pt)
        if "%" in (pt.parent.get_text() if pt.parent else ""):
            # Only skip if the dollar amount is near a percentage sign
            parent_full = pt.parent.get_text() if pt.parent else ""
            if re.search(r"\d+\s*%", parent_full):
                continue
        p = parse_price(pt)
        if p and p > 0:
            prices.append(p)
    prices = sorted(set(prices))
    if len(prices) >= 2:
        return prices[-1], prices[0]

    return original, sale


# ---------------------------------------------------------------------------
# Pagination helpers
# ---------------------------------------------------------------------------

def make_page_url(base_url: str, page_num: int) -> str:
    """Append or replace ?page=N in a URL."""
    parsed = urlparse(base_url)
    params = parse_qs(parsed.query, keep_blank_values=True)
    params["page"] = [str(page_num)]
    new_query = urlencode(params, doseq=True)
    return urlunparse(parsed._replace(query=new_query))


# ---------------------------------------------------------------------------
# Browser-based fetching (Playwright)
# ---------------------------------------------------------------------------

def fetch_page_browser(browser, url: str) -> BeautifulSoup | None:
    """Load a page in a real Chromium browser and return parsed HTML."""
    context = None
    try:
        context = browser.new_context(
            user_agent=USER_AGENT,
            locale="en-CA",
            viewport={"width": 1920, "height": 1080},
        )
        page = context.new_page()
        page.goto(url, wait_until="domcontentloaded", timeout=BROWSER_TIMEOUT * 1000)
        # Wait a bit for JS to render product cards
        page.wait_for_timeout(3000)
        html = page.content()
        return BeautifulSoup(html, "html.parser")
    except Exception as e:
        print(f"  ⚠ Browser failed for {url}: {e}")
        return None
    finally:
        if context:
            context.close()


# ---------------------------------------------------------------------------
# Deal history (seen_deals.json)
# ---------------------------------------------------------------------------

def deal_hash(deal: Deal) -> str:
    """Generate a unique hash for a deal based on site + title + price."""
    key = f"{deal.site}|{deal.title.lower().strip()}|{deal.sale_price:.2f}"
    return hashlib.md5(key.encode("utf-8")).hexdigest()


def load_history() -> dict:
    """Load seen deals history from disk."""
    if not HISTORY_FILE.exists():
        return {}
    try:
        with open(HISTORY_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data.get("deals", {})
    except (json.JSONDecodeError, IOError):
        return {}


def save_history(history: dict):
    """Save seen deals history to disk."""
    with open(HISTORY_FILE, "w", encoding="utf-8") as f:
        json.dump({"deals": history}, f, indent=2, ensure_ascii=False)


def purge_expired(history: dict, days: int) -> dict:
    """Remove deals older than N days from history."""
    cutoff = (datetime.now() - timedelta(days=days)).isoformat()
    return {
        h: info for h, info in history.items()
        if info.get("first_seen", "") > cutoff
    }


# ---------------------------------------------------------------------------
# Discord webhook
# ---------------------------------------------------------------------------

def send_discord(deals: list[Deal], webhook_url: str, max_per_run: int = 25):
    """Send new deals to a Discord webhook as formatted embeds."""
    if not webhook_url or not deals:
        return

    # Sort by discount descending
    deals = sorted(deals, key=lambda d: d.discount_percent, reverse=True)

    extra = 0
    if max_per_run > 0 and len(deals) > max_per_run:
        extra = len(deals) - max_per_run
        deals = deals[:max_per_run]

    sites = len(set(d.site for d in deals))
    total_count = len(deals) + extra

    # Send summary message first
    summary = {
        "content": f"**Found {total_count} new deal(s) across {sites} site(s)**"
    }
    try:
        requests.post(webhook_url, json=summary, timeout=10)
        time.sleep(1)
    except Exception as e:
        print(f"  ⚠ Discord summary failed: {e}")
        return

    # Send deals in batches of 10 embeds (Discord limit)
    for i in range(0, len(deals), 10):
        batch = deals[i:i + 10]
        embeds = []
        for d in batch:
            # Color based on discount
            if d.discount_percent >= 80:
                color = 0xFF0000  # red
            elif d.discount_percent >= 60:
                color = 0xFF8C00  # orange
            else:
                color = 0xFFD700  # yellow

            orig = f"${d.original_price:.2f}" if d.original_price else "N/A"
            sale = f"${d.sale_price:.2f}" if d.sale_price else "N/A"

            embed = {
                "title": f"[{d.discount_percent:.0f}% OFF] {d.title[:200]}",
                "url": d.url,
                "description": f"Was {orig} → Now **{sale}**\nSite: {d.site}",
                "color": color,
            }
            if d.image_url and d.image_url.startswith("http"):
                embed["thumbnail"] = {"url": d.image_url}
            embeds.append(embed)

        payload = {"embeds": embeds}

        # Footer on last batch if there are extra deals
        if extra > 0 and i + 10 >= len(deals):
            embeds[-1]["footer"] = {"text": f"...and {extra} more deal(s) not shown"}

        try:
            resp = requests.post(webhook_url, json=payload, timeout=10)
            if resp.status_code == 429:
                retry_after = resp.json().get("retry_after", 2)
                time.sleep(retry_after)
                requests.post(webhook_url, json=payload, timeout=10)
        except Exception as e:
            print(f"  ⚠ Discord batch failed: {e}")

        if i + 10 < len(deals):
            time.sleep(1)  # rate limit between batches

    print(f"  Sent {len(deals)} deal(s) to Discord" +
          (f" (+{extra} more not shown)" if extra else ""))


# ---------------------------------------------------------------------------
# Site-specific scrapers
# ---------------------------------------------------------------------------

def scrape_redflagdeals(session, site, min_discount, browser=None, max_pages=5, paginate=True):
    """Scrape RedFlagDeals forum pages."""
    deals = []
    base = "https://forums.redflagdeals.com"
    base_url = site["url"]
    pages_to_scrape = max_pages if paginate else 1
    pages_to_scrape = min(pages_to_scrape, 5)  # RFD: cap at 5 forum pages

    for page_num in range(1, pages_to_scrape + 1):
        url = base_url if page_num == 1 else make_page_url(base_url, page_num)
        soup = fetch_page(session, url)
        if not soup:
            break

        cards = soup.select("li.topic-card")
        if not cards:
            break

        for card in cards:
            title_el = card.select_one(".thread_title, .thread_title_link, .topic_title_link")
            if not title_el:
                continue
            title = title_el.get_text(strip=True)

            link_el = card.select_one("a.topic-card-info, a.thread_info")
            link = urljoin(base, link_el.get("href", "")) if link_el else url

            dealer_el = card.select_one(".dealer_name")
            dealer = dealer_el.get_text(strip=True) if dealer_el else ""
            if dealer:
                title = f"[{dealer}] {title}"

            savings_el = card.select_one(".savings")
            orig, sale, discount = 0.0, 0.0, 0.0

            if savings_el:
                savings_text = savings_el.get_text(strip=True)
                pct_match = re.search(r"(\d+)\s*%", savings_text)
                if pct_match:
                    discount = float(pct_match.group(1))
                price_nums = re.findall(r"[\d]+\.[\d]{2}", savings_text)
                if len(price_nums) >= 2:
                    sale = float(price_nums[0])
                    orig = float(price_nums[1])
                    if orig > sale > 0:
                        discount = max(discount, calc_discount(orig, sale))

            if discount >= min_discount:
                deals.append(Deal(
                    site=site["name"], title=title[:120],
                    original_price=orig, sale_price=sale,
                    discount_percent=discount, url=link,
                ))

    return deals


def scrape_generic(session, site, min_discount, browser=None, max_pages=10, paginate=True):
    """Generic scraper using plain HTTP requests, with pagination."""
    all_deals = []
    base_url = site["url"]
    pages_to_scrape = max_pages if paginate else 1

    prev_count = None
    for page_num in range(1, pages_to_scrape + 1):
        url = base_url if page_num == 1 else make_page_url(base_url, page_num)
        soup = fetch_page(session, url)
        if not soup:
            break

        page_deals = _parse_generic_soup(soup, site, min_discount)

        if not page_deals:
            break  # no products found on this page, stop

        # Detect duplicate-heavy page (>80% overlap = we've looped)
        if all_deals:
            new_titles = {d.title.lower() for d in page_deals}
            existing_titles = {d.title.lower() for d in all_deals}
            overlap = len(new_titles & existing_titles)
            if overlap > len(new_titles) * 0.8:
                break

        all_deals.extend(page_deals)

        # If this page has fewer cards than page 1, we've likely hit the last page
        if prev_count is not None and len(page_deals) < prev_count * 0.5:
            break
        prev_count = len(page_deals)

    return all_deals


def scrape_browser(session, site, min_discount, browser=None, max_pages=10, paginate=True):
    """Generic scraper using Playwright headless browser, with pagination."""
    if not browser:
        print(f"  ⚠ {site['name']}: Playwright not available, skipping")
        return []

    all_deals = []
    base_url = site["url"]
    pages_to_scrape = max_pages if paginate else 1

    prev_count = None
    for page_num in range(1, pages_to_scrape + 1):
        url = base_url if page_num == 1 else make_page_url(base_url, page_num)
        soup = fetch_page_browser(browser, url)
        if not soup:
            break

        page_deals = _parse_generic_soup(soup, site, min_discount)

        if not page_deals:
            break

        # Detect duplicate-heavy page
        if all_deals:
            new_titles = {d.title.lower() for d in page_deals}
            existing_titles = {d.title.lower() for d in all_deals}
            overlap = len(new_titles & existing_titles)
            if overlap > len(new_titles) * 0.8:
                break

        all_deals.extend(page_deals)

        if prev_count is not None and len(page_deals) < prev_count * 0.5:
            break
        prev_count = len(page_deals)

    return all_deals


def _parse_generic_soup(soup, site, min_discount):
    """Shared logic to extract deals from a BeautifulSoup page."""
    deals = []
    card_selectors = [
        "[class*='product-card']", "[class*='product-tile']",
        "[class*='product-item']", "[class*='productCard']",
        "[class*='deal-card']", "[class*='deal-item']",
        "[class*='grid-item']", "[class*='item-card']",
        ".product", "article",
        "li[class*='product']", "[data-product]", "[data-item]",
    ]
    cards = []
    for sel in card_selectors:
        cards = soup.select(sel)
        if len(cards) >= 2:
            break

    if not cards:
        for el in soup.find_all(True):
            texts = el.find_all(string=re.compile(r"\$\s*\d"))
            if len(texts) >= 2 and len(el.get_text()) < 500:
                cards.append(el)
        cards = cards[:50]

    for card in cards[:100]:
        title_el = card.select_one(
            "h2, h3, h4, a[class*='title'], a[class*='name'], "
            "[class*='title'], [class*='name'], [class*='description']"
        )
        if not title_el:
            continue
        title = title_el.get_text(strip=True)
        if len(title) < 4 or len(title) > 200:
            continue

        # Find product link — prefer title link, then any link in the card
        link_el = None
        if title_el.name == "a":
            link_el = title_el
        elif title_el.find_parent("a"):
            link_el = title_el.find_parent("a")
        if not link_el:
            link_el = card.select_one("a[href]")
        link = site["url"]
        if link_el and link_el.get("href"):
            href = link_el["href"]
            if href.startswith(("http://", "https://")):
                link = href
            elif href.startswith("/"):
                link = urljoin(site["url"], href)

        orig, sale = extract_prices_from_element(card)

        discount = 0.0
        pct_el = card.select_one(
            "[class*='discount'], [class*='saving'], [class*='badge'], "
            "[class*='percent'], [class*='off']"
        )
        if pct_el:
            m = re.search(r"(\d+)\s*%", pct_el.get_text())
            if m:
                discount = float(m.group(1))

        # Sanity check: reject obviously bad price parses
        if orig and sale and sale < orig:
            if orig > 50000:
                continue  # unrealistic original price
            # If the "sale" price is suspiciously low relative to original,
            # it's likely a misparse (e.g. picking up "19" from "Save 19%")
            if sale > 0 and orig / sale > 10 and sale < 50:
                continue  # e.g. $949 / $19 = 50x, likely wrong
            if sale > 0 and orig / sale > 15:
                continue  # even for higher sale prices, 15x ratio is suspect
            discount = max(discount, calc_discount(orig, sale))

        if discount >= min_discount:
            img_el = card.select_one("img[src]")
            img = img_el["src"] if img_el else ""
            deals.append(Deal(
                site=site["name"], title=title[:120],
                original_price=orig or 0, sale_price=sale or 0,
                discount_percent=discount, url=link, image_url=img,
            ))
    return deals


# ---------------------------------------------------------------------------
# Dispatcher
# ---------------------------------------------------------------------------

SCRAPERS = {
    "generic": scrape_generic,
    "browser": scrape_browser,
}


def scrape_site(site: dict, min_discount: float, browser=None,
                max_pages: int = 10, paginate: bool = True) -> list[Deal]:
    scraper_type = site.get("type", "generic")
    scraper_fn = SCRAPERS.get(scraper_type, scrape_generic)
    session = get_session()

    # Per-site pagination overrides
    site_paginate = site.get("paginate", paginate)
    site_max_pages = site.get("max_pages", max_pages)

    try:
        return scraper_fn(session, site, min_discount, browser=browser,
                          max_pages=site_max_pages, paginate=site_paginate)
    except Exception as e:
        print(f"  ⚠ Error scraping {site['name']}: {e}")
        return []


# ---------------------------------------------------------------------------
# Output formatters
# ---------------------------------------------------------------------------

def print_deals(deals: list[Deal]):
    if not deals:
        print("\nNo deals found matching your criteria.")
        return
    deals.sort(key=lambda d: d.discount_percent, reverse=True)
    print(f"\n{'=' * 70}")
    print(f" Found {len(deals)} deal(s) at {len(set(d.site for d in deals))} site(s)")
    print(f"{'=' * 70}")
    current_site = None
    for d in deals:
        if d.site != current_site:
            current_site = d.site
            print(f"\n--- {current_site} ---")
        print(f"\n{d}")
    print(f"\n{'=' * 70}\n")


def save_csv(deals: list[Deal], path: str):
    deals.sort(key=lambda d: d.discount_percent, reverse=True)
    with open(path, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["Discount %", "Title", "Original Price", "Sale Price", "Site", "URL", "Image URL"])
        for d in deals:
            writer.writerow([
                f"{d.discount_percent:.0f}%", d.title,
                f"${d.original_price:.2f}" if d.original_price else "",
                f"${d.sale_price:.2f}" if d.sale_price else "",
                d.site, d.url, d.image_url,
            ])
    print(f"Saved {len(deals)} deals to {path}")


def save_html(deals: list[Deal], path: str):
    deals.sort(key=lambda d: d.discount_percent, reverse=True)
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M")
    rows = []
    for d in deals:
        orig = f"${d.original_price:.2f}" if d.original_price else "N/A"
        sale = f"${d.sale_price:.2f}" if d.sale_price else "N/A"
        rows.append(f"""
        <tr>
          <td class="discount">{d.discount_percent:.0f}%</td>
          <td><a href="{d.url}" target="_blank">{d.title}</a></td>
          <td class="price-old">{orig}</td>
          <td class="price-new">{sale}</td>
          <td>{d.site}</td>
        </tr>""")

    html = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Canadian Deals Report – {timestamp}</title>
<style>
  * {{ margin: 0; padding: 0; box-sizing: border-box; }}
  body {{ font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
         background: #0f1117; color: #e0e0e0; padding: 20px; }}
  h1 {{ text-align: center; margin: 20px 0; color: #ff6b6b; }}
  .meta {{ text-align: center; color: #888; margin-bottom: 20px; }}
  table {{ width: 100%; border-collapse: collapse; margin-top: 10px; }}
  th {{ background: #1a1d2e; color: #ff6b6b; padding: 12px 8px; text-align: left;
       position: sticky; top: 0; cursor: pointer; }}
  th:hover {{ background: #252840; }}
  td {{ padding: 10px 8px; border-bottom: 1px solid #222; }}
  tr:hover {{ background: #1a1d2e; }}
  a {{ color: #6bb5ff; text-decoration: none; }}
  a:hover {{ text-decoration: underline; }}
  .discount {{ font-weight: bold; color: #ff4444; font-size: 1.1em; text-align: center; }}
  .price-old {{ text-decoration: line-through; color: #888; }}
  .price-new {{ font-weight: bold; color: #44ff88; }}
  .filter-bar {{ text-align: center; margin: 15px 0; }}
  .filter-bar input {{ padding: 8px 16px; border-radius: 6px; border: 1px solid #333;
                       background: #1a1d2e; color: #e0e0e0; width: 300px; font-size: 14px; }}
</style>
</head>
<body>
  <h1>Canadian Deals &ge;50% Off</h1>
  <p class="meta">Generated {timestamp} &mdash; {len(deals)} deals found</p>
  <div class="filter-bar">
    <input type="text" id="search" placeholder="Filter deals..." oninput="filterTable()">
  </div>
  <table id="deals">
    <thead>
      <tr>
        <th onclick="sortTable(0)" style="width:80px">Discount</th>
        <th onclick="sortTable(1)">Product</th>
        <th onclick="sortTable(2)" style="width:100px">Was</th>
        <th onclick="sortTable(3)" style="width:100px">Now</th>
        <th onclick="sortTable(4)" style="width:160px">Site</th>
      </tr>
    </thead>
    <tbody>
      {''.join(rows)}
    </tbody>
  </table>
  <script>
    function filterTable() {{
      const q = document.getElementById('search').value.toLowerCase();
      document.querySelectorAll('#deals tbody tr').forEach(row => {{
        row.style.display = row.textContent.toLowerCase().includes(q) ? '' : 'none';
      }});
    }}
    let sortDir = {{}};
    function sortTable(col) {{
      const tbody = document.querySelector('#deals tbody');
      const rows = Array.from(tbody.rows);
      sortDir[col] = !sortDir[col];
      rows.sort((a, b) => {{
        let x = a.cells[col].textContent.trim();
        let y = b.cells[col].textContent.trim();
        const nx = parseFloat(x.replace(/[^\\d.-]/g, ''));
        const ny = parseFloat(y.replace(/[^\\d.-]/g, ''));
        if (!isNaN(nx) && !isNaN(ny)) return sortDir[col] ? nx - ny : ny - nx;
        return sortDir[col] ? x.localeCompare(y) : y.localeCompare(x);
      }});
      rows.forEach(r => tbody.appendChild(r));
    }}
  </script>
</body>
</html>"""
    with open(path, "w", encoding="utf-8") as f:
        f.write(html)
    print(f"Saved HTML report to {path}")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def list_sites():
    config = load_config()
    print(f"\nConfigured sites ({len(config['sites'])} total):\n")
    print(f"  {'#':<4} {'Enabled':<9} {'Type':<10} {'Name':<30} Description")
    print(f"  {'─'*4} {'─'*7}   {'─'*8}  {'─'*28}  {'─'*40}")
    for i, s in enumerate(config["sites"], 1):
        status = "Y" if s.get("enabled", True) else "N"
        stype = s.get("type", "generic")
        print(f"  {i:<4} {status:<9} {stype:<10} {s['name']:<30} {s.get('description', '')}")
    print(f"\nMinimum discount: {config.get('minimum_discount_percent', 50)}%")
    print(f"Config file: {SITES_FILE.resolve()}")
    print(f"Playwright available: {'Yes' if PLAYWRIGHT_AVAILABLE else 'No (pip install playwright && python -m playwright install chromium)'}\n")


def main():
    parser = argparse.ArgumentParser(
        description="Canadian Deal Scraper – finds deals >=50%% off across Canadian websites",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
examples:
  python scraper.py                                    # scrape all sites
  python scraper.py --no-browser                       # fast mode, HTTP only
  python scraper.py --keywords "laptop,monitor,TV"     # only show these products
  python scraper.py --exclude "refurbished,renewed"    # hide these products
  python scraper.py --price-min 20 --price-max 200     # sale price between $20-$200
  python scraper.py --category electronics,gaming      # only scrape these categories
  python scraper.py --max-results 20                   # show top 20 deals only
  python scraper.py --max-per-site 5                   # max 5 deals from each site
  python scraper.py --min 60                           # minimum 60%% discount
  python scraper.py --html report.html                 # save HTML report
  python scraper.py --csv deals.csv                    # save CSV file
  python scraper.py --discord URL                      # send new deals to Discord
  python scraper.py --no-pagination                    # only scrape page 1 (faster)
  python scraper.py --max-pages 3                      # max 3 pages per site
  python scraper.py --reset-history                    # clear seen deals history
        """,
    )
    parser.add_argument("--list", action="store_true", help="List all configured sites and exit")
    parser.add_argument("--csv", metavar="FILE", help="Save results to a CSV file")
    parser.add_argument("--html", metavar="FILE", help="Save results to an HTML report")
    parser.add_argument("--min", type=float, metavar="PCT", help="Override minimum discount percentage")
    parser.add_argument("--max-results", type=int, metavar="N", help="Max total deals to show (default from config)")
    parser.add_argument("--max-per-site", type=int, metavar="N", help="Max deals per site (default from config)")
    parser.add_argument("--price-min", type=float, metavar="$", help="Only show deals with sale price >= this")
    parser.add_argument("--price-max", type=float, metavar="$", help="Only show deals with sale price <= this")
    parser.add_argument("--keywords", metavar="WORDS", help="Only show deals matching these keywords (comma-separated)")
    parser.add_argument("--exclude", metavar="WORDS", help="Hide deals matching these keywords (comma-separated)")
    parser.add_argument("--category", metavar="CATS", help="Only scrape these categories (comma-separated, e.g. electronics,fashion)")
    parser.add_argument("--sites", metavar="NAMES", help="Comma-separated list of site names to scrape")
    parser.add_argument("--workers", type=int, default=MAX_WORKERS, help=f"Number of parallel threads (default {MAX_WORKERS})")
    parser.add_argument("--no-browser", action="store_true", help="Skip sites that require a browser (faster)")
    # New: pagination
    parser.add_argument("--no-pagination", action="store_true", help="Only scrape page 1 of each site (faster, like old behavior)")
    parser.add_argument("--max-pages", type=int, metavar="N", help="Max pages to scrape per site (default from config)")
    # New: Discord
    parser.add_argument("--discord", metavar="URL", help="Discord webhook URL (overrides config)")
    parser.add_argument("--notify-max", type=int, metavar="N", help="Max Discord notifications per run (default from config)")
    # New: history
    parser.add_argument("--reset-history", action="store_true", help="Clear seen deals history and exit")
    args = parser.parse_args()

    if args.reset_history:
        if HISTORY_FILE.exists():
            HISTORY_FILE.unlink()
            print("Deal history cleared.")
        else:
            print("No deal history to clear.")
        return

    if args.list:
        list_sites()
        return

    config = load_config()
    min_discount = args.min if args.min is not None else config.get("minimum_discount_percent", 50)

    # Build filters from config + CLI overrides
    max_results = args.max_results if args.max_results is not None else config.get("max_results", 0)
    max_per_site = args.max_per_site if args.max_per_site is not None else config.get("max_results_per_site", 0)
    price_min = args.price_min if args.price_min is not None else config.get("price_min", 0)
    price_max = args.price_max if args.price_max is not None else config.get("price_max", 0)

    # Pagination settings
    paginate = not args.no_pagination
    max_pages = args.max_pages if args.max_pages is not None else config.get("default_max_pages", DEFAULT_MAX_PAGES)

    # Discord settings
    discord_url = args.discord or config.get("discord_webhook_url", "")
    notify_max = args.notify_max if args.notify_max is not None else config.get("notify_max_per_run", 25)
    history_expiry = config.get("history_expiry_days", 7)

    keywords = []
    if args.keywords:
        keywords = [k.strip().lower() for k in args.keywords.split(",")]
    elif config.get("keywords"):
        keywords = [k.lower() for k in config["keywords"]]

    exclude_keywords = []
    if args.exclude:
        exclude_keywords = [k.strip().lower() for k in args.exclude.split(",")]
    elif config.get("exclude_keywords"):
        exclude_keywords = [k.lower() for k in config["exclude_keywords"]]

    categories = []
    if args.category:
        categories = [c.strip().lower() for c in args.category.split(",")]
    elif config.get("categories"):
        categories = [c.lower() for c in config["categories"]]

    # Filter sites
    sites = [s for s in config["sites"] if s.get("enabled", True)]
    if args.sites:
        selected = {n.strip().lower() for n in args.sites.split(",")}
        sites = [s for s in sites if s["name"].lower() in selected]
    if categories:
        sites = [s for s in sites if s.get("category", "").lower() in categories]

    if not sites:
        print("No sites to scrape. Check sites.json or --sites / --category filter.")
        return

    # Split into HTTP sites and browser sites
    http_sites = [s for s in sites if s.get("type", "generic") != "browser"]
    browser_sites = [s for s in sites if s.get("type", "generic") == "browser"]

    if args.no_browser:
        browser_sites = []

    total = len(http_sites) + len(browser_sites)
    print(f"\nCanadian Deal Scraper")
    print(f"   Minimum discount: {min_discount}% off")
    if paginate:
        print(f"   Pagination: up to {max_pages} pages per site")
    else:
        print(f"   Pagination: disabled (page 1 only)")
    if keywords:
        print(f"   Keywords: {', '.join(keywords)}")
    if exclude_keywords:
        print(f"   Excluding: {', '.join(exclude_keywords)}")
    if price_min or price_max:
        prange = f"${price_min:.0f}" if price_min else "$0"
        prange += f" - ${price_max:.0f}" if price_max else "+"
        print(f"   Price range: {prange}")
    if max_per_site:
        print(f"   Max per site: {max_per_site}")
    if max_results:
        print(f"   Max total: {max_results}")
    if discord_url:
        print(f"   Discord: enabled (max {notify_max} per run)")
    print(f"   Scanning {total} site(s) ({len(http_sites)} HTTP + {len(browser_sites)} browser)...\n")

    all_deals: list[Deal] = []
    start_time = time.time()

    # --- Phase 1: HTTP sites (fast, parallel) ---
    if http_sites:
        with ThreadPoolExecutor(max_workers=args.workers) as executor:
            futures = {
                executor.submit(scrape_site, site, min_discount, None, max_pages, paginate): site
                for site in http_sites
            }
            for future in as_completed(futures):
                site = futures[future]
                try:
                    deals = future.result()
                    if deals:
                        print(f"  + {site['name']}: {len(deals)} deal(s)")
                    else:
                        print(f"  . {site['name']}: no qualifying deals")
                    all_deals.extend(deals)
                except Exception as e:
                    print(f"  x {site['name']}: error - {e}")

    # --- Phase 2: Browser sites (Playwright, sequential – sync API is single-threaded) ---
    if browser_sites:
        if not PLAYWRIGHT_AVAILABLE:
            print("\n  Playwright not installed. Skipping browser sites.")
            print("    Install with: pip install playwright && python -m playwright install chromium")
        else:
            print(f"\n  Loading {len(browser_sites)} browser site(s) (sequential)...")
            with sync_playwright() as pw:
                browser = pw.chromium.launch(headless=True)
                try:
                    for site in browser_sites:
                        try:
                            deals = scrape_site(site, min_discount, browser, max_pages, paginate)
                            if deals:
                                print(f"  + {site['name']}: {len(deals)} deal(s) [browser]")
                            else:
                                print(f"  . {site['name']}: no qualifying deals [browser]")
                            all_deals.extend(deals)
                        except Exception as e:
                            print(f"  x {site['name']}: error - {e}")
                finally:
                    browser.close()

    elapsed = time.time() - start_time
    print(f"\nScan completed in {elapsed:.1f}s")

    # Deduplicate
    seen = set()
    unique_deals = []
    for d in all_deals:
        key = (d.site, d.title.lower())
        if key not in seen:
            seen.add(key)
            unique_deals.append(d)

    # --- Apply filters ---
    filtered = unique_deals

    # Keyword filter (include)
    if keywords:
        filtered = [d for d in filtered
                    if any(k in d.title.lower() for k in keywords)]

    # Keyword filter (exclude)
    if exclude_keywords:
        filtered = [d for d in filtered
                    if not any(k in d.title.lower() for k in exclude_keywords)]

    # Price range filter
    if price_min > 0:
        filtered = [d for d in filtered if d.sale_price >= price_min]
    if price_max > 0:
        filtered = [d for d in filtered if d.sale_price <= price_max]

    # Sort by discount descending
    filtered.sort(key=lambda d: d.discount_percent, reverse=True)

    # Cap per site
    if max_per_site > 0:
        site_counts: dict[str, int] = {}
        capped = []
        for d in filtered:
            site_counts[d.site] = site_counts.get(d.site, 0) + 1
            if site_counts[d.site] <= max_per_site:
                capped.append(d)
        filtered = capped

    # Cap total results
    if max_results > 0:
        filtered = filtered[:max_results]

    if len(filtered) < len(unique_deals):
        print(f"  Filtered: {len(unique_deals)} deals -> {len(filtered)} after filters")

    # --- Deal history & Discord notifications ---
    history = load_history()
    history = purge_expired(history, history_expiry)

    new_deals = []
    for d in filtered:
        h = deal_hash(d)
        if h not in history:
            new_deals.append(d)
            history[h] = {
                "title": d.title,
                "site": d.site,
                "first_seen": datetime.now().isoformat(),
                "sale_price": d.sale_price,
            }

    save_history(history)

    known_count = len(filtered) - len(new_deals)
    if new_deals:
        print(f"\n  {len(new_deals)} NEW deal(s), {known_count} previously seen")
    elif filtered:
        print(f"\n  All {len(filtered)} deal(s) previously seen (no new deals)")

    # Print ALL deals to console/files
    print_deals(filtered)

    if args.csv:
        save_csv(filtered, args.csv)
    if args.html:
        save_html(filtered, args.html)

    # Send only NEW deals to Discord
    if discord_url and new_deals:
        print(f"\n  Sending {len(new_deals)} new deal(s) to Discord...")
        send_discord(new_deals, discord_url, notify_max)
    elif discord_url and not new_deals:
        print(f"\n  No new deals to send to Discord.")


if __name__ == "__main__":
    main()
