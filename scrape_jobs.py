#!/usr/bin/env python3
"""
MassRobotics Job Listing Scraper
Scrapes job listings from MassRobotics resident startup websites and generates jobs.html and index.html.
"""

import argparse
import json
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
from threading import Lock, local
from urllib.parse import urljoin, urlparse

import requests
from bs4 import BeautifulSoup

try:
    from playwright.sync_api import sync_playwright
    PLAYWRIGHT_AVAILABLE = True
except ImportError:
    PLAYWRIGHT_AVAILABLE = False

MASSROBOTICS_URL = "https://www.massrobotics.org/startups/massrobotics-resident-startups/"
OUTPUT_FILES = ["jobs.html", "index.html"]
REQUEST_TIMEOUT = 10
REQUEST_DELAY = 0.5  # seconds between requests
RATE_LIMIT_RETRIES = 3  # retries after a 429 Too Many Requests

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (compatible; MassRoboticsJobBot/1.0; "
        "+https://www.massrobotics.org)"
    )
}

# Career-related URL path fragments to try
CAREER_PATHS = [
    "/careers",
    "/jobs",
    "/open-positions",
    "/openings",
    "/join",
    "/join-us",
    "/work-with-us",
    "/opportunities",
    "/hiring",
    "/careers/",
    "/jobs/",
    "/about/careers",
    "/about/jobs",
    "/company/careers",
    "/company/jobs",
    "/team/careers",
    "/team/jobs",
    "/positions",
]

# Keywords that indicate a link leads to a careers page
CAREER_LINK_KEYWORDS = [
    "career", "careers", "job", "jobs", "hiring", "join us", "join our team",
    "work with us", "open position", "open role", "we're hiring", "we are hiring",
    "opportunities", "openings", "positions", "employment",
]

# Job title keywords compiled as a regex with word boundaries to avoid
# substring matches like "intern" inside "International".
# Phrases like "head of" and abbreviations like "vp" use simpler patterns.
_KW_WORD = [
    "engineer", "manager", "director", "designer", "scientist", "analyst",
    "developer", "lead", "intern", "internship", "specialist", "coordinator",
    "researcher", "technician", "officer", "architect", "consultant",
    "associate", "principal", "staff", "senior", "junior",
    "software", "hardware", "mechanical", "electrical",
    "robotics", "embedded", "firmware", "recruiter",
    "executive", "representative", "operator", "writer", "counsel",
]
_KW_PHRASE = [
    r"head of", r"\bvp\b", r"\bcto\b", r"\bceo\b", r"\bcoo\b", r"\bcfo\b",
]
JOB_KEYWORD_RE = re.compile(
    r"\b(?:" + "|".join(re.escape(k) for k in _KW_WORD) + r")\b"
    + "|" + "|".join(_KW_PHRASE),
    re.IGNORECASE,
)

# Stronger keywords that unambiguously indicate a job listing (used for validation).
# "developer" excluded — it appears too often in product names like "Developer Kit".
STRONG_KEYWORD_RE = re.compile(
    r"\b(?:engineer|manager|director|designer|scientist|analyst|"
    r"researcher|architect|technician|recruiter|coordinator|specialist|"
    r"intern(?:ship)?)\b",
    re.IGNORECASE,
)

# Boilerplate phrases that are NOT job titles
BOILERPLATE_PHRASES = [
    "we're hiring", "we are hiring", "join our team", "join us", "apply now",
    "apply here", "see all jobs", "view all jobs", "all open positions",
    "view openings", "learn more", "read more", "get in touch", "contact us",
    "send your resume", "submit application", "no open positions",
    "no current openings", "check back", "follow us", "about us",
    "our mission", "our values", "our culture", "life at", "benefits",
    "perks", "why work", "what we offer",
]

# Navigation words that are NOT job titles
NAV_WORDS = {
    "home", "about", "contact", "blog", "news", "team", "press", "investors",
    "partners", "customers", "solutions", "products", "services", "platform",
    "technology", "research", "resources", "support", "login", "sign in",
    "sign up", "get started", "request demo", "book a demo", "schedule",
    "privacy", "terms", "cookie", "sitemap", "faq",
}

# Domains to exclude from the resident list (non-startup links on the page)
RESIDENT_DOMAIN_BLACKLIST = {
    "defense.gov", "eepurl.com", "mailchimp.com", "linkedin.com",
    "twitter.com", "x.com", "facebook.com", "instagram.com", "youtube.com",
    "google.com", "apple.com", "massrobotics.org",
}

# Known job board domains (for validating careers URL redirects)
KNOWN_JOB_BOARDS = {
    "lever.co", "greenhouse.io", "ashbyhq.com", "bamboohr.com",
    "workday.com", "myworkday.com", "icims.com", "smartrecruiters.com",
    "jobvite.com", "recruitee.com", "notion.so", "odoo.com", "workable.com",
    "rippling.com",
}

# Regex to find a direct href to a job board with a reliable API in page source.
# When a company's /careers page links out to Workable/Lever/Greenhouse, we
# prefer the board URL so the displayed careers link is accurate.
# NOTE: Ashby and BambooHR are intentionally excluded — their pages are
# JS-rendered; we get better results scraping the company's own careers page
# (where the jobs are typically rendered server-side).
_BOARD_HREF_RE = re.compile(
    r'https?://(?:apply\.workable\.com|jobs\.lever\.co|boards\.greenhouse\.io'
    r'|ats\.rippling\.com/[A-Za-z0-9_-]+)/[A-Za-z0-9_-]+/?',
    re.IGNORECASE,
)

# Domains that are never valid career page destinations (parked/expired domains)
CAREERS_DOMAIN_BLACKLIST = {
    "expireddomains.com", "sedoparking.com", "godaddy.com",
    "parking.com", "dan.com", "sedo.com", "namecheap.com",
}

# Social media and job aggregator sites — never treat as a company's own careers page
SOCIAL_AND_AGGREGATOR_DOMAINS = {
    "linkedin.com", "twitter.com", "x.com", "facebook.com", "instagram.com",
    "youtube.com", "glassdoor.com", "indeed.com", "ziprecruiter.com",
    "monster.com", "wellfound.com", "angel.co", "builtinboston.com",
}

# Link text that unambiguously means "this company's own careers page"
# (short, primary-nav terms). When a link has one of these exact texts,
# we follow it to ANY external domain (not just known boards), since the
# company might use a board we haven't seen before.
PRIMARY_NAV_CAREER_TERMS = {
    "careers", "career", "jobs", "job openings", "open positions",
    "open roles", "join us", "join our team", "work with us",
    "we're hiring", "we are hiring", "hiring", "openings", "employment",
    "opportunities",
}

# Matches id/class names that indicate a layout chrome element (nav, header, footer)
# so we can strip div/section wrappers that aren't semantic <nav>/<footer> tags.
_LAYOUT_CHROME_RE = re.compile(
    r"\b(footer|navbar|nav-?bar|main-?nav|site-?nav|top-?nav|masthead|"
    r"site-?header|primary-?nav|global-?nav|page-?header|menu-?wrap|"
    r"nav-?menu|nav-?mobile|mobile-?nav|header-?wrap|menu-?bar)\b",
    re.IGNORECASE,
)

# Workers for parallel company processing
MAX_WORKERS = 16
# Career paths probed concurrently per company (keeps per-site load modest)
PROBE_BATCH_SIZE = 6
_PROBE_POOL = ThreadPoolExecutor(max_workers=MAX_WORKERS * PROBE_BATCH_SIZE)
_THREAD_LOCAL = local()
_PRINT_LOCK = Lock()


def strip_layout_chrome(soup):
    """
    Remove nav/header/footer elements (both semantic tags and div/section wrappers
    identified by class or id) from a BeautifulSoup tree in-place.
    """
    # Semantic tags first
    for tag in soup.find_all(["nav", "header", "footer"]):
        tag.decompose()
    # Div/section wrappers with nav/footer-like class or id
    for tag in soup.find_all(["div", "section", "aside"]):
        if tag.parent is None:
            continue  # already removed as a child of a decomposed parent
        tag_id = (tag.get("id") or "").lower()
        tag_classes = " ".join(tag.get("class") or []).lower()
        if _LAYOUT_CHROME_RE.search(tag_id + " " + tag_classes):
            tag.decompose()


def _session():
    """Per-thread requests.Session so connections are reused across requests."""
    session = getattr(_THREAD_LOCAL, "session", None)
    if session is None:
        session = _THREAD_LOCAL.session = requests.Session()
    return session


def make_request(url, method="get", **kwargs):
    """
    Make an HTTP request with error handling. Returns Response or None.
    A 429 (rate limited) response is retried after a short back-off, since
    some sites throttle the parallel careers-path probes.
    """
    kwargs.setdefault("timeout", REQUEST_TIMEOUT)
    kwargs.setdefault("headers", HEADERS)
    kwargs.setdefault("allow_redirects", True)
    for attempt in range(RATE_LIMIT_RETRIES + 1):
        try:
            resp = getattr(_session(), method)(url, **kwargs)
        except Exception:
            return None
        if resp.status_code == 200:
            return resp
        if resp.status_code != 429 or attempt == RATE_LIMIT_RETRIES:
            return None
        retry_after = resp.headers.get("Retry-After", "")
        delay = int(retry_after) if retry_after.isdigit() else 2 * (attempt + 1)
        time.sleep(min(delay, 10))


def get_soup(url):
    """Fetch a URL and return a BeautifulSoup object, or None on failure."""
    resp = make_request(url)
    if resp is None:
        return None
    try:
        return BeautifulSoup(resp.content, "lxml")
    except Exception:
        return None


def get_residents():
    """
    Fetch the MassRobotics resident page and return a list of
    {"name": str, "url": str} dicts.
    """
    print(f"Fetching resident list from {MASSROBOTICS_URL}...")
    soup = get_soup(MASSROBOTICS_URL)
    if soup is None:
        print("ERROR: Could not fetch MassRobotics resident page.", file=sys.stderr)
        sys.exit(1)

    residents = _residents_from_cards(soup)
    if not residents:
        print("WARNING: no resident cards found; falling back to link scan "
              "(no logos or descriptions).", file=sys.stderr)
        residents = _residents_from_links(soup)

    print(f"Found {len(residents)} residents.")
    return residents


def _residents_from_cards(soup):
    """
    Parse the WordPress resident cards (div.post-wrap.resident), each holding
    a logo, the linked company name, and a short description.
    """
    residents = []
    seen_urls = set()
    for card in soup.select("div.post-wrap.resident"):
        a = card.select_one(".content-wrap h1 a[href]")
        if a is None:
            continue  # no website listed, nothing to scrape
        href = a["href"].strip()
        parsed = urlparse(href)
        if not href.startswith("http") or parsed.netloc in seen_urls:
            continue
        if any(bl in parsed.netloc.lower() for bl in RESIDENT_DOMAIN_BLACKLIST):
            continue
        seen_urls.add(parsed.netloc)
        name = " ".join(a.get_text(" ", strip=True).split())

        img = card.select_one(".image-wrap img")
        logo = (img.get("src") or img.get("data-src")) if img else None

        # Description is everything in the content block except the name heading
        content = card.select_one(".content-wrap")
        content.find("h1").decompose()
        description = " ".join(content.get_text(" ", strip=True).split())

        residents.append({
            "name": name,
            "url": f"{parsed.scheme}://{parsed.netloc}",
            "logo": logo,
            "description": description,
        })
    return residents


def _residents_from_links(soup):
    """Fallback: treat every external link in the page body as a resident."""
    residents = []
    seen_urls = set()

    # Remove nav/header/footer so we only look at main content
    strip_layout_chrome(soup)

    # Look for links that are clearly company links (external, not massrobotics.org)
    for a in soup.find_all("a", href=True):
        href = a["href"].strip()
        if not href.startswith("http"):
            continue
        parsed = urlparse(href)
        netloc = parsed.netloc.lower().lstrip("www.")

        # Skip MassRobotics itself and known non-resident domains
        if any(bl in netloc for bl in RESIDENT_DOMAIN_BLACKLIST):
            continue
        if parsed.netloc in seen_urls:
            continue

        text = a.get_text(strip=True)
        if not text or len(text) > 80:
            continue

        # Skip obvious non-company links
        if any(kw in href.lower() for kw in ["linkedin", "twitter", "facebook",
                                               "instagram", "youtube", "mailto",
                                               "tel:", "javascript:"]):
            continue

        seen_urls.add(parsed.netloc)
        # Normalize URL to just scheme + netloc
        base_url = f"{parsed.scheme}://{parsed.netloc}"
        residents.append({"name": text, "url": base_url})
    return residents


def _probe_career_path(url, company_domain):
    """
    Fetch one candidate careers URL. Returns the careers URL it leads to,
    or None if it doesn't look like a careers page.
    """
    resp = make_request(url)
    if resp is None:
        return None
    final_url = resp.url
    final_domain = urlparse(final_url).netloc
    # Reject if redirected to a parked/expired domain
    if any(bd in final_domain for bd in CAREERS_DOMAIN_BLACKLIST):
        return None
    # Accept only if still on company domain or a known job board
    on_company = company_domain in final_domain or final_domain in company_domain
    on_job_board = any(jb in final_domain for jb in KNOWN_JOB_BOARDS)
    if not (on_company or on_job_board) or urlparse(final_url).path in ("", "/", "//"):
        return None
    # If the careers page directly links to a known job board
    # (e.g. dephy.com/careers → apply.workable.com/dephy/),
    # prefer the board URL so the HTML careers link is accurate.
    m = _BOARD_HREF_RE.search(resp.text)
    if m:
        return m.group(0).rstrip("/") + "/"
    return final_url


def find_careers_url(company_url):
    """
    Find the careers/jobs page for a company.
    Returns the careers URL string, or None if not found.
    """
    parsed = urlparse(company_url)
    base = f"{parsed.scheme}://{parsed.netloc}"

    company_domain = parsed.netloc

    # 1. Try common career subpaths, a batch at a time in parallel. Results
    # are checked in CAREER_PATHS order, so the earliest matching path wins.
    urls = [base + path for path in CAREER_PATHS]
    for i in range(0, len(urls), PROBE_BATCH_SIZE):
        futures = [_PROBE_POOL.submit(_probe_career_path, url, company_domain)
                   for url in urls[i:i + PROBE_BATCH_SIZE]]
        for future in futures:
            found = future.result()
            if found:
                time.sleep(REQUEST_DELAY)
                return found

    # 2. Scan homepage links for career keywords
    time.sleep(REQUEST_DELAY)
    soup = get_soup(company_url)
    if soup is None:
        return None

    for a in soup.find_all("a", href=True):
        href = a["href"].strip()
        link_text = a.get_text(strip=True).lower()
        href_lower = href.lower()

        if any(kw in link_text for kw in CAREER_LINK_KEYWORDS) or \
           any(kw in href_lower for kw in ["career", "jobs", "hiring", "openings",
                                            "opportunities", "positions"]):
            full_url = urljoin(company_url, href)
            if not full_url.startswith("http"):
                continue
            full_domain = urlparse(full_url).netloc

            on_company = (company_domain in full_domain or full_domain in company_domain)
            on_known_board = any(board in full_domain for board in KNOWN_JOB_BOARDS)
            is_blocked = (
                any(bd in full_domain for bd in CAREERS_DOMAIN_BLACKLIST) or
                any(bd in full_domain for bd in SOCIAL_AND_AGGREGATOR_DOMAINS)
            )
            # Follow to an unknown external board when the link text is an
            # unambiguous primary-nav career term (e.g. "Careers", "Jobs").
            # This is how we catch boards we haven't explicitly seen before.
            is_primary_nav = link_text.strip() in PRIMARY_NAV_CAREER_TERMS

            if not is_blocked and (on_company or on_known_board or is_primary_nav):
                time.sleep(REQUEST_DELAY)
                return full_url

    return None


# ---------------------------------------------------------------------------
# Job board-specific extractors
# ---------------------------------------------------------------------------

def extract_lever(slug):
    """Lever public API."""
    url = f"https://api.lever.co/v0/postings/{slug}?mode=json"
    resp = make_request(url)
    if resp is None:
        return []
    try:
        data = resp.json()
        jobs = []
        for item in data:
            cats = item.get("categories") or {}
            jobs.append({
                "title": item["text"],
                "url": item.get("hostedUrl"),
                "posted": parse_date(item.get("createdAt")),
                **location_fields(cats.get("allLocations") or [cats.get("location")],
                                  item.get("workplaceType")),
            })
        return jobs
    except Exception:
        return []


def extract_greenhouse(slug):
    """Greenhouse public API."""
    url = f"https://boards-api.greenhouse.io/v1/boards/{slug}/jobs"
    resp = make_request(url)
    if resp is None:
        return []
    try:
        data = resp.json()
        return [
            {
                "title": job["title"],
                "url": job.get("absolute_url"),
                "posted": parse_date(job.get("first_published")),
                **location_fields([(job.get("location") or {}).get("name")]),
            }
            for job in data.get("jobs", [])
        ]
    except Exception:
        return []


def ashby_board(slug):
    """
    Ashby public posting API. Returns {job_id: job dict}, or None on failure.
    Cached, since company sites often link many jobs on the same Ashby board.
    """
    with _BOARD_CACHE_LOCK:
        if ("ashby", slug) in _BOARD_CACHE:
            return _BOARD_CACHE[("ashby", slug)]
    board = None
    resp = make_request(f"https://api.ashbyhq.com/posting-api/job-board/{slug}")
    if resp is not None:
        try:
            board = {}
            for item in resp.json().get("jobs", []):
                if item.get("isListed") is False:
                    continue
                locs = [item.get("location")] + [
                    x.get("location") for x in item.get("secondaryLocations") or []]
                board[item["id"]] = {
                    "title": item["title"],
                    "url": item.get("jobUrl"),
                    "posted": parse_date(item.get("publishedAt")),
                    **location_fields(locs, item.get("workplaceType")),
                }
        except Exception:
            board = None
    with _BOARD_CACHE_LOCK:
        _BOARD_CACHE[("ashby", slug)] = board
    return board


def extract_ashby(slug, page_url):
    """Ashby: use the posting API, falling back to scraping the HTML listing."""
    board = ashby_board(slug)
    if board:
        return list(board.values())
    soup = get_soup(page_url)
    if soup is None:
        return []
    jobs = []
    for a in soup.find_all("a", href=True):
        href = a["href"]
        if f"/jobs/{slug}/" in href or "/jobs/" in href:
            title = a.get_text(strip=True)
            if title and is_job_title(title):
                jobs.append({"title": title, "url": urljoin(page_url, href)})
    return jobs


def extract_bamboohr(slug, page_url):
    """BambooHR job listing page."""
    soup = get_soup(page_url)
    if soup is None:
        return []
    jobs = []
    for a in soup.find_all("a", href=True):
        href = a["href"]
        if "/jobs/" in href or "bamboohr.com" in href:
            title = a.get_text(strip=True)
            if title and is_job_title(title):
                jobs.append({"title": title, "url": urljoin(page_url, href)})
    return jobs


def extract_workable(slug, page_url):
    """Workable job board: uses the v3 JSON API."""
    api_url = f"https://apply.workable.com/api/v3/accounts/{slug}/jobs"
    try:
        resp = make_request(
            api_url,
            method="post",
            json={},
            headers={**HEADERS, "Content-Type": "application/json"},
        )
        if resp is None:
            return []
        data = resp.json()
        jobs = []
        for item in data.get("results", []):
            title = item.get("title", "")
            shortcode = item.get("shortcode", "")
            if title and is_job_title(title):
                job_url = (f"https://apply.workable.com/{slug}/j/{shortcode}/"
                           if shortcode else None)
                locs = [", ".join(filter(None, [loc.get("city"), loc.get("region")]))
                        or loc.get("country")
                        for loc in item.get("locations") or [item.get("location") or {}]]
                workplace = "remote" if item.get("remote") else item.get("workplace")
                jobs.append({
                    "title": title,
                    "url": job_url,
                    "posted": parse_date(item.get("published")),
                    **location_fields(locs, workplace),
                })
        return jobs
    except Exception:
        return []


def extract_rippling(slug, page_url):
    """
    Rippling ATS: use the public board API (titles + locations), falling back
    to scraping the server-rendered jobs listing page.
    """
    resp = make_request(f"https://api.rippling.com/platform/api/ats/v1/board/{slug}/jobs")
    if resp is not None:
        try:
            jobs = [
                {
                    "title": item["name"].strip(),
                    "url": item.get("url"),
                    **location_fields([(item.get("workLocation") or {}).get("label")]),
                }
                for item in resp.json()
                if is_job_title(item["name"].strip())
            ]
            if jobs:
                return jobs
        except Exception:
            pass
    url = f"https://ats.rippling.com/{slug}/jobs"
    soup = get_soup(url)
    if soup is None:
        return []
    jobs = []
    seen = set()
    _CTA = {"view job", "apply", "apply now", "view", "see job"}
    for a in soup.find_all("a", href=True):
        href = a["href"]
        # Job links look like /{slug}/jobs/{uuid}
        if f"/{slug}/jobs/" not in href:
            continue
        title = a.get_text(strip=True)
        if not title or title.lower() in _CTA:
            continue
        if not is_job_title(title):
            continue
        full_url = urljoin(url, href)
        if title not in seen:
            seen.add(title)
            jobs.append({"title": title, "url": full_url})
    return jobs


# ---------------------------------------------------------------------------
# Posting date / location
# ---------------------------------------------------------------------------

_BOARD_CACHE = {}
_BOARD_CACHE_LOCK = Lock()

_COUNTRY_PREFIXES = {
    "us", "usa", "uk", "united states", "united kingdom", "canada", "germany",
    "france", "switzerland", "israel", "japan", "australia",
}
# Regions that, paired with "Remote", mean remote work rather than an office
_REMOTE_REGIONS = _COUNTRY_PREFIXES | {
    "global", "worldwide", "anywhere", "europe", "emea", "north america", "americas",
}
_WORKPLACE_WORDS_RE = re.compile(
    r"\(?\b(?:remote|on-?site|hybrid)\b\)?|\b(?:hub|office|hq)\b", re.IGNORECASE)


def parse_date(value):
    """Parse an epoch-ms number or ISO-8601 string to 'YYYY-MM-DD', or None."""
    if value in (None, ""):
        return None
    try:
        if isinstance(value, (int, float)):
            return datetime.fromtimestamp(value / 1000).strftime("%Y-%m-%d")
        m = re.match(r"\s*(\d{4}-\d{2}-\d{2})", str(value))
        return m.group(1) if m else None
    except (ValueError, OverflowError, OSError):
        return None


def _city(location):
    """
    'US, Boston, MA' / 'Boston, MA' / 'Onsite Berlin' / 'Boston Hub' /
    '529 Main St, Boston MA' -> city.
    """
    parts = [p.strip() for p in _WORKPLACE_WORDS_RE.sub(" ", location).split(",")]
    parts = [" ".join(p.split()) for p in parts if p.strip()]
    if len(parts) > 1 and parts[0].lower() in _COUNTRY_PREFIXES:
        parts = parts[1:]
    if len(parts) > 1 and parts[0][0].isdigit():
        parts = parts[1:]  # street address
    if not parts:
        return None
    return re.sub(r"(?<=[a-z]) (?-i:[A-Z]{2})$", "", parts[0]) or None


def _is_remote_region(location):
    """True for e.g. 'Remote', 'Canada - Remote', 'Remote, USA', 'Global (Remote)'."""
    if not re.search(r"\bremote\b", location, re.IGNORECASE):
        return False
    rest = re.sub(r"[\s,()/-]+", " ", _WORKPLACE_WORDS_RE.sub(" ", location)).strip().lower()
    return not rest or rest in _REMOTE_REGIONS


def location_fields(locations, workplace=None):
    """
    Summarise a job's raw location strings and workplace type (remote/hybrid/
    onsite, as boards report it) into {"location": label, "location_detail": str}.
    The label is a city, "Remote", "Hybrid" (hybrid, or remote allowed
    alongside an office), or "Multiple" (several offices); the detail lists
    every raw location for the hover tooltip.
    """
    raw = [" ".join(str(l).split()) for l in locations if l and str(l).strip()]
    raw = list(dict.fromkeys(raw))
    workplace = re.sub(r"[^a-z]", "", (workplace or "").lower())
    remote_listed = any(re.search(r"\bremote\b", l, re.IGNORECASE) for l in raw)
    # "Canada - Remote" / "Remote, USA" name a country, not a city
    places = [l for l in raw if not _is_remote_region(l)]
    cities = list(dict.fromkeys(c for c in (_city(l) for l in places) if c))

    if workplace == "remote" or (remote_listed and not cities):
        label = "Remote"
    elif len(cities) > 1:
        label = "Multiple"
    elif workplace == "hybrid" or remote_listed:
        label = "Hybrid"
    else:
        label = cities[0] if cities else None
    if not label:
        return {}
    detail = "; ".join(raw)
    if workplace in ("remote", "hybrid", "onsite") and workplace not in detail.lower():
        detail = f"{detail} ({workplace})" if detail else workplace
    return {"location": label, "location_detail": detail}


_UUID_RE = re.compile(r"[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}")
_RIPPLING_DATE_RE = re.compile(r'"createdOn":"(\d{4}-\d{2}-\d{2})')


def _job_page_details(url):
    """
    Read a job's own page for its posting date and location, from schema.org
    JobPosting data (JSON-LD or microdata) or, on Rippling, the embedded
    page data. Returns a dict with any of "posted", "location", "location_detail".
    """
    resp = make_request(url)
    if resp is None:
        return {}
    soup = BeautifulSoup(resp.content, "html.parser")
    found = {}

    for script in soup.find_all("script", type="application/ld+json"):
        try:
            data = json.loads(script.string or "")
        except Exception:
            continue
        items = data if isinstance(data, list) else data.get("@graph", [data])
        for item in items:
            if not isinstance(item, dict) or item.get("@type") != "JobPosting":
                continue
            found["posted"] = parse_date(item.get("datePosted"))
            places = item.get("jobLocation") or []
            places = places if isinstance(places, list) else [places]
            locs = []
            for place in places:
                addr = (place or {}).get("address") or {}
                if isinstance(addr, dict):
                    locs.append(", ".join(filter(None, [addr.get("addressLocality"),
                                                        addr.get("addressRegion")])))
            workplace = "remote" if item.get("jobLocationType") == "TELECOMMUTE" else None
            found.update(location_fields(locs, workplace))
            return found

    tag = soup.find(attrs={"itemprop": "datePosted"})
    if tag:
        found["posted"] = parse_date(tag.get("content") or tag.get_text(strip=True))
        city = soup.find(attrs={"itemprop": "addressLocality"})
        if city:
            found.update(location_fields([city.get("content") or city.get_text(strip=True)]))
        return found

    m = _RIPPLING_DATE_RE.search(resp.text)
    if m:
        found["posted"] = m.group(1)
    h1 = soup.find("h1")
    if h1 is not None:
        found.update(_card_locations(h1))
    return found


def enrich_jobs(jobs):
    """
    Fill in missing posting dates and locations. Jobs on an Ashby board are
    matched against its API; others have their own page read in parallel.
    """
    to_fetch = []
    for job in jobs:
        if job.get("posted") and job.get("location"):
            continue
        url = job.get("url") or ""
        m = re.search(r"jobs\.ashbyhq\.com/([^/?#]+)/(" + _UUID_RE.pattern + ")", url)
        if m:
            info = (ashby_board(m.group(1)) or {}).get(m.group(2))
            if info:
                for key in ("posted", "location", "location_detail"):
                    if not job.get(key):
                        job[key] = info.get(key)
                continue
        if url.startswith("http"):
            to_fetch.append(job)

    for job, details in zip(to_fetch, _PROBE_POOL.map(_job_page_details,
                                                     [j["url"] for j in to_fetch])):
        for key, value in details.items():
            if value and not job.get(key):
                job[key] = value
    return jobs


# Map-pin icons that sites put next to a job's location: Lucide's "map-pin"
# class, or the path data of the Lucide and Heroicons location pins.
_PIN_CLASS_RE = re.compile(r"map-?pin|location|marker", re.IGNORECASE)
_PIN_PATH_PREFIXES = ("M20 10c0 4.993", "M17.657 16.657")
_LOCATION_CLASS_RE = re.compile(r"\blocation\b|job-?location|posting-?location",
                                re.IGNORECASE)
# A job's details line, e.g. "Full-Time | On-Site | Boston, MA"
_META_CLASS_RE = re.compile(r"\bmeta\b|-meta\b|\bdetails?\b", re.IGNORECASE)
_META_SPLIT_RE = re.compile(r"\s*[|·•]\s*")
_PLACE_RE = re.compile(r"^[A-Z][\w.' -]+, ?[A-Z][\w. ]+(?: ?\(.*\))?$")
_WORKPLACE_RE = re.compile(r"^(remote|on-?site|hybrid)$", re.IGNORECASE)


def _card_locations(title_tag):
    """
    Find the location(s) shown on a job's card in a generic careers page:
    text next to a map-pin icon, in an element whose class names a location,
    or in a details line like "Full-Time | On-Site | Boston, MA" (classed as
    such, or the line right after the title).
    The card is the nearest ancestor of the title that holds no other job
    title of the same kind, so one job never picks up a neighbour's location.
    Returns location_fields() for what it finds.
    """
    card = title_tag
    for _ in range(4):
        parent = card.parent
        if parent is None or parent.name in ("body", "html"):
            break
        if len(parent.find_all(title_tag.name)) > 1:
            break
        card = parent

    locations = []
    for svg in card.find_all("svg"):
        cls = " ".join(svg.get("class") or [])
        path = svg.find("path")
        d = (path.get("d") or "") if path else ""
        if _PIN_CLASS_RE.search(cls) or d.startswith(_PIN_PATH_PREFIXES):
            locations.append(svg.parent.get_text(" ", strip=True))
    if not locations:
        for el in card.find_all(class_=_LOCATION_CLASS_RE):
            if not el.find(class_=_LOCATION_CLASS_RE):
                locations.append(el.get_text(" ", strip=True))

    workplace = None
    if not locations:
        # Details lines: elements classed as such, or the line right after
        # the title when it is separator-delimited
        meta = [el for el in card.find_all(class_=_META_CLASS_RE)
                if not el.find(class_=_META_CLASS_RE)]
        nxt = title_tag.find_next_sibling()
        if nxt is not None and _META_SPLIT_RE.search(nxt.get_text(" ", strip=True)):
            meta.append(nxt)
        for el in meta:
            for part in _META_SPLIT_RE.split(el.get_text(" ", strip=True)):
                if _PLACE_RE.match(part):
                    locations.append(part)
                elif _WORKPLACE_RE.match(part):
                    workplace = part
    return location_fields([l for l in locations if l and len(l) <= 60], workplace)


# ---------------------------------------------------------------------------
# Generic HTML scraper
# ---------------------------------------------------------------------------

def is_job_title(text):
    """
    Heuristic: does this text look like a job title?
    Returns True if it likely is.
    """
    text = text.strip()
    if not text or len(text) < 3 or len(text) > 100:
        return False

    lower = text.lower()

    # Reject copyright / footer text
    if "©" in text or "all rights reserved" in lower or lower.startswith("copyright"):
        return False

    # Reject boilerplate
    for phrase in BOILERPLATE_PHRASES:
        if phrase in lower:
            return False

    # Reject single nav words
    if lower in NAV_WORDS:
        return False

    # Reject if looks like a sentence (too many words or ends with punctuation like '.')
    words = text.split()
    if len(words) > 10:
        return False
    if text.endswith(".") and len(words) > 4:
        return False

    # Reject product / document nouns as suffixes (e.g. "Developer Kit", "Software Downloads")
    _PRODUCT_SUFFIX_RE = re.compile(
        r"\b(kit|download|downloads|bundle|bundles|hub|documentation|"
        r"overview|tutorial|guide|sdk|api|catalog|library|release|update)\s*$",
        re.IGNORECASE,
    )
    if _PRODUCT_SUFFIX_RE.search(lower):
        return False

    # Reject navigational / CTA / description prefixes
    _NAV_PREFIX_RE = re.compile(
        r"^(visit|explore|discover|download|read|view|see|learn|get|"
        r"request|book|why join|we are|we're|join the|"
        r"transform\w*|build\w*|advance\w*|empower\w*|revolutioniz\w*|"
        r"official|introducing|announcing|"
        # Article/possessive openers — signals a description sentence, not a title
        r"a\s|an\s|our\s|the\s"
        r")\b"
        # Imperative sentence fragments from job descriptions (not titles)
        r"|^(own|take|drive|help|shape|deliver|define|"
        r"lead\sthe|ensure|manage|develop|create|design)\s",
        re.IGNORECASE,
    )
    if _NAV_PREFIX_RE.match(lower):
        return False

    # Reject "Label: detail" fragments like "Senior: 6+ years required" or "Location: Boston"
    if re.match(r"^[A-Za-z]{2,20}:\s", text):
        return False

    # Questions are never job titles
    if text.endswith("?"):
        return False

    # Must contain a job keyword (word-boundary matched to avoid "intern" in "International")
    if JOB_KEYWORD_RE.search(text):
        if len(words) >= 2:
            return True
        # Single-word: only accept unambiguous standalone role names
        SINGLE_WORD_ROLES = {
            "intern", "cto", "ceo", "coo", "cfo", "ciso", "cpo",
            "recruiter", "accountant", "technician",
        }
        return lower in SINGLE_WORD_ROLES

    return False


def find_career_sections(soup):
    """
    Return a list of Tag objects that are likely career/job listing sections.
    """
    career_section_keywords = [
        "career", "careers", "job", "jobs", "position", "positions",
        "opening", "openings", "opportunity", "opportunities", "hiring",
        "join us", "join our team", "we're hiring",
    ]
    sections = []

    # Look for elements whose id or class suggests a career section
    for tag in soup.find_all(True):
        tag_id = (tag.get("id") or "").lower()
        tag_class = " ".join(tag.get("class") or []).lower()
        combined = tag_id + " " + tag_class
        if any(kw in combined for kw in ["job", "career", "position", "opening",
                                          "hiring", "role"]):
            sections.append(tag)

    if sections:
        return sections

    # Fallback: find headings that mention careers, return their parent
    for tag in soup.find_all(["h1", "h2", "h3", "h4"]):
        text = tag.get_text(strip=True).lower()
        if any(kw in text for kw in career_section_keywords):
            parent = tag.find_parent(["section", "div", "article", "main"]) or tag.parent
            if parent:
                sections.append(parent)

    return sections


def extract_next_data_jobs(soup, page_url):
    """
    Extract jobs from a Next.js __NEXT_DATA__ JSON blob, if present.
    Returns a list of jobs, or None if no __NEXT_DATA__ found or no jobs extracted.
    """
    script = soup.find("script", id="__NEXT_DATA__")
    if not script or not script.string:
        return None
    try:
        data = json.loads(script.string)
    except Exception:
        return None

    found = []

    def search(obj, depth=0):
        if depth > 12:
            return
        if isinstance(obj, list) and obj:
            # Check if this array looks like a job listing (majority have job titles)
            candidates = []
            for item in obj:
                if isinstance(item, dict):
                    title = (item.get("title") or item.get("name") or
                             item.get("job_title") or item.get("jobTitle") or "")
                    if title and is_job_title(str(title)):
                        candidates.append(item)
            if candidates and len(candidates) >= max(1, len(obj) * 0.4):
                for item in candidates:
                    title = (item.get("title") or item.get("name") or
                             item.get("job_title") or item.get("jobTitle", ""))
                    link = (item.get("url") or item.get("link") or
                            item.get("apply_url") or item.get("absolute_url") or
                            item.get("hostedUrl") or "")
                    if title:
                        full_url = urljoin(page_url, link) if link else None
                        found.append({"title": str(title), "url": full_url})
                return  # don't recurse into this array's items
            for item in obj:
                search(item, depth + 1)
        elif isinstance(obj, dict):
            for v in obj.values():
                search(v, depth + 1)

    search(data)
    return found if found else None


def extract_jobs_from_html(url, soup=None):
    """
    Generic HTML scraper. Returns list of {"title": str, "url": str|None}.
    If `soup` is provided, skips fetching (used by Playwright fallback).
    """
    if soup is None:
        soup = get_soup(url)
    if soup is None:
        return []

    # Strip nav/header/footer (semantic tags + div/section wrappers) so their
    # links don't get mistaken for job listings
    strip_layout_chrome(soup)

    jobs = []
    seen_titles = set()

    # Patterns that signal the start of location/metadata appended to a job title.
    # Optional leading \(? so we catch "Engineer (Remote)" as well as "Engineer Remote".
    # Note: "Hybrid" excluded — it appears in technical specializations like "Hybrid Propulsion".
    _META_RE = re.compile(
        r"\s*\(?(?:\bUS\b|\bUK\b|\bEU\b|On-?site|Full.?time|Part.?time"
        r"|(?-i:[A-Z]{2}),\s[A-Za-z]|\bRemote\b)",
        re.IGNORECASE,
    )

    def clean_title(text):
        """Strip location/job-type metadata that some sites append to the title."""
        m = _META_RE.search(text)
        if m and m.start() > 5:
            text = text[:m.start()]
        return text.strip(" ,;-")

    def add_job(title, href=None, tag=None):
        title = clean_title(title.strip())
        if title and title.lower() not in seen_titles and is_job_title(title):
            seen_titles.add(title.lower())
            full_url = urljoin(url, href) if href else None
            job = {"title": title, "url": full_url}
            if tag is not None:
                job.update(_card_locations(tag))
            jobs.append(job)

    # Step 1: Link-based extraction within career sections
    sections = find_career_sections(soup)
    have_career_sections = bool(sections)
    search_scope = sections if sections else [soup]

    for scope in search_scope:
        for a in scope.find_all("a", href=True):
            href = a["href"]
            # Skip obvious non-job links
            if any(kw in href.lower() for kw in ["linkedin", "twitter", "facebook",
                                                   "instagram", "youtube", "mailto:",
                                                   "tel:", "#"]):
                continue
            # If the <a> wraps a card containing a heading + description (e.g. Odoo),
            # use the heading text only rather than concatenating all descendant text.
            heading = a.find(["h2", "h3", "h4"])
            if heading:
                title = heading.get_text(strip=True)
            else:
                # Prefer a span/div explicitly marked as the job title
                # (e.g. Humanoid/Ashby uses <span class="role-link-title">)
                title_el = a.find(class_=re.compile(
                    r"\b(?:title|role-?link|job-?name|position-?name|role-?title|"
                    r"job-?title|listing-?title|opening-?title|vacancy-?title)\b",
                    re.IGNORECASE,
                ))
                title = title_el.get_text(strip=True) if title_el else a.get_text(strip=True)
            add_job(title, href, tag=a)

    _CTA_TEXTS = {
        "learn more", "apply", "apply now", "view job", "view role",
        "apply here", "see role", "read more", "view opening", "open position",
        "see details", "view details", "details", "apply online", "find out more",
        "see opening", "view listing", "job details",
    }

    def first_valid_href(tag):
        """Return the first non-social href from a tag's descendant links, or None."""
        for a in tag.find_all("a", href=True):
            h = a["href"]
            if not any(bad in h.lower() for bad in
                       ["linkedin", "twitter", "facebook", "mailto:", "tel:"]):
                return h
        return None

    def find_job_url_near(tag, max_levels=4):
        """
        Find a URL for a job title tag.
        Checks inside the tag first, then walks up up to max_levels ancestor levels
        looking for a CTA link (e.g. 'Learn More', 'See Details') in each ancestor's
        subtree. This handles layouts where the title and apply link are siblings
        within a common wrapper div.
        """
        href = first_valid_href(tag)
        if href:
            return href
        node = tag
        for _ in range(max_levels):
            node = node.parent
            if node is None:
                break
            for a in node.find_all("a", href=True):
                h = a["href"]
                if any(bad in h.lower() for bad in ["mailto:", "tel:", "javascript:"]):
                    continue
                if a.get_text(strip=True).lower() in _CTA_TEXTS:
                    return h
        return None

    # Step 2: Plain-text extraction within career sections.
    # Also looks for sibling CTA links (e.g. "Learn More", "See Details") to
    # capture the job URL via find_job_url_near().
    if len(jobs) < 2:
        for scope in search_scope:
            for tag in scope.find_all(["h2", "h3", "h4", "li", "dt", "p"]):
                # Skip if this element contains nested block tags (complex structure)
                if tag.find(["ul", "ol", "div", "section"]):
                    continue
                title = tag.get_text(strip=True)
                href = find_job_url_near(tag)
                # <p> tags are often description text; require a strong keyword
                # when there's no accompanying link to anchor the result.
                if tag.name == "p" and not href and not STRONG_KEYWORD_RE.search(title):
                    continue
                add_job(title, href=href, tag=tag)

        # Step 2b: Some sites put job titles in <div> or <span> leaf nodes rather
        # than headings (e.g. Webflow-generated class names like "text-block-8").
        # Only scan within identified career sections to limit noise.
        if len(jobs) < 2 and have_career_sections:
            for scope in search_scope:
                for tag in scope.find_all(["div", "span"]):
                    # Leaf nodes only — no nested block elements
                    if tag.find(["div", "p", "h1", "h2", "h3", "h4",
                                 "ul", "ol", "li", "section", "article"]):
                        continue
                    title = tag.get_text(strip=True)
                    href = find_job_url_near(tag)
                    add_job(title, href=href, tag=tag)

    # Step 3: Whole-page fallback — only if actual career sections were identified.
    # Without identified sections, a full-page scan produces too many false positives.
    if len(jobs) < 2 and have_career_sections:
        for tag in soup.find_all(["li", "h2", "h3"]):
            title = tag.get_text(strip=True)
            add_job(title, href=find_job_url_near(tag), tag=tag)

    # Sanity check: if every result lacks a URL, we've likely scraped a
    # marketing/culture page rather than an actual job listing. Apply stricter
    # keyword filtering (require a strongly role-specific word).
    if jobs and all(not j.get("url") for j in jobs):
        jobs = [j for j in jobs if STRONG_KEYWORD_RE.search(j["title"])]

    # Supplement with Next.js __NEXT_DATA__ jobs (handles React/Next.js sites
    # that server-embed job data in a JSON script tag).
    next_jobs = extract_next_data_jobs(soup, url)
    if next_jobs:
        existing_titles = {j["title"].lower() for j in jobs}
        for j in next_jobs:
            if j["title"].lower() not in existing_titles:
                jobs.append(j)
                existing_titles.add(j["title"].lower())

    return jobs


# ---------------------------------------------------------------------------
# Embedded job board detection
# ---------------------------------------------------------------------------

# Patterns to detect job board slugs embedded in page source or iframes
_EMBED_PATTERNS = [
    # Lever: api.lever.co/v0/postings/{slug} or jobs.lever.co/{slug}
    (re.compile(r"(?:api\.lever\.co/v0/postings|jobs\.lever\.co)/([A-Za-z0-9_-]+)",
                re.IGNORECASE), "lever"),
    # Greenhouse: boards.greenhouse.io/{slug} or boards-api.greenhouse.io/v1/boards/{slug}
    (re.compile(r"boards(?:-api)?\.greenhouse\.io/(?:v1/boards/)?([A-Za-z0-9_-]+)",
                re.IGNORECASE), "greenhouse"),
    # Ashby: jobs.ashbyhq.com/{slug}
    (re.compile(r"jobs\.ashbyhq\.com/([A-Za-z0-9_-]+)",
                re.IGNORECASE), "ashby"),
    # BambooHR: {slug}.bamboohr.com
    (re.compile(r"([A-Za-z0-9_-]+)\.bamboohr\.com",
                re.IGNORECASE), "bamboohr"),
    # Workable: apply.workable.com/{slug}
    (re.compile(r"apply\.workable\.com/([A-Za-z0-9_-]+)",
                re.IGNORECASE), "workable"),
    # Rippling ATS: ats.rippling.com/{slug}/jobs
    (re.compile(r"ats\.rippling\.com/([A-Za-z0-9_-]+)/jobs",
                re.IGNORECASE), "rippling"),
]


def detect_embedded_job_board(careers_url):
    """
    Fetch the careers page and scan its source for embedded job board references.
    Returns job list if a known board is detected, or None if not found.
    """
    resp = make_request(careers_url)
    if resp is None:
        return None

    source = resp.text
    for pattern, board in _EMBED_PATTERNS:
        m = pattern.search(source)
        if not m:
            continue
        slug = m.group(1).lower()
        # Sanity: slug should look reasonable (not a long URL fragment)
        if len(slug) > 60 or "/" in slug:
            continue
        if board == "lever":
            return extract_lever(slug)
        if board == "greenhouse":
            return extract_greenhouse(slug)
        if board == "ashby":
            return extract_ashby(slug, f"https://jobs.ashbyhq.com/{slug}")
        if board == "bamboohr":
            return extract_bamboohr(slug, f"https://{slug}.bamboohr.com/jobs/")
        if board == "workable":
            return extract_workable(slug, f"https://apply.workable.com/{slug}/")
        if board == "rippling":
            return extract_rippling(slug, f"https://ats.rippling.com/{slug}/jobs")

    # Odoo HR module: company.odoo.com/jobs (possibly with locale prefix)
    m = re.search(
        r"https?://([A-Za-z0-9_-]+)\.odoo\.com(?:/[a-z]{2}(?:_[A-Z]{2})?)?/jobs",
        source, re.IGNORECASE,
    )
    if m:
        odoo_url = m.group(0)
        return extract_jobs_from_html(odoo_url)

    return None


# ---------------------------------------------------------------------------
# Playwright fallback for JS-rendered / Cloudflare-protected pages
# ---------------------------------------------------------------------------

def render_with_playwright(url):
    """Fetch a page using a real browser (Playwright). Returns HTML or None."""
    if not PLAYWRIGHT_AVAILABLE:
        return None
    try:
        with sync_playwright() as p:
            browser = p.chromium.launch(headless=True)
            ctx = browser.new_context(
                user_agent=(
                    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                    "AppleWebKit/537.36 (KHTML, like Gecko) "
                    "Chrome/124.0.0.0 Safari/537.36"
                ),
                viewport={"width": 1280, "height": 800},
            )
            page = ctx.new_page()
            page.goto(url, wait_until="networkidle", timeout=30_000)
            html = page.content()
            browser.close()
        return html
    except Exception:
        return None


def extract_jobs_with_playwright(url):
    """
    Extract jobs from the fully-rendered HTML of a page. Used as a fallback
    when requests-based scraping returns nothing — covers Cloudflare-protected
    boards, Next.js/React SPAs, and any other board we haven't seen before.
    """
    html = render_with_playwright(url)
    if html is None:
        return []
    return extract_jobs_from_html(url, soup=BeautifulSoup(html, "lxml"))


def extract_gusto(url):
    """
    Gusto job board (Cloudflare-protected, so rendered with Playwright).
    Each posting is a card link: an <h3> title, then a <p> with the location.
    """
    html = render_with_playwright(url)
    if html is None:
        return []
    jobs = []
    for a in BeautifulSoup(html, "lxml").select('a[href*="/postings/"]'):
        title = a.find("h3")
        if title is None:
            continue
        loc = a.find("p")
        jobs.append({
            "title": title.get_text(" ", strip=True),
            "url": urljoin(url, a["href"]),
            **location_fields([loc.get_text(" ", strip=True) if loc else None]),
        })
    return jobs


# ---------------------------------------------------------------------------
# Main extractor dispatcher
# ---------------------------------------------------------------------------

def extract_jobs(careers_url):
    """
    Dispatch to the right extractor based on the careers URL.
    Returns list of {"title": str, "url": str|None}.
    """
    if not careers_url:
        return []

    lower = careers_url.lower()

    # Lever
    m = re.search(r"jobs\.lever\.co/([^/?#]+)", lower)
    if m:
        return extract_lever(m.group(1))

    # Greenhouse
    m = re.search(r"boards\.greenhouse\.io/([^/?#]+)", lower)
    if m:
        return extract_greenhouse(m.group(1))

    # Ashby
    m = re.search(r"jobs\.ashbyhq\.com/([^/?#]+)", lower)
    if m:
        return extract_ashby(m.group(1), careers_url)

    # BambooHR
    m = re.search(r"([^.]+)\.bamboohr\.com", lower)
    if m:
        return extract_bamboohr(m.group(1), careers_url)

    # Workable
    m = re.search(r"apply\.workable\.com/([^/?#]+)", lower)
    if m:
        return extract_workable(m.group(1), careers_url)

    # Rippling ATS
    m = re.search(r"ats\.rippling\.com/([^/?#]+)", lower)
    if m:
        return extract_rippling(m.group(1), careers_url)

    # Gusto
    if "jobs.gusto.com/boards/" in lower:
        return extract_gusto(careers_url)

    # For company-hosted careers pages, scan the page source for embedded job
    # board API/widget references (e.g. Lever embed on a company's own domain).
    embedded = detect_embedded_job_board(careers_url)
    if embedded:
        return embedded

    # Generic HTML scrape for everything else
    jobs = extract_jobs_from_html(careers_url)

    # Sanity check: if we got ≥3 results but NONE have a strong job keyword
    # (e.g. "engineer", "manager"), we've probably scraped a product/marketing page.
    if len(jobs) >= 3:
        strong = sum(1 for j in jobs if STRONG_KEYWORD_RE.search(j["title"]))
        if strong == 0:
            jobs = []

    # If HTML scraping returned nothing, try a real browser. This covers
    # Cloudflare-protected boards (e.g. Gusto), JS-rendered React/Next.js
    # pages, and any board we haven't explicitly coded for.
    if not jobs:
        jobs = extract_jobs_with_playwright(careers_url)

    return jobs


# ---------------------------------------------------------------------------
# HTML generation
# ---------------------------------------------------------------------------

CSS = """
* { box-sizing: border-box; margin: 0; padding: 0; }
body {
    font-family: "Avenir", "Avenir Next", -apple-system, BlinkMacSystemFont,
                 "Segoe UI", Roboto, sans-serif;
    background: #f4f4f4;
    color: #202731;
    line-height: 1.6;
}
header {
    background: #fff;
    border-bottom: 3px solid #D90B1C;
    padding: 16px 32px;
    display: flex;
    align-items: center;
    gap: 24px;
}
header img { height: 44px; }
header .header-text h1 { font-size: 1.2rem; font-weight: 700; color: #202731; }
header .header-text p  { font-size: 0.8rem; color: #666; margin-top: 2px; }
main { max-width: 960px; margin: 32px auto; padding: 0 16px; }
.summary {
    background: #fff;
    border-radius: 6px;
    padding: 14px 20px;
    margin-bottom: 24px;
    border-left: 4px solid #D90B1C;
    font-size: 1rem;
    color: #202731;
}
.summary strong { color: #D90B1C; }
.summary .disclaimer { font-size: 0.8rem; color: #666; margin-top: 6px; }
.summary .intro { font-size: 0.95rem; margin-top: 12px; }
.company {
    background: #fff;
    border: 1px solid #ddd;
    border-radius: 6px;
    margin-bottom: 14px;
    padding: 14px 18px;
}
.company-header {
    display: flex;
    align-items: center;
    gap: 12px;
    margin-bottom: 8px;
}
.company-name { font-size: 2rem; line-height: 1.2; font-weight: 700; margin-left: auto; text-align: right; }
.company-name a { color: #D90B1C; text-decoration: none; }
.company-logo-link { display: inline-flex; }
.company-logo { height: 56px; max-width: 240px; object-fit: contain; }
.company-desc { font-size: 0.85rem; color: #555; margin-bottom: 10px; }
.company-name a:hover { text-decoration: underline; }
.job-count { font-size: 1rem; color: #888; white-space: nowrap; }
ul.jobs { list-style: none; padding-left: 8px; }
ul.jobs li {
    display: grid;
    grid-template-columns: 1fr 6.5em 8em;
    gap: 12px;
    align-items: baseline;
    padding: 4px 0;
    border-bottom: 1px solid #f0f0f0;
    font-size: 0.9rem;
}
ul.jobs li .job-date, ul.jobs li .job-location {
    text-align: right;
    font-size: 0.8rem;
    color: #888;
    white-space: nowrap;
    overflow: hidden;
    text-overflow: ellipsis;
}
@media (max-width: 560px) {
    .company-name { font-size: 1.4rem; }
    .company-logo { height: 40px; max-width: 160px; }
    ul.jobs li { grid-template-columns: 1fr 8em; gap: 0 12px; }
    ul.jobs li .job-title { grid-column: 1 / -1; }
}
ul.jobs li:last-child { border-bottom: none; }
.sort-btn {
    all: unset;
    cursor: pointer;
    text-align: right;
}
.sort-btn:hover, .sort-btn[data-dir] { color: #D90B1C; }
.sort-btn:focus-visible { outline: 2px solid #D90B1C; outline-offset: 2px; }
.sort-btn[data-dir="asc"]::after { content: " ▲"; }
.sort-btn[data-dir="desc"]::after { content: " ▼"; }
ul.jobs li.jobs-head {
    font-size: 0.7rem;
    font-weight: 700;
    color: #888;
    text-transform: uppercase;
    letter-spacing: 0.05em;
    text-align: right;
}
ul.jobs li a { color: #D90B1C; text-decoration: none; }
ul.jobs li a:hover { text-decoration: underline; }
ul.jobs li .no-link { color: #333; }
"""


LOGO_URL = ("https://www.massrobotics.org/wp-content/uploads/2022/07/"
            "massrobotics-logo.jpg")


SORT_SCRIPT = """<script>
// Clicking "Posted" or "Location" sorts every company's job list by that
// column; clicking it again reverses the order. Jobs missing the value
// always go last. Posted starts newest-first, Location A-Z.
document.addEventListener("click", function (e) {
  var btn = e.target.closest(".sort-btn");
  if (!btn) return;
  var key = btn.dataset.key;
  var dir = btn.dataset.dir === "desc" ? "asc"
          : btn.dataset.dir === "asc" ? "desc"
          : key === "posted" ? "desc" : "asc";
  document.querySelectorAll(".sort-btn").forEach(function (b) {
    if (b.dataset.key === key) b.dataset.dir = dir;
    else delete b.dataset.dir;
  });
  function value(li) {
    return key === "posted" ? (li.dataset.posted || "")
         : li.querySelector(".job-location").textContent.trim();
  }
  document.querySelectorAll("ul.jobs").forEach(function (ul) {
    var rows = Array.from(ul.querySelectorAll("li:not(.jobs-head)"));
    rows.sort(function (a, b) {
      var x = value(a), y = value(b);
      if (!x || !y) return (x ? 0 : 1) - (y ? 0 : 1);
      var c = x.localeCompare(y);
      return dir === "asc" ? c : -c;
    });
    rows.forEach(function (li) { ul.appendChild(li); });
  });
});
</script>"""


def generate_html(results, output_paths=OUTPUT_FILES):
    """
    Generate the output files (jobs.html and index.html).
    results: list of {name, site, careers_url, jobs}
    """
    with_jobs = [r for r in results if r["jobs"]]

    total_jobs = sum(len(r["jobs"]) for r in with_jobs)
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    lines = [
        "<!DOCTYPE html>",
        '<html lang="en">',
        "<head>",
        '<meta charset="UTF-8">',
        '<meta name="viewport" content="width=device-width, initial-scale=1.0">',
        "<title>MassRobotics Resident Jobs</title>",
        f"<style>{CSS}</style>",
        "</head>",
        "<body>",
        "<header>",
        f'  <img src="{LOGO_URL}" alt="MassRobotics">',
        '  <div class="header-text">',
        "    <h1>Resident Jobs</h1>",
        f"    <p>Last updated: {timestamp}</p>",
        "  </div>",
        "</header>",
        "<main>",
        '<div class="summary">',
        f"  <strong>{total_jobs}</strong> open roles found",
        '  <p class="disclaimer">We never charge for listing jobs. MassRobotics is '
        "not a job board or recruiter. These listings are all scraped from public "
        "data; we offer no guarantee on the accuracy of the data.</p>",
        '  <p class="intro">MassRobotics resident startups are dynamic companies '
        "dedicated to advancing robotics and supporting technologies. They aim to "
        "transform how we live, work, and play through innovative solutions. "
        "Joining MassRobotics means becoming part of a global community of experts "
        "and like-minded entrepreneurs. These startups cover a range of stages, "
        "from concept to manufacturing, and focus on robotics, Physical AI, and "
        "connected devices.</p>",
        '  <p class="intro">See below for opportunities across the globe.</p>',
        "</div>",
    ]

    for r in sorted(with_jobs, key=lambda x: x["name"].lower()):
        lines.append('<div class="company">')
        lines.append('  <div class="company-header">')
        link = r.get("careers_url") or r["site"]
        if r.get("logo"):
            lines.append(
                f'    <a class="company-logo-link" href="{link}" target="_blank">'
                f'<img class="company-logo" src="{_esc(r["logo"])}" '
                f'alt="{_esc(r["name"])}" loading="lazy"></a>'
            )
        lines.append(
            f'    <span class="company-name"><a href="{link}" target="_blank">'
            f'{_esc(r["name"])} career page</a></span>'
        )
        lines.append(
            f'    <span class="job-count">{len(r["jobs"])} role'
            f'{"s" if len(r["jobs"]) != 1 else ""}</span>'
        )
        lines.append("  </div>")
        if r.get("description"):
            lines.append(f'  <p class="company-desc">{_esc(r["description"])}</p>')
        lines.append('  <ul class="jobs">')
        lines.append('    <li class="jobs-head"><span class="job-title"></span><button class="sort-btn" data-key="posted">Posted</button><button class="sort-btn" data-key="location">Location</button></li>')
        for job in r["jobs"]:
            posted = _fmt_date(job.get("posted"))
            location = job.get("location") or ""
            detail = job.get("location_detail") or location
            meta = (
                f'<span class="job-date">{posted}</span>'
                f'<span class="job-location" title="{_esc(detail)}">'
                f'{_esc(location)}</span>'
            )
            if job.get("url"):
                title = (f'<a class="job-title" href="{job["url"]}" target="_blank">'
                         f'{_esc(job["title"])}</a>')
            else:
                title = f'<span class="job-title no-link">{_esc(job["title"])}</span>'
            lines.append(f'    <li data-posted="{job.get("posted") or ""}">{title}{meta}</li>')
        lines.append("  </ul>")
        lines.append("</div>")

    lines += ["</main>", SORT_SCRIPT, "</body>", "</html>"]

    html = "\n".join(lines)
    for output_path in output_paths:
        with open(output_path, "w", encoding="utf-8") as f:
            f.write(html)
        print(f"Written to {output_path}")


def _fmt_date(iso_date):
    """'2026-10-05' -> 'Oct 5, 2026'; '' if missing or unparseable."""
    try:
        d = datetime.strptime(iso_date, "%Y-%m-%d")
    except (TypeError, ValueError):
        return ""
    return f"{d:%b} {d.day}, {d.year}"


def _esc(text):
    """HTML-escape a string."""
    return (
        str(text)
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
    )


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def process_resident(resident, index, total):
    """
    Process one resident company: find its careers page and extract jobs.
    Returns a result dict. Called from worker threads.
    """
    name = resident["name"]
    site = resident["url"]

    with _PRINT_LOCK:
        print(f"[{index}/{total}] {name} ({site})")

    careers_url = find_careers_url(site)
    if careers_url:
        with _PRINT_LOCK:
            print(f"  -> careers: {careers_url}")
        time.sleep(REQUEST_DELAY)
        jobs = enrich_jobs(extract_jobs(careers_url))
        with _PRINT_LOCK:
            if jobs:
                print(f"  -> {len(jobs)} job(s) found")
            else:
                print(f"  -> 0 jobs extracted  [CHECK MANUALLY: {careers_url}]")
    else:
        with _PRINT_LOCK:
            print("  -> no careers page found")
        jobs = []

    return {
        "name": name,
        "site": site,
        "logo": resident.get("logo"),
        "description": resident.get("description"),
        "careers_url": careers_url,
        "jobs": jobs,
    }


def parse_args():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--limit", type=int, metavar="N",
        help="only process the first N residents (for quick test runs)",
    )
    parser.add_argument(
        "--only", action="append", metavar="NAME",
        help="only process residents whose name contains NAME "
             "(case-insensitive; repeatable)",
    )
    parser.add_argument(
        "--no-playwright", action="store_true",
        help="skip the slow headless-browser fallback",
    )
    parser.add_argument(
        "--output", action="append", metavar="FILE",
        help="file(s) to write (repeatable). Defaults to jobs.html and "
             "index.html, or test.html when --limit/--only is used so a "
             "partial run never overwrites the real page.",
    )
    return parser.parse_args()


def main():
    global PLAYWRIGHT_AVAILABLE
    args = parse_args()
    if args.no_playwright:
        PLAYWRIGHT_AVAILABLE = False

    residents = get_residents()
    if args.only:
        needles = [n.lower() for n in args.only]
        residents = [r for r in residents
                     if any(n in r["name"].lower() for n in needles)]
    if args.limit is not None:
        residents = residents[:args.limit]
    partial = bool(args.only or args.limit is not None)
    output_paths = args.output or (["test.html"] if partial else OUTPUT_FILES)
    if partial:
        print(f"Partial run: processing {len(residents)} resident(s).")

    total = len(residents)
    results = [None] * total

    # Process companies in parallel — each company is a different domain,
    # so we won't hammer the same server. Per-domain delays are still respected
    # inside each worker via REQUEST_DELAY sleeps.
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        future_to_idx = {
            executor.submit(process_resident, resident, i + 1, total): i
            for i, resident in enumerate(residents)
        }
        for future in as_completed(future_to_idx):
            idx = future_to_idx[future]
            try:
                results[idx] = future.result()
            except Exception as exc:
                name = residents[idx]["name"]
                with _PRINT_LOCK:
                    print(f"  ERROR processing {name}: {exc}", file=sys.stderr)
                results[idx] = {
                    "name": name,
                    "site": residents[idx]["url"],
                    "logo": residents[idx].get("logo"),
                    "description": residents[idx].get("description"),
                    "careers_url": None,
                    "jobs": [],
                }

    total_jobs = sum(len(r["jobs"]) for r in results)
    with_jobs = sum(1 for r in results if r["jobs"])
    print(
        f"\nDone: {total_jobs} jobs across {with_jobs}/{len(results)} companies."
    )

    # Post-run manual check list: careers page found but 0 jobs extracted.
    # These may use a JS-rendered board or an unsupported platform.
    needs_check = [r for r in results if r["careers_url"] and not r["jobs"]]
    if needs_check:
        print(f"\n--- {len(needs_check)} companies need manual review (careers page found, 0 jobs extracted) ---")
        for r in sorted(needs_check, key=lambda x: x["name"]):
            print(f"  {r['name']}: {r['careers_url']}")

    generate_html(results, output_paths)


if __name__ == "__main__":
    main()
