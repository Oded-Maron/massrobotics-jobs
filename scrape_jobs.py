#!/usr/bin/env python3
"""
MassRobotics Job Listing Scraper
Scrapes job listings from MassRobotics resident startup websites and generates jobs.html.
"""

import json
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
from threading import Lock
from urllib.parse import urljoin, urlparse

import requests
from bs4 import BeautifulSoup

try:
    from playwright.sync_api import sync_playwright
    PLAYWRIGHT_AVAILABLE = True
except ImportError:
    PLAYWRIGHT_AVAILABLE = False

MASSROBOTICS_URL = "https://www.massrobotics.org/startups/massrobotics-resident-startups/"
OUTPUT_FILE = "jobs.html"
REQUEST_TIMEOUT = 10
REQUEST_DELAY = 0.5  # seconds between requests

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
MAX_WORKERS = 8
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


def make_request(url, method="get", **kwargs):
    """Make an HTTP request with error handling. Returns Response or None."""
    try:
        kwargs.setdefault("timeout", REQUEST_TIMEOUT)
        kwargs.setdefault("headers", HEADERS)
        kwargs.setdefault("allow_redirects", True)
        resp = getattr(requests, method)(url, **kwargs)
        if resp.status_code == 200:
            return resp
        return None
    except Exception:
        return None


def get_soup(url):
    """Fetch a URL and return a BeautifulSoup object, or None on failure."""
    resp = make_request(url)
    if resp is None:
        return None
    try:
        return BeautifulSoup(resp.text, "lxml")
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

    print(f"Found {len(residents)} residents.")
    return residents


def find_careers_url(company_url):
    """
    Find the careers/jobs page for a company.
    Returns the careers URL string, or None if not found.
    """
    parsed = urlparse(company_url)
    base = f"{parsed.scheme}://{parsed.netloc}"

    company_domain = parsed.netloc

    # 1. Try common career subpaths
    for path in CAREER_PATHS:
        url = base + path
        resp = make_request(url)
        if resp is not None:
            final_url = resp.url
            final_domain = urlparse(final_url).netloc
            # Reject if redirected to a parked/expired domain
            if any(bd in final_domain for bd in CAREERS_DOMAIN_BLACKLIST):
                time.sleep(0.1)
                continue
            # Accept only if still on company domain or a known job board
            on_company = company_domain in final_domain or final_domain in company_domain
            on_job_board = any(jb in final_domain for jb in KNOWN_JOB_BOARDS)
            if (on_company or on_job_board) and urlparse(final_url).path not in ("", "/", "//"):
                # If the careers page directly links to a known job board
                # (e.g. dephy.com/careers → apply.workable.com/dephy/),
                # prefer the board URL so the HTML careers link is accurate.
                m = _BOARD_HREF_RE.search(resp.text)
                if m:
                    time.sleep(REQUEST_DELAY)
                    return m.group(0).rstrip("/") + "/"
                time.sleep(REQUEST_DELAY)
                return final_url
        time.sleep(0.1)

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
        return [{"title": item["text"], "url": item.get("hostedUrl")} for item in data]
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
            {"title": job["title"], "url": job.get("absolute_url")}
            for job in data.get("jobs", [])
        ]
    except Exception:
        return []


def extract_ashby(slug, page_url):
    """Ashby renders jobs server-side; scrape the HTML listing."""
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
        resp = requests.post(
            api_url,
            json={},
            headers={"Content-Type": "application/json"},
            timeout=REQUEST_TIMEOUT,
        )
        if not resp.ok:
            return []
        data = resp.json()
        jobs = []
        for item in data.get("results", []):
            title = item.get("title", "")
            shortcode = item.get("shortcode", "")
            if title and is_job_title(title):
                job_url = (f"https://apply.workable.com/{slug}/j/{shortcode}/"
                           if shortcode else None)
                jobs.append({"title": title, "url": job_url})
        return jobs
    except Exception:
        return []


def extract_rippling(slug, page_url):
    """Rippling ATS: server-side rendered Next.js, scrape the jobs listing page."""
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

    def add_job(title, href=None):
        title = clean_title(title.strip())
        if title and title.lower() not in seen_titles and is_job_title(title):
            seen_titles.add(title.lower())
            full_url = urljoin(url, href) if href else None
            jobs.append({"title": title, "url": full_url})

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
            add_job(title, href)

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
                add_job(title, href=href)

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
                    add_job(title, href=href)

    # Step 3: Whole-page fallback — only if actual career sections were identified.
    # Without identified sections, a full-page scan produces too many false positives.
    if len(jobs) < 2 and have_career_sections:
        for tag in soup.find_all(["li", "h2", "h3"]):
            title = tag.get_text(strip=True)
            add_job(title, href=find_job_url_near(tag))

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

def extract_jobs_with_playwright(url):
    """
    Fetch a page using a real browser (Playwright) and extract jobs from the
    fully-rendered HTML. Used as a fallback when requests-based scraping
    returns nothing — covers Cloudflare-protected boards, Next.js/React SPAs,
    and any other board we haven't seen before.
    """
    if not PLAYWRIGHT_AVAILABLE:
        return []
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
        soup = BeautifulSoup(html, "lxml")
        return extract_jobs_from_html(url, soup=soup)
    except Exception:
        return []


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
    font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
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
.company {
    background: #fff;
    border: 1px solid #ddd;
    border-radius: 6px;
    margin-bottom: 14px;
    padding: 14px 18px;
}
.company-header {
    display: flex;
    align-items: baseline;
    gap: 12px;
    margin-bottom: 8px;
}
.company-name { font-size: 1rem; font-weight: 700; }
.company-name a { color: #202731; text-decoration: none; }
.company-name a:hover { color: #D90B1C; }
.careers-link { font-size: 0.8rem; color: #666; }
.careers-link a { color: #D90B1C; text-decoration: none; }
.careers-link a:hover { text-decoration: underline; }
.job-count { font-size: 0.8rem; color: #888; margin-left: auto; }
ul.jobs { list-style: none; padding-left: 8px; }
ul.jobs li { padding: 4px 0; border-bottom: 1px solid #f0f0f0; font-size: 0.9rem; }
ul.jobs li:last-child { border-bottom: none; }
ul.jobs li a { color: #D90B1C; text-decoration: none; }
ul.jobs li a:hover { text-decoration: underline; }
ul.jobs li .no-link { color: #333; }
"""


LOGO_URL = ("https://www.massrobotics.org/wp-content/uploads/2022/07/"
            "massrobotics-logo.jpg")


def generate_html(results, output_path=OUTPUT_FILE):
    """
    Generate the jobs.html output file.
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
        "</div>",
    ]

    for r in sorted(with_jobs, key=lambda x: x["name"].lower()):
        lines.append('<div class="company">')
        lines.append('  <div class="company-header">')
        lines.append(
            f'    <span class="company-name"><a href="{r["site"]}" target="_blank">'
            f'{_esc(r["name"])}</a></span>'
        )
        if r.get("careers_url"):
            lines.append(
                f'    <span class="careers-link">'
                f'<a href="{r["careers_url"]}" target="_blank">careers page</a></span>'
            )
        lines.append(
            f'    <span class="job-count">{len(r["jobs"])} role'
            f'{"s" if len(r["jobs"]) != 1 else ""}</span>'
        )
        lines.append("  </div>")
        lines.append('  <ul class="jobs">')
        for job in r["jobs"]:
            if job.get("url"):
                lines.append(
                    f'    <li><a href="{job["url"]}" target="_blank">'
                    f'{_esc(job["title"])}</a></li>'
                )
            else:
                lines.append(
                    f'    <li><span class="no-link">{_esc(job["title"])}</span></li>'
                )
        lines.append("  </ul>")
        lines.append("</div>")

    lines += ["</main>", "</body>", "</html>"]

    with open(output_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))

    print(f"Written to {output_path}")


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
        jobs = extract_jobs(careers_url)
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
        "careers_url": careers_url,
        "jobs": jobs,
    }


def main():
    residents = get_residents()
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

    generate_html(results)


if __name__ == "__main__":
    main()
