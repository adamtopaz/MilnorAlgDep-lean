#!/usr/bin/env python3
"""Check the internal links of the generated site, as served under a URL path prefix.

GitHub Pages serves the site at https://adamtopaz.github.io/MilnorAlgDep-lean/, not at the root
of a domain. Every page has a `<base href>` pointing at the site root, so a link only works there
if it is relative and written relative to the site root; a bare `#anchor` resolves against the
front page, and an absolute `/path` escapes the prefix. This script resolves every internal
`href`/`src` of every page as the browser would under the prefix, and checks that the target file
and, for links into generated pages, the target anchor exist.

Usage: python3 check-links.py [_out/html-multi]
"""

import html.parser
import pathlib
import sys
import urllib.parse

ORIGIN = "https://example.org"
PREFIX = "/MilnorAlgDep-lean/"


class Page(html.parser.HTMLParser):
    def __init__(self):
        super().__init__()
        self.base = None
        self.links = []
        self.ids = set()

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if a.get("id"):
            self.ids.add(a["id"])
        if tag == "base":
            if self.base is None:
                self.base = a.get("href")
            return
        for k in ("href", "src"):
            if a.get(k):
                self.links.append(a[k])


def main():
    root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1
                        else pathlib.Path(__file__).parent / "_out" / "html-multi").resolve()
    pages = {}
    for f in root.rglob("*.html"):
        p = Page()
        p.feed(f.read_text(encoding="utf-8"))
        pages[f] = p

    errors = []
    checked = 0
    for f, p in sorted(pages.items()):
        rel = f.relative_to(root).as_posix()
        page_url = ORIGIN + PREFIX + rel.removesuffix("index.html")
        base_url = urllib.parse.urljoin(page_url, p.base) if p.base is not None else page_url
        for v in p.links:
            target = urllib.parse.urlparse(urllib.parse.urljoin(base_url, v))
            if target.scheme + "://" + target.netloc != ORIGIN:
                continue  # external
            checked += 1
            if not target.path.startswith(PREFIX):
                errors.append(f"{rel}: {v!r} leaves the site (resolves to {target.path})")
                continue
            local = root / urllib.parse.unquote(target.path[len(PREFIX):])
            if target.path.endswith("/") or local.is_dir():
                local = local / "index.html"
            if not local.exists():
                errors.append(f"{rel}: {v!r} points to a missing file "
                              f"{local.relative_to(root).as_posix()}")
                continue
            frag = urllib.parse.unquote(target.fragment)
            if frag and local in pages and frag not in pages[local].ids:
                errors.append(f"{rel}: {v!r} points to a missing anchor #{frag} in "
                              f"{local.relative_to(root).as_posix()}")

    for e in errors:
        print(e, file=sys.stderr)
    print(f"check-links: {checked} internal links on {len(pages)} pages, {len(errors)} errors")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
