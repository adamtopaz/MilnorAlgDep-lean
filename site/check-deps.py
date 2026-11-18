#!/usr/bin/env python3
"""Check that the site package pins the same dependencies as the root package.

The site package (`site/`) shares the root's dependency directory (`packagesDir =
"../.lake/packages"` in `site/lakefile.toml`). Before building, Lake checks out every package at
the revision recorded in the *site* manifest. If that differed from the root manifest, a site
build would move the shared Mathlib checkout to another revision, and the next root build would
rebuild Mathlib. This script refuses to let that happen: run it before any `lake` command in
`site/` (`build.sh` does).

Usage: python3 site/check-deps.py
"""

import json
import pathlib
import sys

SITE = pathlib.Path(__file__).resolve().parent
ROOT = SITE.parent


def load(path):
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def main():
    errors = []

    root_tc = (ROOT / "lean-toolchain").read_text().strip()
    site_tc = (SITE / "lean-toolchain").read_text().strip()
    if root_tc != site_tc:
        errors.append(f"lean-toolchain: root has {root_tc}, site has {site_tc}")

    root = {p["name"]: p for p in load(ROOT / "lake-manifest.json")["packages"]}
    site = {p["name"]: p for p in load(SITE / "lake-manifest.json")["packages"]}

    for name, p in root.items():
        q = site.get(name)
        if q is None:
            errors.append(f"{name}: in the root manifest but not in the site manifest")
            continue
        for field in ("type", "url", "rev"):
            if p.get(field) != q.get(field):
                errors.append(
                    f"{name}: {field} is {p.get(field)!r} in the root manifest "
                    f"but {q.get(field)!r} in the site manifest")

    me = site.get("MilnorAlgDep")
    if me is None or me.get("type") != "path" or me.get("dir") not in ("..", "../"):
        errors.append("MilnorAlgDep: the site manifest must require it as the path dependency '..'")

    if errors:
        print("check-deps: site/lake-manifest.json is out of sync with lake-manifest.json:",
              file=sys.stderr)
        for e in errors:
            print("  - " + e, file=sys.stderr)
        print("Do not run lake in site/ until this is fixed (it would check out other revisions\n"
              "in the shared .lake/packages). See 'Updating dependencies' in site/README.md.",
              file=sys.stderr)
        return 1
    print(f"check-deps: OK ({len(root)} shared packages, {root_tc})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
