#!/usr/bin/env bash
# Builds the companion text into site/_out/html-multi. See site/README.md.
#
#   site/build.sh            build and render
#   site/build.sh --draft    extra arguments are passed to the renderer (SiteMain.lean)
#
# Can be run from any directory.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"

# 1. Refuse to touch the shared dependency checkout if the pins disagree with the root package.
python3 check-deps.py

# 2. MD4Lean (a Verso dependency) compiles C code with `cc` from PATH. Machines without a system
#    C compiler (e.g. NixOS) can use the one some Lean toolchains ship next to `lean`.
if ! command -v cc >/dev/null 2>&1; then
  toolchain_bin="$(dirname "$(elan which lean)")"
  if [ -x "$toolchain_bin/cc" ]; then
    export PATH="$toolchain_bin:$PATH"
  else
    echo "build.sh: no C compiler 'cc' found (needed once, to build MD4Lean)" >&2
    exit 1
  fi
fi

# 3. Elaborate the document (and whatever part of MilnorAlgDep it imports).
lake build

# 4. Render the HTML. `versoMain` runs SiteMain.lean in the interpreter, so that Mathlib is never
#    compiled to native code.
rm -rf _out
lake run versoMain SiteMain.lean --output _out "$@"

# 5. Check that every formula is valid KaTeX (Verso itself does not report math errors), and that
#    every internal link works when the site is served under /MilnorAlgDep-lean/.
if command -v node >/dev/null 2>&1; then
  node check-math.js _out/html-multi
else
  echo "build.sh: node not found, skipping the math check" >&2
fi
python3 check-links.py _out/html-multi

echo "Site written to site/_out/html-multi."
echo "Preview: python3 -m http.server --directory site/_out/html-multi 8000"
