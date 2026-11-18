#!/usr/bin/env bash
# Regenerate the root import file `MilnorAlgDep.lean` as a module importing every file.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
{
  echo "module"
  echo
  find MilnorAlgDep -name '*.lean' | LC_ALL=C sort | sed -e 's/\.lean$//' -e 's#/#.#g' -e 's/^/public import /'
} > MilnorAlgDep.lean
