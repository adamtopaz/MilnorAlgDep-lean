#!/usr/bin/env bash
# Run once from the root of a fresh git worktree of this repo.
# Shares the (read-only) dependency checkout + Mathlib build cache of the main checkout,
# so that no worktree ever downloads or rebuilds Mathlib.
set -euo pipefail
MAIN=/home/adam/projects/autoformalization/MilnorAlgDep
here=$(git rev-parse --show-toplevel)
if [ "$here" = "$MAIN" ]; then echo "already in main checkout"; exit 0; fi
mkdir -p "$here/.lake"
if [ ! -e "$here/.lake/packages" ]; then
  ln -s "$MAIN/.lake/packages" "$here/.lake/packages"
fi
echo "worktree ready: $here"
