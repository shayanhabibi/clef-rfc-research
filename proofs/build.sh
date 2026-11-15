#!/usr/bin/env bash
# Checks every proof with the Rocq on PATH, in the order _CoqProject lists the files.
# Each file gets a .vo and a .glob beside it, which the site build and rocq-capture read.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
grep -E '\.v$' _CoqProject | tr -d '\r' | while read -r file; do
  echo "rocq compile $file"
  rocq compile -Q theories Clef "$file"
done
