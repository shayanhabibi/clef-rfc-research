#!/usr/bin/env bash
# Starts an RFC from proofs/template: new-rfc.sh <four-digit number> "<title>"
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"

if [[ $# -ne 2 || ! $1 =~ ^[0-9]{4}$ ]]; then
  echo 'usage: new-rfc.sh <four-digit number> "<title>"' >&2
  exit 1
fi

number=$1
title=$2
target="theories/RFC$number"

if [[ -e $target ]]; then
  echo "$target already exists" >&2
  exit 1
fi

mkdir -p "$target"
for module in Overview Design Discussion; do
  NUMBER=$number TITLE=$title DATE=$(date +%F) awk '
    { gsub(/NNNN/, ENVIRON["NUMBER"]); gsub(/TITLE/, ENVIRON["TITLE"]); gsub(/DATE/, ENVIRON["DATE"]); print }
  ' "template/$module.v" > "$target/$module.v"
  printf '%s\n' "$target/$module.v" >> _CoqProject
done

echo "Created $target. Next: bash proofs/build.sh"
