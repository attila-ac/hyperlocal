#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-formalisation/Hyperlocal}"

tmp_axioms="$(mktemp)"
trap 'rm -f "$tmp_axioms"' EXIT

echo "=== DISTINCT AXIOM DECLARATIONS ==="
rg -n '^[[:space:]]*axiom[[:space:]]+' "$ROOT" \
  | tee "$tmp_axioms" \
  | sed -E 's#^([^:]+):([0-9]+):[[:space:]]*axiom[[:space:]]+([^ (:{]+).*#\3\t\1:\2#' \
  | sort -u \
  | awk -F '\t' '{printf "%-45s %s\n",$1,$2}'

echo
count="$(sed -E 's#^([^:]+):([0-9]+):[[:space:]]*axiom[[:space:]]+([^ (:{]+).*#\3#' "$tmp_axioms" | sort -u | wc -l | tr -d ' ')"
echo "=== ABSOLUTE DISTINCT AXIOM COUNT ==="
echo "$count"

echo
echo "=== RAW DECLARATION LINES ==="
sort "$tmp_axioms"

echo
echo "=== USAGE BY AXIOM (EXCLUDING DECLARATION LINE) ==="
sed -E 's#^([^:]+):([0-9]+):[[:space:]]*axiom[[:space:]]+([^ (:{]+).*#\3\t\1\t\2#' "$tmp_axioms" \
| sort -u \
| while IFS=$'\t' read -r ax file line; do
  echo "===== $ax ====="
  rg -n "\\b${ax}\\b" "$ROOT" \
    | awk -F: -v f="$file" -v l="$line" '!( $1==f && $2==l )'
  echo
done
