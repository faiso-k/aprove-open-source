#!/usr/bin/env bash
set -euo pipefail
. "$(dirname "$0")/../lib/solver.sh"
: "${JAVA:=java}"

tmpdir="$(mktemp -d)"; trap 'rm -rf "$tmpdir"' EXIT
tmp="$tmpdir/input.ari"
r1="$(mktemp)"; r2="$(mktemp)"; r3="$(mktemp)"; trap 'rm -rf "$tmpdir" "$r1" "$r2" "$r3"' EXIT

mkinput "$tmp" "(GOAL COMPLEXITY)" "(STRATEGY INNERMOST)" < "$BENCHMARK"
TO="$(eff_timeout "${TIMEOUT:-60}" 10)"

[ "${PRINT_INPUT:-0}" = 1 ] && { printf '%s\n' "---BEGIN INPUT (DCI_Rewriting)---" >&2; cat "$tmp" >&2; printf '%s\n' "---END INPUT---" >&2; }

if [ "${CERT:-false}" = true ]; then
  $JAVA $JAVA_HEAVY_OPTS -jar "$APROVE" -m wst -p cpf -C ceta -w 4 -t "$TO" "$tmp" 1> "$r1"
  tail -n +2 "$r1" > "$r2"
  "$CPF_CONVERTER" "$r2" > "$r3"
  head -n 1 "$r1"
  cat "$r3"
else
  $JAVA $JAVA_HEAVY_OPTS -jar "$APROVE" -m wst -p plain -w 4 -t "$TO" "$tmp"
fi
