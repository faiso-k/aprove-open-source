#!/usr/bin/env bash
set -euo pipefail
. "$(dirname "$0")/../lib/solver.sh"
: "${JAVA:=java}"

TO="$(eff_timeout "${TIMEOUT:-60}" 2)"

ast_dir="$(mktemp -d)"; sast_dir="$(mktemp -d)"
trap 'rm -rf "$ast_dir" "$sast_dir"' EXIT

ASTTRS="$ast_dir/ast.ari"
SASTTRS="$sast_dir/sast.ari"
ANS_AST="$(mktemp)"; ANS_SAST="$(mktemp)"
trap 'rm -rf "$ast_dir" "$sast_dir" "$ANS_AST" "$ANS_SAST"' EXIT

mkinput "$ASTTRS"  "(GOAL AST)" "(STRATEGY INNERMOST)"            < "$BENCHMARK"
mkinput "$SASTTRS" "(GOAL COMPLEXITY)" "(STRATEGY INNERMOST)"     < "$BENCHMARK"

[ "${PRINT_INPUT:-0}" = 1 ] && { printf '%s\n' "---BEGIN AST INPUT---" >&2; head -n 20 "$ASTTRS" >&2; printf '%s\n' "---BEGIN SAST INPUT---" >&2; head -n 20 "$SASTTRS" >&2; printf '%s\n' "---END---" >&2; }

$JAVA $JAVA_PLAIN_OPTS -jar "$APROVE" -m wst       -p plain -t "$TO" "$ASTTRS"  1> "$ANS_AST"
LD_LIBRARY_PATH=../lib:${LD_LIBRARY_PATH:-} PATH=.:$PATH \
$JAVA $JAVA_PLAIN_OPTS -jar "$APROVE" -m benchmark -p plain -t "$TO" "$SASTTRS" 1> "$ANS_SAST"

first_ast="$(head -n1 "$ANS_AST")"
first_sast="$(head -n1 "$ANS_SAST")"

if grep -Eq '^(.*O\(1\).*|.*O\(n\^[0-9]+\).*|.*EXP.*|.*2-EXP.*)$' <<<"$first_sast"; then
  echo "SAST"; tail -n +2 "$ANS_SAST"
elif [[ "$first_ast" == "YES" ]]; then
  echo "AST";  tail -n +2 "$ANS_AST"
else
  echo "MAYBE"
fi
