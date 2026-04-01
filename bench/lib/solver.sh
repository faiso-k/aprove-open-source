
# lib/solver.sh
set -euo pipefail

: "${APROVE:=/opt/bundle/aprove.jar}"
: "${CPF_CONVERTER:=/opt/bundle/cpfconverter/cpf2_to_3.sh}"
: "${JAVA:=java}"                 # or point to your jenv shim
: "${JAVA_PLAIN_OPTS:=-ea}"
: "${JAVA_HEAVY_OPTS:=-Xmx14G -Xms14G -ea}"

mkinput() {                      # mkinput OUTFILE line... + benchmark
  out="$1"; shift
  { for l in "$@"; do [ -n "$l" ] && printf '%s\n' "$l"; done; cat; } > "$out"
}

run_plain() {                    # run_plain INPUT [heavy]
  if [ "${2:-}" = heavy ]; then
    exec 3>&1; "$JAVA" $JAVA_HEAVY_OPTS -jar "$APROVE" -m wst -p plain "${@:3}" "$1" 1>&3 
  else
    exec 3>&1; "$JAVA" $JAVA_PLAIN_OPTS -jar "$APROVE" -m wst -p plain "${@:3}" "$1" 1>&3 
  fi
}

run_cpf_convert() {              # run_cpf_convert INPUT [heavy] [extra opts...]
  tmp1="$(mktemp)"; trap 'rm -f "$tmp1" "$tmp2"' RETURN
  if [ "${2:-}" = heavy ]; then
    shift; HEAVY=1
    "$JAVA" $JAVA_HEAVY_OPTS -jar "$APROVE" -m wst -p cpf -C ceta "$@" 1> "$tmp1" 2>/dev/null
  else
    "$JAVA" $JAVA_PLAIN_OPTS -jar "$APROVE" -m wst -p cpf -C ceta "$@" 1> "$tmp1" 2>/dev/null
  fi
  decision="$(head -n1 "$tmp1")"
  echo "$decision"
  if [[ "$decision" == YES || "$decision" == NO ]]; then
    tmp2="$(mktemp)"
    tail -n +2 "$tmp1" > "$tmp2"
    "$CPF_CONVERTER" "$tmp2"
  fi
}

eff_timeout() {                  # eff_timeout TIMEOUT subtract_if_large
  T="$1"; SUB="${2:-0}"
  if [ "$T" -gt $((SUB+5)) ]; then echo $((T - SUB)); else echo "$T"; fi
}
