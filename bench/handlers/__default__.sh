#!/usr/bin/env bash

set -euo pipefail
. "$(dirname "$0")/../lib/solver.sh"

# $BENCHMARK path/to/problem.extension
# where extension is provided by config

if [ "${CERT:-false}" = true ]; then
  run_cpf_convert "$BENCHMARK"
else
  run_plain "$BENCHMARK"
fi
