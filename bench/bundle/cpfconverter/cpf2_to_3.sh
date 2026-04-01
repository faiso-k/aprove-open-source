#!/bin/bash
# converts CPF 2 file to CPF 3
# usage: ./cpf2_to_3.sh [--termIndex] [cpf2.xml | - ]

# Get absolute directory of this script
DIR=$(dirname "$(readlink -f "$0")")

# Check dependencies
command -v xmllint >/dev/null 2>&1 || { echo >&2 "Error: xmllint is not installed."; exit 1; }
command -v xsltproc >/dev/null 2>&1 || { echo >&2 "Error: xsltproc is not installed."; exit 1; }
if [[ ! -x "${DIR}/cpf2_to_3_phase_1" ]]; then
    echo >&2 "Error: ${DIR}/cpf2_to_3_phase_1 is not found or not executable."
    exit 1
fi
if [[ ! -f "${DIR}/cpf2_to_3.xsl" ]]; then
    echo >&2 "Error: ${DIR}/cpf2_to_3.xsl not found."
    exit 1
fi

# Run phase 1, process large XML safely, then transform with XSLT
"${DIR}/cpf2_to_3_phase_1" "$@" \
    | xmllint --huge - \
    | xsltproc --huge --maxdepth 100000 "${DIR}/cpf2_to_3.xsl" -

