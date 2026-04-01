#!/bin/bash

TPDB=/Users/jckassing/Desktop/Aprove/TPDB-ARI
BASEDIR=results
FLAT_CSV="$BASEDIR/flat.csv"
SAMPLE=""
SAMPLE_PCT=""
CONFIG_DIR="example_configs"
LOCAL=""
IMAGE=""

usage() {
    echo "Usage: $0 [--tpdb PATH] [--sample N] [--sample-pct PCT] [--flat-csv PATH] [--config-dir DIR] [--local] [--image TAG]"
    exit 1
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --tpdb)       TPDB="$2";       shift 2 ;;
        --sample)     SAMPLE="$2";     shift 2 ;;
        --sample-pct) SAMPLE_PCT="$2"; shift 2 ;;
        --flat-csv)   FLAT_CSV="$2";   shift 2 ;;
        --config-dir) CONFIG_DIR="$2"; shift 2 ;;
        --local)      LOCAL="--local"; shift ;;
        --image)      IMAGE="$2";      shift 2 ;;
        *) usage ;;
    esac
done

SAMPLE_ARG=""
if [[ -n "$SAMPLE" ]]; then
    SAMPLE_ARG="--sample $SAMPLE"
elif [[ -n "$SAMPLE_PCT" ]]; then
    SAMPLE_ARG="--sample-pct $SAMPLE_PCT"
fi

IMAGE_ARG=""
if [[ -z "$LOCAL" && -n "$IMAGE" ]]; then
    IMAGE_ARG="--image $IMAGE"
fi

for c in "$CONFIG_DIR"/*.toml; do
    name=$(basename "$c" .toml)
    echo "Running benchmark with config: $c -> $BASEDIR/$name"
    python3 benchmark.py $LOCAL $IMAGE_ARG -f "$TPDB" -j 8 -c "$c" -o "$BASEDIR/$name" -F "$FLAT_CSV" -t 60 $SAMPLE_ARG
done
