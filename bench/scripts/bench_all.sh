#!/bin/bash

bench_dirs=(
    "hash"
    "wots"
    # "bench/treehash_jasmin_vs_new"
)

SCRIPT_DIR=$(pwd $(dirname "$0"))

mkdir -p $SCRIPT_DIR/../bench_results/

for dir in "${bench_dirs[@]}"; do
    make -C "$SCRIPT_DIR/../$dir/" "run"
    mv "$SCRIPT_DIR/../$dir/results.txt" "$SCRIPT_DIR/../bench_results/results_$(basename "$dir").txt"
done
