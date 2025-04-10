#!/bin/bash

bench_dirs=(
    "bench/hash"
    "bench/wots"
    "bench/treehash"
)

mkdir -p ../bench_results/

for dir in "${bench_dirs[@]}"; do
    make -C "$(dirname "$0")/../$dir/ run"
    mv "$(dirname "$0")/../$dir/results.txt" "../bench_results/results_$(basename "$dir").txt"
done
