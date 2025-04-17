#!/bin/bash

export DISPLAY=:0

notify() {
    local title="$1"
    local message="$2"
    if [ "$(hostname)" = "rui-ThinkPad-T16-Gen-2" ]; then
        notify-send "$title" "$message" || echo "Failed to send notification"
    fi
}

bench_dirs=(
    "hash"
    "wots"
    # "bench/treehash_jasmin_vs_new"
)

SCRIPT_DIR=$(dirname "$0")

rm -rf "$SCRIPT_DIR/../bench_results/" # remove old results 
mkdir -p "$SCRIPT_DIR/../bench_results/"

# Check if notify-send is installed
if ! command -v notify-send &> /dev/null; then
    echo "notify-send is not installed. Install with sudo apt install libnotify-bin"
    notify_send_installed=false
else 
    notify_send_installed=true
fi

for dir in "${bench_dirs[@]}"; do
    make -C "$SCRIPT_DIR/../$dir/" "run"
    mv "$SCRIPT_DIR/../$dir/results.txt" "$SCRIPT_DIR/../bench_results/results_$(basename "$dir").txt"
    
    if [ "$notify_send_installed" ]; then
        notify "Benchmark XMSS" "Benchmarking for $dir is done"
    fi
done
