#!/bin/bash

test_dirs=("hash" "wots")

for dir in "${test_dirs[@]}"; do
    echo "Running tests for ${dir}"
    make -C ../test/${dir}/ clean run
done
