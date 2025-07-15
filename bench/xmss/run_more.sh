#!/bin/bash

for i in {0..10}
do
    ./run.sh
    mv results.csv results_${i}.csv
done
