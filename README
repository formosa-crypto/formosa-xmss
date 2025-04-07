This currently runs with the following tool versions:

EasyCrypt (security) version: r2025.02
EasyCrypt (correctness) version: r2025.02

Jasmin & ECLib: release-2025.02


## Benchmark results

#### Hash 

| Function       | Median Jasmin | Median Ref | Faster Implementation | Diff (%) |
|----------------|---------------|------------|------------------------|----------|
| hash_message   | 5670          | 4782       | Ref                    | 18.57    |
| prf            | 2403          | 3275       | Jasmin                 | 26.63    |
| prf_keygen     | 3371          | 3762       | Jasmin                 | 10.39    |
| thash_f        | 7057          | 9273       | Jasmin                 | 23.90    |
| thash_h        | 10445         | 12702      | Jasmin                 | 17.77    |


#### WOTS

<!-- cat .ssh/config | grep -oE "Host bench-.+" | cut -d' ' -f2-->
Run on 

- [X] bench-mpi-6700K
- [ ] bench-mpi-8700K
- [ ] bench-mpi-11700K
- [ ] bench-mpi-12700K
- [ ] bench-mpi-13700K
- [ ] bench-mpi-13900K
