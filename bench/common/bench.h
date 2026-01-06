#ifndef BENCHMARK_H
#define BENCHMARK_H

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

// From https://github.com/formosa-crypto/formosa-mldsa/blob/main/bench/bench_jasmin.c
static inline uint64_t cpucycles(void) {
    uint64_t result;

    asm volatile("rdtsc; shlq $32,%%rdx; orq %%rdx,%%rax" : "=a"(result) : : "%rdx");

    return result;
}

// From https://github.com/formosa-crypto/formosa-mldsa/blob/main/bench/bench_jasmin.c
static int cmp_uint64(const void *a, const void *b) {
#ifdef DEBUG
    if (a == NULL && b == NULL) {
        perror("cmp_uint64: both arguments are NULL");
        return 0;
    }

    if (a == NULL) {
        perror("cmp_uint64: first argument is NULL");
        return 0;
    }

    if (b == NULL) {
        perror("cmp_uint64: second argument is NULL");
        return 0;
    }
#endif

    if (*(uint64_t *)a < *(uint64_t *)b) {
        return -1;
    }
    if (*(uint64_t *)a > *(uint64_t *)b) {
        return 1;
    }

    return 0;
}

// From https://github.com/formosa-crypto/formosa-mldsa/blob/main/bench/bench_jasmin.c
static uint64_t median(uint64_t *l, size_t llen) {
#ifdef DEBUG
    if (l == NULL) {
        perror("median: pointer argument is NULL");
        return 0;
    }
#endif

    qsort(l, llen, sizeof(uint64_t), cmp_uint64);

    if (llen % 2) {
        return l[llen / 2];
    } else {
        return (l[llen / 2 - 1] + l[llen / 2]) / 2;
    }
}

// From https://github.com/formosa-crypto/formosa-mldsa/blob/main/bench/bench_jasmin.c
static uint64_t average(uint64_t *t, size_t tlen) {
#ifdef DEBUG
    if (t == NULL) {
        perror("average: pointer argument is NULL");
        return 0;
    }
#endif

    size_t i;
    uint64_t acc = 0;

    for (i = 0; i < tlen; i++) {
        acc += t[i];
    }

    return acc / tlen;
}

static uint64_t overhead_of_cpucycles_call(void) {
    uint64_t t0, t1, overhead = -1LL;
    unsigned int i;

    for (i = 0; i < 100000; i++) {
        t0 = cpucycles();
        __asm__ volatile("");
        t1 = cpucycles();
        if (t1 - t0 < overhead) {
            overhead = t1 - t0;
        }
    }

    return overhead;
}

/*
 * This macro benchmarks a function call `N` times and writes the
 * raw clock cycle counts for each execution to a file.
 *
 * Usage:
 *   BENCHMARK_N_TIMES(1000, "results.txt", my_function(arg1));
 */

#define BENCHMARK_N_TIMES(N, filename, func_call)                                            \
    do {                                                                                     \
        FILE *fp = fopen(filename, "w");                                                     \
        if (fp == NULL) {                                                                    \
            fprintf(stderr, "Failed to open file for benchmarking results: %s: ", filename); \
            perror("");                                                                      \
            break;                                                                           \
        }                                                                                    \
                                                                                             \
        for (int i = 0; i < (N); ++i) {                                                      \
            unsigned long long start_cycles, end_cycles;                                     \
            start_cycles = cpucycles();                                                      \
            func_call;                                                                       \
            end_cycles = cpucycles();                                                        \
            fprintf(fp, "%llu\n", end_cycles - start_cycles);                                \
        }                                                                                    \
        fclose(fp);                                                                          \
        printf("Benchmark results for %d executions written to '%s'\n", (N), (filename));    \
    } while (0)

#endif  // BENCHMARK_H
