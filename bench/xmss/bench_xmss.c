#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "bench_common.h"
#include "config.h"
#include "macros.h"
#include "params.h"
#include "xmss.h"

#ifndef IMPL
#error IMPL must be defined
#endif

#ifndef FILENAME
#define FILENAME "xmss_results.txt"
#endif

#ifndef MESSAGE_SIZE
#define MESSAGE_SIZE 128
#endif

extern int xmssmt_keypair_jazz(uint8_t *pk, uint8_t *sk);

bool verbose = true;

static size_t find_min_index(const uint64_t *array, size_t size) {
    size_t min_index = 0;
    for (size_t i = 1; i < size; i++) {
        if (array[i] < array[min_index]) {
            min_index = i;
        }
    }
    return min_index;
}

xmss_params setup_params(void) {
    xmss_params p;
    uint32_t oid;

    if (xmssmt_str_to_oid(&oid, xstr(IMPL)) == -1) {
        fprintf(stderr, "Failed to generate oid from impl name\n");
        exit(EXIT_FAILURE);
    }

    if (xmssmt_parse_oid(&p, oid) == -1) {
        fprintf(stderr, "Failed to generate params from oid\n");
        exit(EXIT_FAILURE);
    }

    return p;
}

uint32_t setup_oid(void) {
    uint32_t oid;

    if (xmssmt_str_to_oid(&oid, xstr(IMPL)) == -1) {
        fprintf(stderr, "Failed to generate oid from impl name\n");
        exit(EXIT_FAILURE);
    }

    return oid;
}

void clearfile(const char *filename) {
    FILE *f = NULL;
    if (!(f = fopen(filename, "w"))) {
        fprintf(stderr, "Failed to open %s\n", filename);
        exit(EXIT_FAILURE);
    }
    fclose(f);
}

void print_header(const char *filename) {
    FILE *f = NULL;
    if (!(f = fopen(filename, "w"))) {
        fprintf(stderr, "Failed to open %s\n", filename);
        exit(EXIT_FAILURE);
    }
    fprintf(f, "Function;Average;Median\n");
    fclose(f);
}

static inline uint64_t cpucycles(void) {
    uint64_t result;

    asm volatile("rdtsc; shlq $32,%%rdx; orq %%rdx,%%rax" : "=a"(result) : : "%rdx");

    return result;
}

/*
 * Func is a wrapper around the function to be benchmarked. It sets up the
 * xmss_params and register the cycles before and after executing the function.
 */
void bench_function(void (*func)(uint64_t *, uint64_t *), const char *s) {
    uint64_t observations[RUNS][TIMINGS] = {0};
    uint64_t medians[RUNS] = {0};
    uint64_t averages[RUNS] = {0};
    uint64_t before, after;

    uint64_t cpucycles_overhead = overhead_of_cpucycles_call();

    for (int run = 0; run < RUNS; run++) {
        for (int i = 0; i + 1 < TIMINGS; i++) {
            if (verbose) {
                printf("[%s]: Timing %d/%d (Run %d/%d)\n", s, i + 1, TIMINGS - 1, run + 1, RUNS);
            }

            func(&before, &after);

            observations[run][i] = (after - cpucycles_overhead) - before;
        }
        medians[run] = average(observations[run], TIMINGS);
        averages[run] = median(observations[run], TIMINGS);
    }

    size_t index = find_min_index(medians, RUNS);
    uint64_t median_val = medians[index];
    uint64_t average_val = averages[index];

    FILE *f = NULL;
    if (!(f = fopen(FILENAME, "a"))) {
        fprintf(stderr, "Failed to open %s for writing\n", FILENAME);
        exit(EXIT_FAILURE);
    }

    assert(f != NULL);

    fprintf(f, "%s;%" PRIu64 ";%" PRIu64 "\n", s, average_val, median_val);
    fclose(f);
}

void bench_xmssmt_kg_ref(uint64_t *before, uint64_t *after) {
    uint32_t oid = setup_oid();
    xmss_params p = setup_params();

    uint8_t sk[p.sk_bytes];
    uint8_t pk[p.pk_bytes];

    *before = cpucycles();
    xmssmt_keypair(pk, sk, oid);
    *after = cpucycles();
}

void bench_xmssmt_kg_jasmin(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    uint8_t sk[p.sk_bytes];
    uint8_t pk[p.pk_bytes];

    *before = cpucycles();
    xmssmt_keypair_jazz(pk, sk);
    *after = cpucycles();
}

int main(void) {
    bench_function(bench_xmssmt_kg_ref, "kg_ref");
    bench_function(bench_xmssmt_kg_jasmin, "kg_jasmin");
    return EXIT_SUCCESS;
}