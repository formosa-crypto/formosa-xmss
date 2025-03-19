#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "bench_common.h"
#include "config.h"
#include "hash.h"
#include "macros.h"
#include "params.h"

#ifndef IMPL
#define IMPL XMSSMT-SHA2_20/2_256
#endif

#ifndef FILENAME
#define FILENAME "results.txt"
#endif

extern void prf_jazz(uint8_t *out, const uint8_t *in, const uint8_t *key);

bool verbose = true;

void clearfile(const char *filename) {
    FILE *f = NULL;
    if (!(f = fopen(filename, "w"))) {
        fprintf(stderr, "Failed to open %s\n", filename);
        exit(EXIT_FAILURE);
    }
    fclose(f);
}

static inline uint64_t cpucycles(void) {
    uint64_t result;

    asm volatile("rdtsc; shlq $32,%%rdx; orq %%rdx,%%rax" : "=a"(result) : : "%rdx");

    return result;
}

void bench_function(void (*func)(uint64_t *, uint64_t *), const char *s) {
    uint64_t observations[TIMINGS] = {0};
    uint64_t before, after;

    uint64_t cpucycles_overhead = overhead_of_cpucycles_call();

    for (int i = 0; i + 1 < TIMINGS; i++) {
        if (verbose) {
            printf("[%s]: Timing %d/%d\n", s, i + 1, TIMINGS - 1);
        }

        func(&before, &after);

        observations[i] = (after - cpucycles_overhead) - before;
    }

    uint64_t average_val = average(observations, TIMINGS);
    uint64_t median_val = median(observations, TIMINGS);

    FILE *f = NULL;
    if (!(f = fopen(FILENAME, "a"))) {
        fprintf(stderr, "Failed to open %s for writing\n", FILENAME);
        exit(EXIT_FAILURE);
    }

    assert(f != NULL);

    fprintf(f, "%s;%" PRIu64 ";%" PRIu64 "\n", s, average_val, median_val);
    fclose(f);
}

void bench_prf_jasmin(uint64_t *before, uint64_t *after) {
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

    uint8_t out[p.n];
    uint8_t in[32];
    uint8_t key[p.n];

    *before = cpucycles();
    prf_jazz(out, in, key);
    *after = cpucycles();
}

void bench_prf_c(uint64_t *before, uint64_t *after) {
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

    uint8_t out[p.n];
    uint8_t in[32];
    uint8_t key[p.n];

    *before = cpucycles();
    prf(&p, out, in, key);
    *after = cpucycles();
}

int main(void) {
    clearfile(FILENAME);

    bench_function(bench_prf_jasmin, "prf_jasmin");
    bench_function(bench_prf_c, "prf_ref");

    return EXIT_SUCCESS;
}