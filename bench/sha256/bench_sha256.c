#include <assert.h>
#include <inttypes.h>
#include <openssl/sha.h>
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
#include "randombytes.h"

#ifndef FILENAME
#define FILENAME "results.txt"
#endif

#ifndef MESSAGE_SIZE
#define MESSAGE_SIZE 128
#endif

extern void sha256_96(uint8_t *, const uint8_t *);
extern void sha256_128(uint8_t *, const uint8_t *);

bool verbose = true;

void clearfile(const char *filename) {
    FILE *f = NULL;
    if (!(f = fopen(filename, "w"))) {
        fprintf(stderr, "Failed to open %s\n", filename);
        exit(EXIT_FAILURE);
    }
    fclose(f);
}

static uint32_t random_valid_idx(const xmss_params *p) {
    return rand() % (1 << (uint32_t)(1 << p->tree_height));
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

void bench_sha256_96_jasmin(uint64_t *before, uint64_t *after) {
    uint8_t out[32];
    uint8_t in[96];

    randombytes(in, 96);

    *before = cpucycles();
    sha256_96(out, in);
    *after = cpucycles();
}

void bench_sha256_96_c(uint64_t *before, uint64_t *after) {
    uint8_t out[32];
    uint8_t in[96];

    randombytes(in, 96);

    *before = cpucycles();
    SHA256(in, 96, out);
    *after = cpucycles();
}

void bench_sha256_128_jasmin(uint64_t *before, uint64_t *after) {
    uint8_t out[32];
    uint8_t in[128];

    randombytes(in, 128);

    *before = cpucycles();
    sha256_128(out, in);
    *after = cpucycles();
}

void bench_sha256_128_c(uint64_t *before, uint64_t *after) {
    uint8_t out[32];
    uint8_t in[128];

    randombytes(in, 128);

    *before = cpucycles();
    SHA256(in, 128, out);
    *after = cpucycles();
}

int main(void) {
    clearfile(FILENAME);
    print_header(FILENAME);

    bench_function(bench_sha256_96_c, "c_96");
    bench_function(bench_sha256_96_jasmin, "jasmin_96");

    bench_function(bench_sha256_128_c, "c_128");
    bench_function(bench_sha256_128_jasmin, "jasmin_128");

    return EXIT_SUCCESS;
}