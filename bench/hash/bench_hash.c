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
#error IMPL must be defined
#endif

#ifndef FILENAME
#define FILENAME "results_no_zeroization.txt"
#endif

#ifndef MESSAGE_SIZE
#define MESSAGE_SIZE 128
#endif

extern void prf_jazz(uint8_t *out, const uint8_t *in, const uint8_t *key);
extern void prf_keygen_jazz(uint8_t *out, const uint8_t *in, const uint8_t *key);
extern void hash_message_jazz(uint8_t *mhash, const uint8_t *r, const uint8_t *root, uint64_t idx,
                              uint8_t *m, size_t mlen);
extern void thash_h_jazz(uint8_t *out, uint32_t *addr, const uint8_t *in, const uint8_t *pub_seed);
extern void thash_f_jazz(uint8_t *out, uint32_t *addr, const uint8_t *pub_seed);

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
 * Func is a wrapper around the function to be benchmarked. 
 * It sets up the registers the cycles before and after executing the function and 
 * writes the result to a file.
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
    if (!(f = fopen((xstr(FILENAME)), "a"))) {
        fprintf(stderr, "Failed to open %s for writing\n", (xstr(FILENAME)));
        exit(EXIT_FAILURE);
    }

    assert(f != NULL);

#ifdef ZEROIZATION_STRATEGY
#ifndef ZEROIZATION_SIZE
#error ZEROIZATION_SIZE must be defined when ZEROIZATION_STRATEGY is defined
#else
    fprintf(f, "%s_%s_%s;%" PRIu64 ";%" PRIu64 "\n", s, xstr(ZEROIZATION_STRATEGY),
            xstr(ZEROIZATION_SIZE), average_val, median_val);
#endif
#else
    fprintf(f, "%s;%" PRIu64 ";%" PRIu64 "\n", s, average_val, median_val);
#endif
    fclose(f);
}

void bench_prf_jasmin(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    uint8_t out[p.n];
    uint8_t in[32];
    uint8_t key[p.n];

    *before = cpucycles();
    prf_jazz(out, in, key);
    *after = cpucycles();
}

void bench_prf_c(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    uint8_t out[p.n];
    uint8_t in[32];
    uint8_t key[p.n];

    *before = cpucycles();
    prf(&p, out, in, key);
    *after = cpucycles();
}

void bench_prf_keygen_jasmin(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    uint8_t out[p.n];
    uint8_t in[p.n + 32];
    uint8_t key[p.n];

    *before = cpucycles();
    prf_keygen_jazz(out, in, key);
    *after = cpucycles();
}

void bench_prf_keygen_ref(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    uint8_t out[p.n];
    uint8_t in[p.n + 32];
    uint8_t key[p.n];

    *before = cpucycles();
    prf_keygen(&p, out, in, key);
    *after = cpucycles();
}

void bench_hash_message_jasmin(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    uint64_t idx = (uint64_t)random_valid_idx(&p);
    uint8_t mhash[p.n];
    uint8_t r[p.n];
    uint8_t root[p.n];
    uint8_t m[MESSAGE_SIZE];

    *before = cpucycles();
    hash_message_jazz(mhash, r, root, idx, m, MESSAGE_SIZE);
    *after = cpucycles();
}

void bench_hash_message_ref(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    unsigned long long idx = (unsigned long long)random_valid_idx(&p);
    uint8_t mhash[p.n];
    uint8_t r[p.n];
    uint8_t root[p.n];
    uint8_t m[MESSAGE_SIZE];

    *before = cpucycles();
    hash_message(&p, mhash, r, root, idx, m, MESSAGE_SIZE);
    *after = cpucycles();
}

void bench_thash_h_jasmin(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    uint8_t out[p.n];
    uint32_t addr[8];
    uint8_t in[2 * p.n];
    uint8_t pub_seed[p.n];

    *before = cpucycles();
    thash_h_jazz(out, addr, in, pub_seed);
    *after = cpucycles();
}

void bench_thash_h_ref(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    uint8_t out[p.n];
    uint32_t addr[8];
    uint8_t in[2 * p.n];
    uint8_t pub_seed[p.n];

    *before = cpucycles();
    thash_h(&p, out, in, pub_seed, addr);
    *after = cpucycles();
}

void bench_thash_f_jasmin(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    uint8_t out[p.n];
    uint32_t addr[8];
    uint8_t pub_seed[p.n];

    *before = cpucycles();
    thash_f_jazz(out, addr, pub_seed);
    *after = cpucycles();
}

void bench_thash_f_c(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    uint8_t out[p.n];
    uint32_t addr[8];
    uint8_t pub_seed[p.n];

    *before = cpucycles();
    thash_f(&p, out, out, pub_seed,
            addr); /* the out and in arguments always point to the same memory */
    *after = cpucycles();
}

int main(void) {
    clearfile(xstr(FILENAME));
    print_header(xstr(FILENAME));

    bench_function(bench_prf_jasmin, "prf_jasmin");
    bench_function(bench_prf_c, "prf_ref");

    bench_function(bench_prf_keygen_jasmin, "prf_keygen_jasmin");
    bench_function(bench_prf_keygen_ref, "prf_keygen_ref");

    bench_function(bench_hash_message_jasmin, "hash_message_jasmin");
    bench_function(bench_hash_message_ref, "hash_message_ref");

    bench_function(bench_thash_h_jasmin, "thash_h_jasmin");
    bench_function(bench_thash_h_ref, "thash_h_ref");

    bench_function(bench_thash_f_jasmin, "thash_f_jasmin");
    bench_function(bench_thash_f_c, "thash_f_ref");

    return EXIT_SUCCESS;
}
