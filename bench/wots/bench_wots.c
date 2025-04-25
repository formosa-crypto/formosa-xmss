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
#include "wots.c"

#ifndef IMPL
#define IMPL XMSSMT-SHA2_20/2_256
#endif

#ifndef FILENAME
#define FILENAME "results_no_zeroization.txt"
#endif

#ifndef MESSAGE_SIZE
#define MESSAGE_SIZE 128
#endif

#define MIN(a, b) ((a) < (b) ? (a) : (b))
#define MAX(a, b) ((a) > (b) ? (a) : (b))

extern void expand_seed_jazz(uint8_t *out, uint32_t *addr, const uint8_t *in,
                             const uint8_t *pub_seed);
extern void gen_chain_inplace_jazz(uint8_t *out, uint32_t *addr, uint32_t start, uint32_t steps,
                                   const uint8_t *pub_seed);
extern void wots_pkgen_jazz(uint8_t *pk, uint32_t *addr, const uint8_t *seed,
                            const uint8_t *pub_seed);

extern void wots_sign_jazz(uint8_t *sig, uint32_t *addr, const uint8_t *msg, const uint8_t *seed,
                           const uint8_t *pub_seed);

extern void wots_pk_from_sig_jazz(uint8_t *pk, uint32_t *addr, const uint8_t *sig,
                                  const uint8_t *msg, const uint8_t *pub_seed);

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
    if (!(f = fopen(xstr(FILENAME), "a"))) {
        fprintf(stderr, "Failed to open %s for writing\n", xstr(FILENAME));
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

void bench_expand_seed_jasmin(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    uint8_t out[p.wots_len * p.n];
    uint32_t addr[8];
    uint8_t in[p.n];
    uint8_t pub_seed[p.n];

    *before = cpucycles();
    expand_seed_jazz(out, addr, in, pub_seed);
    *after = cpucycles();
}

void bench_expand_seed_ref(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    uint8_t out[p.wots_len * p.n];
    uint32_t addr[8];
    uint8_t in[p.n];
    uint8_t pub_seed[p.n];

    *before = cpucycles();
    expand_seed(&p, out, in, pub_seed, addr);
    *after = cpucycles();
}

void bench_gen_chain_jasmin(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    uint8_t out[p.n];
    uint32_t addr[8];
    uint32_t t0 = rand() % p.wots_w;
    uint32_t t1 = rand() % (p.wots_w - t0);

    uint32_t start = MIN(t0, t1);
    uint32_t steps = MAX(t0, t1);

    assert(start + steps <= p.wots_w - 1);

    uint8_t pub_seed[p.n];

    *before = cpucycles();
    gen_chain_inplace_jazz(out, addr, start, steps,
                           pub_seed); /* out and in point to the same memory location */
    *after = cpucycles();
}

void bench_gen_chain_ref(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    uint8_t out[p.n];
    uint32_t addr[8];
    uint32_t t0 = rand() % p.wots_w;
    uint32_t t1 = rand() % (p.wots_w - t0);

    uint32_t start = MIN(t0, t1);
    uint32_t steps = MAX(t0, t1);

    assert(start + steps <= p.wots_w - 1);

    uint8_t pub_seed[p.n];

    *before = cpucycles();
    gen_chain(&p, out, out, start, steps, pub_seed,
              addr); /* out and in point to the same memory location */
    *after = cpucycles();
}

void bench_pkgen_jasmin(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    uint8_t pk[p.wots_len * p.n];
    uint32_t addr[8];
    uint8_t seed[p.n];
    uint8_t pub_seed[p.n];

    *before = cpucycles();
    wots_pkgen_jazz(pk, addr, seed, pub_seed);
    *after = cpucycles();
}

void bench_pkgen_ref(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    uint8_t pk[p.wots_len * p.n];
    uint32_t addr[8];
    uint8_t seed[p.n];
    uint8_t pub_seed[p.n];

    *before = cpucycles();
    wots_pkgen(&p, pk, seed, pub_seed, addr);
    *after = cpucycles();
}

void bench_sign_jasmin(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    uint8_t sig[p.wots_len * p.n];
    uint32_t addr[8];
    uint8_t msg[p.n];
    uint8_t seed[p.n];
    uint8_t pub_seed[p.n];

    *before = cpucycles();
    wots_sign_jazz(sig, addr, msg, seed, pub_seed);
    *after = cpucycles();
}

void bench_sign_ref(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    uint8_t sig[p.wots_len * p.n];
    uint32_t addr[8];
    uint8_t msg[p.n];
    uint8_t seed[p.n];
    uint8_t pub_seed[p.n];

    *before = cpucycles();
    wots_sign(&p, sig, msg, seed, pub_seed, addr);
    *after = cpucycles();
}

void bench_pk_from_sig_jasmin(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    uint8_t pk[p.wots_len * p.n];
    uint8_t sig[p.wots_len * p.n];
    uint32_t addr[8];
    uint8_t msg[p.n];
    uint8_t pub_seed[p.n];

    *before = cpucycles();
    wots_pk_from_sig_jazz(pk, addr, sig, msg, pub_seed);
    *after = cpucycles();
}

void bench_pk_from_sig_ref(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();

    uint8_t pk[p.wots_len * p.n];
    uint8_t sig[p.wots_len * p.n];
    uint32_t addr[8];
    uint8_t msg[p.n];
    uint8_t pub_seed[p.n];

    *before = cpucycles();
    wots_pk_from_sig(&p, pk, sig, msg, pub_seed, addr);
    *after = cpucycles();
}

int main(void) {
    clearfile(xstr(FILENAME));
    print_header(xstr(FILENAME));

    bench_function(bench_expand_seed_jasmin, "expand_seed_jasmin");
    bench_function(bench_expand_seed_ref, "expand_seed_ref");

    bench_function(bench_gen_chain_jasmin, "gen_chain_jasmin");
    bench_function(bench_gen_chain_ref, "gen_chain_ref");

    bench_function(bench_pkgen_jasmin, "wots_pkgen_jasmin");
    bench_function(bench_pkgen_ref, "wots_pkgen_ref");

    bench_function(bench_sign_jasmin, "wots_sign_jasmin");
    bench_function(bench_sign_ref, "wots_sign_ref");

    bench_function(bench_pk_from_sig_jasmin, "wots_pk_from_sig_jasmin");
    bench_function(bench_pk_from_sig_ref, "wots_pk_from_sig_ref");

    return EXIT_SUCCESS;
}
