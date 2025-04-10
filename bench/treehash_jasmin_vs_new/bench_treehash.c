#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "bench_common.h"
#include "config.h"
#include "xmss_core.h"
#include "macros.h"
#include "params.h"

#ifndef IMPL
#error IMPL must be defined
#endif

#ifndef FILENAME
#define FILENAME "results.txt"
#endif

#ifndef MESSAGE_SIZE
#define MESSAGE_SIZE 128
#endif

extern void treehash_jazz(uint8_t *root, const uint8_t *sk_seed, const uint8_t *pub_seed,
                          uint32_t start, uint32_t target_height, const uint32_t *subtree_addr);

extern void build_auth_path_jazz(uint8_t *auth_path, const uint8_t *sk_seed,
                                 const uint8_t *pub_seed, uint32_t i, const uint32_t *addr);

extern void treesig_jazz(uint8_t *sig, uint32_t *addr, const uint8_t *M, const uint8_t *sk,
                         uint32_t idx_sig);

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
    if (!(f = fopen(FILENAME, "a"))) {
        fprintf(stderr, "Failed to open %s for writing\n", FILENAME);
        exit(EXIT_FAILURE);
    }

    assert(f != NULL);

    fprintf(f, "%s;%" PRIu64 ";%" PRIu64 "\n", s, average_val, median_val);
    fclose(f);
}

static uint32_t *setup_start_and_target_height(const xmss_params *p) {
    assert(p != NULL);

    // sets up start and target height such that 0 < start < target < p->tree_height
    
    srand((unsigned int)42);

    uint32_t *r = (uint32_t *)malloc(2 * sizeof(uint32_t));

    uint32_t target_height =
        (rand() % (p->tree_height - 1)) + 1;  // Ensures target_height > 0 and < TREE_HEIGHT

    // Generate start in range [1, target_height - 1]
    uint32_t start = rand() % (target_height - 1);  // Ensures start > 0 and < target_height

    r[0] = start;
    r[1] = target_height;

    return r;
}

void bench_treehash_jasmin(uint64_t *before, uint64_t *after) {
    xmss_params p = setup_params();
    uint32_t *heights = setup_start_and_target_height(&p);

    uint8_t root[p.n];
    uint8_t sk_seed[p.n];
    uint8_t pub_seed[p.n];
    uint32_t start = heights[0];
    uint32_t target_height = heights[1];
    uint32_t subtree_addr[8];

    *before = cpucycles();
    treehash_jazz(root, sk_seed, pub_seed, start, target_height, subtree_addr);
    *after = cpucycles();

    free(heights);
}

int main(void) {
    clearfile(FILENAME);
    print_header(FILENAME);

    bench_function(bench_treehash_jasmin, "treehash jasmin");

    return EXIT_SUCCESS;
}
