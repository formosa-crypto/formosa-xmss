#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#include "alignedcalloc.c"
#include "bench.h"
#include "hash_address.h"
#include "macros.h"
#include "params.h"
#include "randombytes.h"
#include "xmss.h"

#ifndef TIMINGS
#warning "TIMINGS not defined, defaulting to 10000"
#define TIMINGS 10000
#endif

#ifndef IMPL
// clang-format off
#define IMPL XMSSMT-SHA2_20/2_256
// clang-format on
#endif

// XMSS parameters from params-xmssmt-sha2_20_2_256.jinc
#define XMSS_N 32
#define XMSS_TREE_HEIGHT 20

// Jazz implementation - computes only the root
extern void treehash_jazz(
    unsigned char *root,
    const unsigned char *sk_seed,
    const unsigned char *pub_seed,
    uint32_t start_index,
    uint32_t target_height,
    const uint32_t subtree_addr[8]
);

// C reference implementation - computes root and auth_path
extern void treehash(
    const xmss_params *params,
    unsigned char *root,
    unsigned char *auth_path,
    const unsigned char *sk_seed,
    const unsigned char *pub_seed,
    uint32_t leaf_idx,
    const uint32_t subtree_addr[8]
);

bool verbose = true;

static xmss_params init_params() {
    xmss_params params;
    uint32_t oid;

    if (xmssmt_str_to_oid(&oid, xstr(IMPL)) == -1) {
        fprintf(stderr, "Failed to generate oid from impl name\n");
        exit(-1);
    }

    if (xmssmt_parse_oid(&params, oid) == -1) {
        fprintf(stderr, "Failed to generate params from oid\n");
        exit(-1);
    }

    return params;
}

void bench_c(FILE *fp) {
    unsigned long long start_cycles, end_cycles;
    xmss_params params = init_params();

    unsigned char seed[3 * params.n];
    randombytes(seed, 3 * params.n);

    unsigned char *pk_orig, *sk_orig;
    unsigned char *pk = alignedcalloc(&pk_orig, params.pk_bytes);
    unsigned char *sk = alignedcalloc(&sk_orig, params.sk_bytes);

    unsigned char *auth_path = malloc(params.tree_height * params.n);
    uint32_t top_tree_addr[8] = {0};
    set_layer_addr(top_tree_addr, params.d - 1);

    /* Initialize index to 0. */
    memset(sk, 0, params.index_bytes);

    /* Initialize SK_SEED and SK_PRF. */
    memcpy(sk + params.index_bytes, seed, 2 * params.n);

    /* Initialize PUB_SEED. */
    memcpy(sk + params.index_bytes + 3 * params.n, seed + 2 * params.n, params.n);
    memcpy(pk + params.n, sk + params.index_bytes + 3 * params.n, params.n);

    start_cycles = cpucycles();
    treehash(&params, pk, auth_path, sk + params.index_bytes, pk + params.n, 0, top_tree_addr);
    end_cycles = cpucycles();

    if (fp != NULL) {
        fprintf(fp, "%llu\n", end_cycles - start_cycles);
    } else {
        fprintf(stderr, "Failed to open file for treehash cycles\n");
    }

    memcpy(sk + params.index_bytes + 2 * params.n, pk, params.n);

    free(auth_path);
    free(pk_orig);
    free(sk_orig);
}

void bench_jasmin(FILE *fp) {
        unsigned long long start_cycles, end_cycles;
    xmss_params params = init_params();

    unsigned char seed[3 * params.n];
    randombytes(seed, 3 * params.n);

    unsigned char *pk_orig, *sk_orig;
    unsigned char *pk = alignedcalloc(&pk_orig, params.pk_bytes);
    unsigned char *sk = alignedcalloc(&sk_orig, params.sk_bytes);

    unsigned char *auth_path = malloc(params.tree_height * params.n);
    uint32_t top_tree_addr[8] = {0};
    set_layer_addr(top_tree_addr, params.d - 1);

    /* Initialize index to 0. */
    memset(sk, 0, params.index_bytes);

    /* Initialize SK_SEED and SK_PRF. */
    memcpy(sk + params.index_bytes, seed, 2 * params.n);

    /* Initialize PUB_SEED. */
    memcpy(sk + params.index_bytes + 3 * params.n, seed + 2 * params.n, params.n);
    memcpy(pk + params.n, sk + params.index_bytes + 3 * params.n, params.n);

    start_cycles = cpucycles();
    treehash_jazz(pk, sk + params.index_bytes, pk + params.n, 0, XMSS_TREE_HEIGHT, top_tree_addr);
    end_cycles = cpucycles();

    if (fp != NULL) {
        fprintf(fp, "%llu\n", end_cycles - start_cycles);
    } else {
        fprintf(stderr, "Failed to open file for treehash cycles\n");
    }

    memcpy(sk + params.index_bytes + 2 * params.n, pk, params.n);

    free(auth_path);
    free(pk_orig);
    free(sk_orig);
}

int main(void) {
    FILE *fp = fopen("bench_treehash_c.txt", "w");

    if (fp == NULL) {
        fprintf(stderr, "Error opening output file.\n");
        exit(EXIT_FAILURE);
    }

    for (int i = 0; i < TIMINGS; i++) {
        if (verbose) {
            printf("C implementation: Iteration %d/%d\n", i + 1, TIMINGS);
        }
        bench_c(fp);
    }

    fclose(fp);

    FILE *fp_jasmin = fopen("bench_treehash_jasmin.txt", "w");
    if (fp_jasmin == NULL) {
        fprintf(stderr, "Error opening output file.\n");
        exit(EXIT_FAILURE);
    }

    for (int i = 0; i < TIMINGS; i++) {
        if (verbose) {
            printf("Jasmin implementation: Iteration %d/%d\n", i + 1, TIMINGS);
        }
        bench_jasmin(fp_jasmin);
    }

    fclose(fp_jasmin);

    return EXIT_SUCCESS;
}