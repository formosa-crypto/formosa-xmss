#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "alignedcalloc.c"
#include "bench.h"
#include "macros.h"
#include "params.h"
#include "randombytes.h"
#include "xmss.h"

#ifndef TIMINGS
#warning "TIMINGS not defined, defaulting to 1000"
#define TIMINGS 1000
#endif

#ifndef IMPL
// clang-format off
#define IMPL XMSSMT-SHA2_20/2_256
// clang-format on
#endif

// XMSS parameters from params-xmssmt-sha2_20_2_256.jinc
#define XMSS_N 32
#define XMSS_TREE_HEIGHT 20

extern void treehash_jazz(unsigned char *root, unsigned char *auth_path,
                          const unsigned char *sk_seed, const unsigned char *pub_seed,
                          uint32_t leaf_idx, const uint32_t subtree_addr[8]);

extern void treehash(const xmss_params *params, unsigned char *root, unsigned char *auth_path,
                     const unsigned char *sk_seed, const unsigned char *pub_seed, uint32_t leaf_idx,
                     const uint32_t subtree_addr[8]);

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

static uint32_t get_oid() {
    uint32_t oid;

    if (xmssmt_str_to_oid(&oid, xstr(IMPL)) == -1) {
        fprintf(stderr, "Failed to generate oid from impl name\n");
        exit(-1);
    }

    return oid;
}

void bench_treehash_kg(void) {
    // NOTA: Neste caso, em jasmin apenas calculamos a raiz da arvore, porque a
    // funcao treehash_jazz nao calcula o auth_path (na implementacao jasmin)
    // em C, no entanto, calculamos ambos (raiz e auth_path), sendo que apenas a raiz e
    // usada posteriormente => o auth_path e calculado desnecessariamente
    xmss_params params = init_params();
    uint32_t OID = get_oid();

    unsigned char *pk_orig, *sk_orig;
    unsigned char *pk = alignedcalloc(&pk_orig, params.pk_bytes + XMSS_OID_LEN);
    unsigned char *sk = alignedcalloc(&sk_orig, params.sk_bytes + XMSS_OID_LEN);

    for (int i = 0; i < TIMINGS; i++) {
        // the benchmark is done inside the keypair function
        xmssmt_keypair(pk, sk, OID);
    }

    free(pk_orig);
    free(sk_orig);
}

int main(void) {
    xmss_params params = init_params();

    bench_treehash_kg();

    return EXIT_SUCCESS;
}
