#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "alignedcalloc.c"
#include "bench.h"
#include "macros.h"
#include "params.h"
#include "randombytes.h"

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
#define XMSS_WOTS_LEN 67
#define XMSS_WOTS_LEN1 64
#define XMSS_WOTS_LEN2 3

extern void expand_seed_jazz(uint8_t outseeds[XMSS_WOTS_LEN * XMSS_N], uint32_t addr[8],
                             const uint8_t inseed[XMSS_N], const uint8_t pub_seed[XMSS_N]);

extern void wots_checksum_jazz(uint32_t csum_base_w[XMSS_WOTS_LEN2],
                               const uint32_t msg_base_w[XMSS_WOTS_LEN1]);

extern void gen_chain_inplace_jazz(uint8_t out[XMSS_N], uint32_t addr[8], uint32_t start,
                                   uint32_t steps, const uint8_t pub_seed[XMSS_N]);

extern void gen_chain_jazz(uint8_t out[XMSS_N], uint32_t addr[8], uint8_t *in_ptr, uint32_t start,
                           uint32_t steps, const uint8_t pub_seed[XMSS_N]);

extern void wots_pkgen_jazz(uint8_t pk[XMSS_WOTS_LEN * XMSS_N], uint32_t addr[8],
                            const uint8_t seed[XMSS_N], const uint8_t pub_seed[XMSS_N]);

extern void wots_sign_jazz(uint8_t sig[XMSS_WOTS_LEN * XMSS_N], uint32_t addr[8],
                           const uint8_t msg[XMSS_N], const uint8_t seed[XMSS_N],
                           const uint8_t pub_seed[XMSS_N]);

extern void wots_pk_from_sig_jazz(uint8_t pk[XMSS_WOTS_LEN * XMSS_N], uint32_t addr[8],
                                  uint8_t *sig_ptr, const uint8_t msg[XMSS_N],
                                  const uint8_t pub_seed[XMSS_N]);

// C reference implementations - need params struct

extern void expand_seed(const xmss_params *params, unsigned char *outseeds,
                        const unsigned char *inseed, const unsigned char *pub_seed,
                        uint32_t addr[8]);

extern void wots_checksum(const xmss_params *params, int *csum_base_w, const int *msg_base_w);

extern void gen_chain(const xmss_params *params, unsigned char *out, const unsigned char *in,
                      unsigned int start, unsigned int steps, const unsigned char *pub_seed,
                      uint32_t addr[8]);

extern void wots_pkgen(const xmss_params *params, unsigned char *pk, const unsigned char *seed,
                       const unsigned char *pub_seed, uint32_t addr[8]);

extern void wots_sign(const xmss_params *params, unsigned char *sig, const unsigned char *msg,
                      const unsigned char *seed, const unsigned char *pub_seed, uint32_t addr[8]);

extern void wots_pk_from_sig(const xmss_params *params, unsigned char *pk, const unsigned char *sig,
                             const unsigned char *msg, const unsigned char *pub_seed,
                             uint32_t addr[8]);

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

void bench_expand_seed(xmss_params *params) {
    if (params == NULL) {
        perror("params is NULL");
    }

    uint8_t *outseeds_jazz_orig, *outseeds_c_orig;
    uint8_t *inseed_orig, *pub_seed_orig;

    uint8_t *outseeds_jazz = alignedcalloc(&outseeds_jazz_orig, XMSS_WOTS_LEN * XMSS_N);
    uint8_t *outseeds_c = alignedcalloc(&outseeds_c_orig, XMSS_WOTS_LEN * XMSS_N);
    uint8_t *inseed = alignedcalloc(&inseed_orig, XMSS_N);
    uint8_t *pub_seed = alignedcalloc(&pub_seed_orig, XMSS_N);
    uint32_t addr[8] = {0};

    randombytes(inseed, XMSS_N);
    randombytes(pub_seed, XMSS_N);

    BENCHMARK_N_TIMES(TIMINGS, "results/expand_seed_jazz.txt",
                      expand_seed_jazz(outseeds_jazz, addr, inseed, pub_seed));

    BENCHMARK_N_TIMES(TIMINGS, "results/expand_seed_c.txt",
                      expand_seed(params, outseeds_c, inseed, pub_seed, addr));

    free(outseeds_jazz_orig);
    free(outseeds_c_orig);
    free(inseed_orig);
    free(pub_seed_orig);
}

void bench_wots_checksum(xmss_params *params) {
    if (params == NULL) {
        perror("params is NULL");
    }

    uint32_t csum_base_w_jazz[XMSS_WOTS_LEN2] = {0};
    int csum_base_w_c[XMSS_WOTS_LEN2] = {0};
    uint32_t msg_base_w_jazz[XMSS_WOTS_LEN1] = {0};
    int msg_base_w_c[XMSS_WOTS_LEN1] = {0};

    // Initialize with random test data
    randombytes((uint8_t *)msg_base_w_jazz, XMSS_WOTS_LEN1 * sizeof(uint32_t));
    randombytes((uint8_t *)msg_base_w_c, XMSS_WOTS_LEN1 * sizeof(int));

    BENCHMARK_N_TIMES(TIMINGS, "results/wots_checksum_jazz.txt",
                      wots_checksum_jazz(csum_base_w_jazz, msg_base_w_jazz));

    BENCHMARK_N_TIMES(TIMINGS, "results/wots_checksum_c.txt",
                      wots_checksum(params, csum_base_w_c, msg_base_w_c));
}

void bench_gen_chain(xmss_params *params) {
    if (params == NULL) {
        perror("params is NULL");
    }

    uint8_t *out_jazz_orig, *out_c_orig, *in_orig, *pub_seed_orig;

    uint8_t *out_jazz = alignedcalloc(&out_jazz_orig, XMSS_N);
    uint8_t *out_c = alignedcalloc(&out_c_orig, XMSS_N);
    uint8_t *in = alignedcalloc(&in_orig, XMSS_N);
    uint8_t *pub_seed = alignedcalloc(&pub_seed_orig, XMSS_N);
    uint32_t addr[8] = {0};
    uint32_t start = 0;
    uint32_t steps = 15;

    randombytes(in, XMSS_N);
    randombytes(pub_seed, XMSS_N);
    memcpy(out_jazz, in, XMSS_N);

    BENCHMARK_N_TIMES(TIMINGS, "results/gen_chain_jazz.txt",
                      gen_chain_jazz(out_jazz, addr, in, start, steps, pub_seed));

    BENCHMARK_N_TIMES(TIMINGS, "results/gen_chain_c.txt",
                      gen_chain(params, out_c, in, start, steps, pub_seed, addr));

    free(out_jazz_orig);
    free(out_c_orig);
    free(in_orig);
    free(pub_seed_orig);
}

void bench_wots_pkgen(xmss_params *params) {
    if (params == NULL) {
        perror("params is NULL");
    }

    uint8_t *pk_jazz_orig, *pk_c_orig, *seed_orig, *pub_seed_orig;

    uint8_t *pk_jazz = alignedcalloc(&pk_jazz_orig, XMSS_WOTS_LEN * XMSS_N);
    uint8_t *pk_c = alignedcalloc(&pk_c_orig, XMSS_WOTS_LEN * XMSS_N);
    uint8_t *seed = alignedcalloc(&seed_orig, XMSS_N);
    uint8_t *pub_seed = alignedcalloc(&pub_seed_orig, XMSS_N);
    uint32_t addr[8] = {0};

    randombytes(seed, XMSS_N);
    randombytes(pub_seed, XMSS_N);

    BENCHMARK_N_TIMES(TIMINGS, "results/wots_pkgen_jazz.txt",
                      wots_pkgen_jazz(pk_jazz, addr, seed, pub_seed));

    BENCHMARK_N_TIMES(TIMINGS, "results/wots_pkgen_c.txt",
                      wots_pkgen(params, pk_c, seed, pub_seed, addr));

    free(pk_jazz_orig);
    free(pk_c_orig);
    free(seed_orig);
    free(pub_seed_orig);
}

void bench_wots_sign(xmss_params *params) {
    if (params == NULL) {
        perror("params is NULL");
    }

    uint8_t *sig_jazz_orig, *sig_c_orig, *msg_orig, *seed_orig, *pub_seed_orig;

    uint8_t *sig_jazz = alignedcalloc(&sig_jazz_orig, XMSS_WOTS_LEN * XMSS_N);
    uint8_t *sig_c = alignedcalloc(&sig_c_orig, XMSS_WOTS_LEN * XMSS_N);
    uint8_t *msg = alignedcalloc(&msg_orig, XMSS_N);
    uint8_t *seed = alignedcalloc(&seed_orig, XMSS_N);
    uint8_t *pub_seed = alignedcalloc(&pub_seed_orig, XMSS_N);
    uint32_t addr[8] = {0};

    randombytes(msg, XMSS_N);
    randombytes(seed, XMSS_N);
    randombytes(pub_seed, XMSS_N);

    BENCHMARK_N_TIMES(TIMINGS, "results/wots_sign_jazz.txt",
                      wots_sign_jazz(sig_jazz, addr, msg, seed, pub_seed));

    BENCHMARK_N_TIMES(TIMINGS, "results/wots_sign_c.txt",
                      wots_sign(params, sig_c, msg, seed, pub_seed, addr));

    free(sig_jazz_orig);
    free(sig_c_orig);
    free(msg_orig);
    free(seed_orig);
    free(pub_seed_orig);
}

void bench_wots_pk_from_sig(xmss_params *params) {
    if (params == NULL) {
        perror("params is NULL");
    }

    uint8_t *pk_jazz_orig, *pk_c_orig, *sig_orig, *msg_orig, *pub_seed_orig;

    uint8_t *pk_jazz = alignedcalloc(&pk_jazz_orig, XMSS_WOTS_LEN * XMSS_N);
    uint8_t *pk_c = alignedcalloc(&pk_c_orig, XMSS_WOTS_LEN * XMSS_N);
    uint8_t *sig = alignedcalloc(&sig_orig, XMSS_WOTS_LEN * XMSS_N);
    uint8_t *msg = alignedcalloc(&msg_orig, XMSS_N);
    uint8_t *pub_seed = alignedcalloc(&pub_seed_orig, XMSS_N);
    uint32_t addr[8] = {0};

    randombytes(sig, XMSS_WOTS_LEN * XMSS_N);
    randombytes(msg, XMSS_N);
    randombytes(pub_seed, XMSS_N);

    BENCHMARK_N_TIMES(TIMINGS, "results/wots_pk_from_sig_jazz.txt",
                      wots_pk_from_sig_jazz(pk_jazz, addr, sig, msg, pub_seed));

    BENCHMARK_N_TIMES(TIMINGS, "results/wots_pk_from_sig_c.txt",
                      wots_pk_from_sig(params, pk_c, sig, msg, pub_seed, addr));

    free(pk_jazz_orig);
    free(pk_c_orig);
    free(sig_orig);
    free(msg_orig);
    free(pub_seed_orig);
}

int main(void) {
    assert(XMSS_WOTS_LEN == XMSS_WOTS_LEN1 + XMSS_WOTS_LEN2);

    xmss_params params = init_params();

    bench_expand_seed(&params);
    bench_wots_checksum(&params);
    bench_gen_chain(&params);
    bench_wots_pkgen(&params);
    bench_wots_sign(&params);
    bench_wots_pk_from_sig(&params);

    return EXIT_SUCCESS;
}
