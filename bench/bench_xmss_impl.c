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
#include "xmss_core.h"

#ifndef TIMINGS
#warning "TIMINGS not defined, defaulting to 10000"
#define TIMINGS 10000
#endif

#ifndef IMPL
// clang-format off
#define IMPL XMSSMT-SHA2_20/2_256
// clang-format on
#endif

#ifndef MSG_LEN
#warning "MSG_LEN not defined, defaulting to 32"
#define MSG_LEN 32
#endif

#define XMSS_OID_LEN 4

#ifdef BENCH_JASMIN
extern int xmssmt_keypair_jazz(unsigned char *pk, unsigned char *sk);
extern int xmssmt_sign_jazz(unsigned char *sk, unsigned char *sm, unsigned long long *smlen,
                            const unsigned char *m, unsigned long long mlen);
extern int xmssmt_sign_open_jazz(unsigned char *m, unsigned long long *mlen,
                                 const unsigned char *sm, unsigned long long smlen,
                                 const unsigned char *pk);
#endif

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

void bench_keygen(const xmss_params *params) {
    uint32_t OID = get_oid();

    unsigned char *pk_orig, *sk_orig;
    unsigned char *pk = alignedcalloc(&pk_orig, params->pk_bytes + XMSS_OID_LEN);
    unsigned char *sk = alignedcalloc(&sk_orig, params->sk_bytes + XMSS_OID_LEN);

#ifdef BENCH_C
    BENCHMARK_N_TIMES(TIMINGS, "results/bench_keygen_c.txt", xmssmt_keypair(pk, sk, OID));
#else
#ifdef BENCH_JASMIN
    #ifdef ZERO_LOOP
        BENCHMARK_N_TIMES(TIMINGS, "results/bench_keygen_jasmin_zero_loop.txt", xmssmt_keypair_jazz(pk, sk));
    #else
        #ifdef ZERO_UNROLL
            BENCHMARK_N_TIMES(TIMINGS, "results/bench_keygen_jasmin_zero_unroll.txt", xmssmt_keypair_jazz(pk, sk));
        #else 
            BENCHMARK_N_TIMES(TIMINGS, "results/bench_keygen_jasmin.txt", xmssmt_keypair_jazz(pk, sk));
        #endif
    #endif 
#else
#error "Either BENCH_JASMIN or BENCH_C must be defined"
#endif
#endif

    free(pk_orig);
    free(sk_orig);
}

void bench_sign(const xmss_params *params) {
    uint32_t OID = get_oid();

    unsigned char *pk_orig, *sk_orig, *m_orig, *sm_orig;
    unsigned char *pk = alignedcalloc(&pk_orig, params->pk_bytes + XMSS_OID_LEN);
    unsigned char *sk = alignedcalloc(&sk_orig, params->sk_bytes + XMSS_OID_LEN);
    unsigned char *m = alignedcalloc(&m_orig, MSG_LEN);
    unsigned long long mlen = MSG_LEN;
    unsigned char *sm = alignedcalloc(&sm_orig, params->sig_bytes + mlen);
    unsigned long long smlen;

    // Generate key pair first (not measured)
    xmssmt_keypair(pk, sk, OID);

    // Generate random message
    randombytes(m, mlen);

#ifdef BENCH_C
    BENCHMARK_N_TIMES(TIMINGS, "results/bench_sign_c.txt", xmssmt_sign(sk, sm, &smlen, m, mlen));
#else
#ifdef BENCH_JASMIN
    #ifdef ZERO_LOOP
        BENCHMARK_N_TIMES(TIMINGS, "results/bench_sign_jasmin_zero_loop.txt",
                          xmssmt_sign_jazz(sk, sm, &smlen, m, mlen));
    #else
        #ifdef ZERO_UNROLL
            BENCHMARK_N_TIMES(TIMINGS, "results/bench_sign_jasmin_zero_unroll.txt",
                              xmssmt_sign_jazz(sk, sm, &smlen, m, mlen));
        #else
            BENCHMARK_N_TIMES(TIMINGS, "results/bench_sign_jasmin.txt",
                              xmssmt_sign_jazz(sk, sm, &smlen, m, mlen));
        #endif
    #endif
#else
#error "Either BENCH_JASMIN or BENCH_C must be defined"
#endif
#endif

    free(pk_orig);
    free(sk_orig);
    free(m_orig);
    free(sm_orig);
}

void bench_verify(const xmss_params *params) {
    uint32_t OID = get_oid();

    unsigned char *pk_orig, *sk_orig, *m_orig, *sm_orig, *mout_orig;
    unsigned char *pk = alignedcalloc(&pk_orig, params->pk_bytes + XMSS_OID_LEN);
    unsigned char *sk = alignedcalloc(&sk_orig, params->sk_bytes + XMSS_OID_LEN);
    unsigned char *m = alignedcalloc(&m_orig, MSG_LEN);
    unsigned long long mlen = MSG_LEN;
    unsigned char *sm = alignedcalloc(&sm_orig, params->sig_bytes + mlen);
    unsigned long long smlen;
    unsigned char *mout = alignedcalloc(&mout_orig, mlen);
    unsigned long long mout_len;

    // Generate key pair and sign (not measured)
    xmssmt_keypair(pk, sk, OID);
    randombytes(m, mlen);
    xmssmt_sign(sk, sm, &smlen, m, mlen);

#ifdef BENCH_C
    BENCHMARK_N_TIMES(TIMINGS, "results/bench_verify_c.txt",
                      xmssmt_sign_open(mout, &mout_len, sm, smlen, pk));
#else
#ifdef BENCH_JASMIN
    #ifdef ZERO_LOOP
        BENCHMARK_N_TIMES(TIMINGS, "results/bench_verify_jasmin_zero_loop.txt",
                          xmssmt_sign_open_jazz(mout, &mout_len, sm, smlen, pk));
    #else
        #ifdef ZERO_UNROLL
            BENCHMARK_N_TIMES(TIMINGS, "results/bench_verify_jasmin_zero_unroll.txt",
                              xmssmt_sign_open_jazz(mout, &mout_len, sm, smlen, pk));
        #else
            BENCHMARK_N_TIMES(TIMINGS, "results/bench_verify_jasmin.txt",
                              xmssmt_sign_open_jazz(mout, &mout_len, sm, smlen, pk));
        #endif
    #endif
#else
#error "Either BENCH_JASMIN or BENCH_C must be defined"
#endif

#endif

    free(pk_orig);
    free(sk_orig);
    free(m_orig);
    free(sm_orig);
    free(mout_orig);
}

int main(void) {
    xmss_params params = init_params();

#ifdef BENCH_JASMIN
    const char *impl_name = "JASMIN";
#else
#ifdef BENCH_C
    const char *impl_name = "C";
#else
#error "Either BENCH_JASMIN or BENCH_C must be defined"
#endif
#endif

    printf("Benchmarking %s implementation\n", impl_name);
    printf("Running %d iterations per operation...\n\n", TIMINGS);

    printf("Benchmarking key generation...\n");
    bench_keygen(&params);

    printf("Benchmarking signing...\n");
    bench_sign(&params);

    printf("Benchmarking verification...\n");
    bench_verify(&params);

    printf("\nAll benchmarks completed!\n");

    return EXIT_SUCCESS;
}
