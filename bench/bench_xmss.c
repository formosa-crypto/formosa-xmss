#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "alignedcalloc.c"
#include "bench.h"
#include "hash.h"
#include "macros.h"
#include "params.h"
#include "randombytes.h"
#include "xmss.h"
#include "xmss_core.h"

#ifndef TIMINGS
#warning "TIMINGS not defined, defaulting to 1000"
#define TIMINGS 1000
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

void bench_sha2_calls_during_kg(const xmss_params *params, FILE *fp) {
    if (params == NULL) {
        perror("params is NULL");
        return;
    }

    if (fp == NULL) {
        perror("file pointer is NULL");
        return;
    }

    unsigned char *pk_orig, *sk_orig;
    unsigned char *pk = alignedcalloc(&pk_orig, params->pk_bytes);
    unsigned char *sk = alignedcalloc(&sk_orig, params->sk_bytes);

    reset_core_hash_call_count();
    xmssmt_core_keypair(params, pk, sk);

    fprintf(fp, "%s,%llu\n", "keygen", get_core_hash_cycle_count());

#ifdef BENCH_JASMIN
    printf("[JASMIN] SHA2 calls during key generation: %llu\n", get_core_hash_call_count());
#else
#ifdef BENCH_C
    printf("[C] SHA2 calls during key generation: %llu\n", get_core_hash_call_count());
#else
#error "Either BENCH_JASMIN or BENCH_C must be defined"
#endif
#endif

    free(pk_orig);
    free(sk_orig);
}

void bench_sha2_calls_during_sign(const xmss_params *params, FILE *fp) {
    if (params == NULL) {
        perror("params is NULL");
        return;
    }

    if (fp == NULL) {
        perror("file pointer is NULL");
        return;
    }

    unsigned char *pk_orig, *sk_orig, *m_orig, *sm_orig;
    unsigned char *pk = alignedcalloc(&pk_orig, params->pk_bytes);
    unsigned char *sk = alignedcalloc(&sk_orig, params->sk_bytes);
    unsigned char *m = alignedcalloc(&m_orig, MSG_LEN);
    unsigned long long mlen = MSG_LEN;
    unsigned char *sm = alignedcalloc(&sm_orig, params->sig_bytes + mlen);
    unsigned long long smlen;

    // Generate key pair first
    xmssmt_core_keypair(params, pk, sk);

    // Generate random message
    randombytes(m, mlen);

    reset_core_hash_call_count();
    xmssmt_core_sign(params, sk, sm, &smlen, m, mlen);

    fprintf(fp, "%s,%llu\n", "sign", get_core_hash_cycle_count());

#ifdef BENCH_JASMIN
    printf("[JASMIN] SHA2 calls during signing: %llu\n", get_core_hash_call_count());
#else
#ifdef BENCH_C
    printf("[C] SHA2 calls during signing: %llu\n", get_core_hash_call_count());
#else
#error "Either BENCH_JASMIN or BENCH_C must be defined"
#endif
#endif

    free(pk_orig);
    free(sk_orig);
    free(m_orig);
    free(sm_orig);
}

void bench_sha2_calls_during_verify(const xmss_params *params, FILE *fp) {
    if (params == NULL) {
        perror("params is NULL");
        return;
    }

    if (fp == NULL) {
        perror("file pointer is NULL");
        return;
    }

    unsigned char *pk_orig, *sk_orig, *m_orig, *sm_orig, *mout_orig;
    unsigned char *pk = alignedcalloc(&pk_orig, params->pk_bytes);
    unsigned char *sk = alignedcalloc(&sk_orig, params->sk_bytes);
    unsigned char *m = alignedcalloc(&m_orig, 32);
    unsigned long long mlen = 32;
    unsigned char *sm = alignedcalloc(&sm_orig, params->sig_bytes + mlen);
    unsigned long long smlen;
    unsigned char *mout = alignedcalloc(&mout_orig, mlen);
    unsigned long long mout_len;

    // Generate key pair
    xmssmt_core_keypair(params, pk, sk);

    // Generate random message and sign it
    randombytes(m, mlen);
    xmssmt_core_sign(params, sk, sm, &smlen, m, mlen);

    reset_core_hash_call_count();
    xmssmt_core_sign_open(params, mout, &mout_len, sm, smlen, pk);

    fprintf(fp, "%s,%llu\n", "verify", get_core_hash_cycle_count());

#ifdef BENCH_JASMIN
    printf("[JASMIN] SHA2 calls during verify: %llu\n", get_core_hash_call_count());
#else
#ifdef BENCH_C
    printf("[C] SHA2 calls during verify: %llu\n", get_core_hash_call_count());
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
    FILE *fp = fopen("results/bench_xmss_sha2_calls_jasmin.csv", "w");
#else
#ifdef BENCH_C
    FILE *fp = fopen("results/bench_xmss_sha2_calls_c.csv", "w");
#else
#error "Either BENCH_JASMIN or BENCH_C must be defined"
#endif
#endif

    if (fp == NULL) {
        perror("Failed to open bench_keygen.csv");
        return EXIT_FAILURE;
    }

    fprintf(fp, "function,cycles\n");

    for (int i = 0; i < TIMINGS; i++) {
        bench_sha2_calls_during_kg(&params, fp);
        bench_sha2_calls_during_sign(&params, fp);
        bench_sha2_calls_during_verify(&params, fp);
    }

    fclose(fp);

    return EXIT_SUCCESS;
}
