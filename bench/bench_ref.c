#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "config.h"
#include "macros.h"
#include "params.h"
#include "xmss.h"

#ifndef IMPL
#error IMPL must be defined
#endif

#ifndef OP
#define OP 3
#endif

#ifndef MESSAGE_SIZE
#define MESSAGE_SIZE 128
#endif

bool verbose = false;

static uint64_t min3(uint64_t a, uint64_t b, uint64_t c) {
    return (a < b ? (a < c ? a : c) : (b < c ? b : c));
}

static uint64_t min3_array(const uint64_t *a) {
    assert(a != NULL);

    return min3(a[0], a[1], a[2]);
}

static int starts_with(const char *str, const char *prefix) {
    return strncmp(str, prefix, strlen(prefix)) == 0;
}

static inline uint64_t cpucycles(void) {
    uint64_t result;

    asm volatile("rdtsc; shlq $32,%%rdx; orq %%rdx,%%rax" : "=a"(result) : : "%rdx");

    return result;
}

static int cmp_uint64(const void *a, const void *b) {
    if (*(uint64_t *)a < *(uint64_t *)b) {
        return -1;
    }
    if (*(uint64_t *)a > *(uint64_t *)b) {
        return 1;
    }
    return 0;
}

static uint64_t median(uint64_t *l, unsigned long long llen) {
    qsort(l, llen, sizeof(uint64_t), cmp_uint64);

    if (llen % 2) {
        return l[llen / 2];
    } else {
        return (l[llen / 2 - 1] + l[llen / 2]) / 2;
    }
}

static uint64_t average(const uint64_t *t, unsigned long long tlen) {
    unsigned long long i;
    uint64_t acc = 0;

    for (i = 0; i < tlen; i++) {
        acc += t[i];
    }

    return acc / tlen;
}

static uint64_t overhead_of_cpucycles_call(void) {
    uint64_t t0, t1, overhead = -1LL;
    unsigned int i;

    for (i = 0; i < 100000; i++) {
        t0 = cpucycles();
        __asm__ volatile("");
        t1 = cpucycles();
        if (t1 - t0 < overhead) {
            overhead = t1 - t0;
        }
    }

    return overhead;
}

void xmssmt_bench_kg(const xmss_params *params, uint32_t oid, uint64_t observations[TIMINGS]) {
    uint8_t pk[XMSS_OID_LEN + params->pk_bytes];
    uint8_t sk[XMSS_OID_LEN + params->sk_bytes];

    uint64_t before, after;

    uint64_t cpucycles_overhead = overhead_of_cpucycles_call();

    for (int i = 0; i + 1 < TIMINGS; i++) {
        if (verbose) {
            printf("[(c-ref) kg]: Timing %d/%d\n", i + 1, TIMINGS - 1);
        }
        before = cpucycles();
        xmssmt_keypair(pk, sk, oid);
        after = cpucycles();
        observations[i] = (after - cpucycles_overhead) - before;
    }
}

void xmssmt_bench_sign(const xmss_params *params, uint32_t oid, uint64_t observations[TIMINGS]) {
    uint8_t pk[XMSS_OID_LEN + params->pk_bytes];
    uint8_t sk[XMSS_OID_LEN + params->sk_bytes];
    uint8_t m[MESSAGE_SIZE];
    uint8_t sm[params->sig_bytes + MESSAGE_SIZE];
    unsigned long long smlen;

    uint64_t before, after;

    uint64_t cpucycles_overhead = overhead_of_cpucycles_call();

    // Generate a valid keypair first
    xmssmt_keypair(pk, sk, oid);

    for (int i = 0; i + 1 < TIMINGS; i++) {
        if (verbose) {
            printf("[(c-ref) sign]: Timing %d/%d\n", i + 1, TIMINGS - 1);
        }
        before = cpucycles();
        xmssmt_sign(sk, sm, &smlen, m, MESSAGE_SIZE);
        after = cpucycles();
        observations[i] = (after - cpucycles_overhead) - before;
    }
}

void xmssmt_bench_verify(const xmss_params *params, uint32_t oid, uint64_t observations[TIMINGS]) {
    uint8_t pk[XMSS_OID_LEN + params->pk_bytes];
    uint8_t sk[XMSS_OID_LEN + params->sk_bytes];
    uint8_t m[MESSAGE_SIZE];
    uint8_t sm[params->sig_bytes + MESSAGE_SIZE];
    unsigned long long smlen = params->sig_bytes + MESSAGE_SIZE;
    unsigned long long mlen;

    uint64_t before, after;

    uint64_t cpucycles_overhead = overhead_of_cpucycles_call();

    // Generate a valid keypair first
    xmssmt_keypair(pk, sk, oid);

    for (int i = 0; i + 1 < TIMINGS; i++) {
        if (verbose) {
            printf("[(c-ref) verify]: Timing %d/%d\n", i + 1, TIMINGS - 1);
        }
        before = cpucycles();
        xmssmt_sign_open(m, &mlen, sm, smlen, pk);
        after = cpucycles();
        observations[i] = (after - cpucycles_overhead) - before;
    }
}

void print_results(uint64_t obs[OP][RUNS][TIMINGS]) {
    uint64_t kg_medians[RUNS];
    uint64_t sign_medians[RUNS];
    uint64_t verify_medians[RUNS];
    char impl_name[1024];

    for (int i = 0; i < RUNS; i++) {
        kg_medians[i] = median(obs[0][i], TIMINGS);
        sign_medians[i] = median(obs[1][i], TIMINGS);
        verify_medians[i] = median(obs[2][i], TIMINGS);
    }

    uint64_t kg_median = min3_array(kg_medians);
    uint64_t sign_median = min3_array(sign_medians);
    uint64_t verify_median = min3_array(verify_medians);

        snprintf(impl_name, sizeof(impl_name), "%s_c_ref", xstr(IMPL));

    printf("%s;%" PRIu64 ";%" PRIu64 ";%" PRIu64 "\n", impl_name, kg_median, sign_median,
           verify_median);
}

int main(void) {
    xmss_params params;
    uint32_t oid;

    if (starts_with(IMPL, "XMSSMT")) {
        if (xmssmt_str_to_oid(&oid, IMPL) == -1) {
            fprintf(stderr, "Failed to generate oid from impl name\n");
            exit(-1);
        }

        if (xmssmt_parse_oid(&params, oid) == -1) {
            fprintf(stderr, "Failed to generate params from oid\n");
            exit(-1);
        }
    } else {
        fprintf(stderr, "multi tree only \n");
        return EXIT_FAILURE;
    }

    // observations[0] : for keygen
    // observations[1] : for signing
    // observations[2] : for verfication
    uint64_t observations[OP][RUNS][TIMINGS] = {0};

    for (int i = 0; i < RUNS; i++) {
        if (verbose) {
            printf("================= Run %d =================\n", i);
        }

        xmssmt_bench_kg(&params, oid,  observations[0][i]);
        xmssmt_bench_sign(&params, oid, observations[1][i]);
        xmssmt_bench_verify(&params, oid, observations[2][i]);
    }

    print_results(observations);

    return EXIT_SUCCESS;
}
