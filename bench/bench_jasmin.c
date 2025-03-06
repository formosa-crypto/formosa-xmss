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

bool verbose = true;

extern int xmssmt_keypair_jazz(uint8_t *pk, uint8_t *sk);
extern int xmssmt_sign_jazz(uint8_t *sk, uint8_t *sm, size_t *smlen, const uint8_t *m, size_t mlen);
extern int xmssmt_sign_open_jazz(uint8_t *m, size_t *mlen, const uint8_t *sm, size_t smlen,
                                 const uint8_t *pk);

static uint64_t min3(uint64_t a, uint64_t b, uint64_t c) {
    return (a < b ? (a < c ? a : c) : (b < c ? b : c));
}

static uint64_t min3_array(const uint64_t *a) {
    assert(a != NULL);

    return min3(a[0], a[1], a[2]);
}

static int starts_with(const char *str, const char *pjasminix) {
    return strncmp(str, pjasminix, strlen(pjasminix)) == 0;
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

static uint64_t median(uint64_t *l, size_t llen) {
    qsort(l, llen, sizeof(uint64_t), cmp_uint64);

    if (llen % 2) {
        return l[llen / 2];
    } else {
        return (l[llen / 2 - 1] + l[llen / 2]) / 2;
    }
}

static uint64_t average(const uint64_t *t, size_t tlen) {
    size_t i;
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
    assert(params != NULL);

    uint8_t pk[XMSS_OID_LEN + params->pk_bytes];
    uint8_t sk[XMSS_OID_LEN + params->sk_bytes];

    uint64_t before, after;

    uint64_t cpucycles_overhead = overhead_of_cpucycles_call();

    for (int i = 0; i + 1 < TIMINGS; i++) {
        if (verbose) {
            printf("[(jasmin) kg]: Timing %d/%d\n", i + 1, TIMINGS);
        }
        before = cpucycles();
        xmssmt_keypair(pk, sk, oid);
        after = cpucycles();
        observations[i] = (after - cpucycles_overhead) - before;
    }
}

int main(void) {
    xmss_params params;
    uint32_t oid;

    uint64_t observations[OP][RUNS][TIMINGS] = {0};

    if (starts_with(IMPL, "XMSSMT")) {
        if (xmssmt_str_to_oid(&oid, IMPL) == -1) {
            fprintf(stderr, "Failed to generate oid from impl name\n");
            exit(-1);
        }

        if (xmssmt_parse_oid(&params, oid) == -1) {
            fprintf(stderr, "Failed to generate params from oid\n");
            exit(-1);
        }

        for (int i = 0; i < RUNS; i++) {
            if (verbose) {
                printf("Run %d\n", i);
            }
            xmssmt_bench_kg(&params, oid, observations[0][i]);
            // xmssmt_bench_sign(&params, oid, observations[1][i]);
            // xmssmt_bench_verify(&params, oid, observations[2][i]);
        }

        char *labels[OP] = {"kg", "sign", "verify"};
        print_results(labels, observations);
    } else {
        // Benchmarks not implemented for single tree variant
        // TODO: DO this later
    }

    return EXIT_SUCCESS;
}
