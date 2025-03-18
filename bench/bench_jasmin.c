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

static uint64_t min_array(const uint64_t *a, size_t len) {
    uint64_t min = a[0];
    for (size_t i = 1; i < len; i++) {
        if (a[i] < min) {
            min = a[i];
        }
    }
    return min;
}

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

void xmssmt_bench_kg(const xmss_params *params, uint64_t observations[TIMINGS]) {
    uint8_t pk[XMSS_OID_LEN + params->pk_bytes];
    uint8_t sk[XMSS_OID_LEN + params->sk_bytes];

    uint64_t before, after;

    uint64_t cpucycles_overhead = overhead_of_cpucycles_call();

    for (int i = 0; i + 1 < TIMINGS; i++) {
        if (verbose) {
            printf("[(jasmin) kg]: Timing %d/%d\n", i + 1, TIMINGS - 1);
        }
        before = cpucycles();
        xmssmt_keypair_jazz(pk, sk);
        after = cpucycles();
        observations[i] = (after - cpucycles_overhead) - before;
    }
}

void xmssmt_bench_sign(const xmss_params *params, uint64_t observations[TIMINGS]) {
    uint8_t pk[XMSS_OID_LEN + params->pk_bytes];
    uint8_t sk[XMSS_OID_LEN + params->sk_bytes];
    uint8_t m[MESSAGE_SIZE];
    uint8_t sm[params->sig_bytes + MESSAGE_SIZE];
    size_t smlen;

    uint64_t before, after;

    uint64_t cpucycles_overhead = overhead_of_cpucycles_call();

    // Generate a valid keypair first
    xmssmt_keypair_jazz(pk, sk);

    for (int i = 0; i + 1 < TIMINGS; i++) {
        if (verbose) {
            printf("[(jasmin) sign]: Timing %d/%d\n", i + 1, TIMINGS - 1);
        }
        before = cpucycles();
        xmssmt_sign_jazz(sk, sm, &smlen, m, MESSAGE_SIZE);
        after = cpucycles();
        observations[i] = (after - cpucycles_overhead) - before;
    }
}

void xmssmt_bench_verify(const xmss_params *params, uint64_t observations[TIMINGS]) {
    uint8_t pk[XMSS_OID_LEN + params->pk_bytes];
    uint8_t sk[XMSS_OID_LEN + params->sk_bytes];
    uint8_t m[MESSAGE_SIZE];
    uint8_t sm[params->sig_bytes + MESSAGE_SIZE];
    size_t smlen = params->sig_bytes + MESSAGE_SIZE;
    size_t mlen;

    uint64_t before, after;

    uint64_t cpucycles_overhead = overhead_of_cpucycles_call();

    // Generate a valid keypair first
    xmssmt_keypair_jazz(pk, sk);

    for (int i = 0; i + 1 < TIMINGS; i++) {
        if (verbose) {
            printf("[(jasmin) verify]: Timing %d/%d\n", i + 1, TIMINGS - 1);
        }
        before = cpucycles();
        xmssmt_sign_open_jazz(m, &mlen, sm, smlen, pk);
        after = cpucycles();
        observations[i] = (after - cpucycles_overhead) - before;
    }
}

void print_results(uint64_t obs[OP][RUNS][TIMINGS]) {
    uint64_t kg_medians[RUNS];
    uint64_t sign_medians[RUNS];
    uint64_t verify_medians[RUNS];

    uint64_t kg_median;
    uint64_t sign_median;
    uint64_t verify_median;

    char impl_name[1024];

    for (int i = 0; i < RUNS; i++) {
        kg_medians[i] = median(obs[0][i], TIMINGS);
        sign_medians[i] = median(obs[1][i], TIMINGS);
        verify_medians[i] = median(obs[2][i], TIMINGS);
    }

    if (RUNS == 3) {
        kg_median = min3_array(kg_medians);
        sign_median = min3_array(sign_medians);
        verify_median = min3_array(verify_medians);
    } else {
        kg_median = min_array(kg_medians, RUNS);
        sign_median = min_array(sign_medians, RUNS);
        verify_median = min_array(verify_medians, RUNS);
    }

#ifdef STACK_ZERO
#ifdef STACK_ZERO_SIZE
    snprintf(impl_name, sizeof(impl_name), "%s_%s_%s", xstr(IMPL), xstr(STACK_ZERO),
             xstr(STACK_ZERO_SIZE));
#else
#error STACK_ZERO_SIZE must be defined when STACK_ZERO is defined
#endif
#else
    snprintf(impl_name, sizeof(impl_name), "%s", xstr(IMPL));
    strcat(impl_name, "_jasmin_ref_no_zeroization");
#endif

    if (verbose) {
        // In this case we print to the file results.txt
        FILE *f = fopen("results.txt", "a");
        if (f == NULL) {
            fprintf(stderr, "Failed to open results.txt for writing\n");
            exit(EXIT_FAILURE);
        }

        printf("Debug: impl_name = %s\n", impl_name);
        fprintf(f, "%s;%" PRIu64 ";%" PRIu64 ";%" PRIu64 "\n", impl_name, kg_median, sign_median,
                verify_median);
        fclose(f);
    } else {
        printf("%s;%" PRIu64 ";%" PRIu64 ";%" PRIu64 "\n", impl_name, kg_median, sign_median,
               verify_median);
    }
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

        xmssmt_bench_kg(&params, observations[0][i]);
        xmssmt_bench_sign(&params, observations[1][i]);
        xmssmt_bench_verify(&params, observations[2][i]);
    }

    print_results(observations);

    return EXIT_SUCCESS;
}
