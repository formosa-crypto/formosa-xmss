#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "params.h"
#include "xmss.h"

#define str(s) #s
#define xstr(s) str(s)

#ifndef MAXBUFSIZE
#define MAXBUFSIZE 1024
#endif

#ifndef DATA_POINTS
#define DATA_POINTS 10
#endif

#ifndef IMPL
#define IMPL "XMSSMT-SHA2_20/2_256"
#endif

#ifndef BENCH_FILE
#define BENCH_FILE "csv/results.csv"
#endif

#ifndef MESSAGE_SIZE
#define MESSAGE_SIZE 65
#endif

#ifndef RUNS
#define RUNS 1
#endif

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

extern int xmssmt_keypair_jazz(uint8_t *pk, uint8_t *sk);
extern int xmssmt_sign_jazz(uint8_t *sk, uint8_t *sm, size_t *smlen, const uint8_t *m, size_t mlen);
extern int xmssmt_sign_open_jazz(uint8_t *m, size_t *mlen, const uint8_t *sm, size_t smlen,
                                 const uint8_t *pk);

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

bool verbose = true;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

static int starts_with(const char *str, const char *prefix) {
    return strncmp(str, prefix, strlen(prefix)) == 0;
}

bool file_exists(const char *filename) {
    assert(filename != NULL);

    FILE *file = fopen(filename, "r");

    if (file) {
        fclose(file);
        return true;
    }

    return false;
}

void write_csv_header(const char *filename) {
    assert(filename != NULL);

    FILE *file = fopen(filename, "w");

    if (!file) {
        perror("Failed to open file");
        exit(EXIT_FAILURE);
    }

    fprintf(file, "op;impl;median;avg\n");
    fclose(file);
}

void get_impl_name(char *buf) {
    assert(buf != NULL);

#ifdef REF_IMPL
    strcpy(buf, "c_ref");
#else

#ifndef ZEROIZATION_STRATEGY
#ifndef ZEROIZATION_SIZE
    // if the strategy and the size are not defined, we can use the default implementation name
    strcpy(buf, "jasmin_base");
#endif
#else
#ifndef ZEROIZATION_SIZE
#error "ZEROIZATION_STRATEGY is defined but ZEROIZATION_SIZE is not defined"
#endif
    snprintf(buf, 256, "jasmin_%s_%s", xstr(ZEROIZATION_STRATEGY), xstr(ZEROIZATION_SIZE));
#endif
#endif
}

void write_results(const char *filename, const char *op, uint64_t median_val, uint64_t avg_val) {
    assert(filename != NULL);
    assert(op != NULL);

    FILE *file = fopen(filename, "a");
    if (file == NULL) {
        perror("Failed to open file");
        exit(EXIT_FAILURE);
    }

    char impl_str[MAXBUFSIZE] = {0};

    get_impl_name(impl_str);

    fprintf(file, "%s;%s;%" PRIu64 ";%" PRIu64 "\n", op, impl_str, median_val, avg_val);
    fclose(file);
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

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

static uint64_t average(uint64_t *t, size_t tlen) {
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

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void xmssmt_bench_kg(const xmss_params *params, uint32_t oid) {
    assert(params != NULL);

    uint8_t pk[XMSS_OID_LEN + params->pk_bytes];
    uint8_t sk[XMSS_OID_LEN + params->sk_bytes];

    uint64_t observations[DATA_POINTS];

    uint64_t before, after;

    uint64_t cpucycles_overhead = overhead_of_cpucycles_call();

    if (!file_exists(BENCH_FILE)) {
        write_csv_header(BENCH_FILE);
    }

    for (size_t i = 0; i + 1 < DATA_POINTS; i++) {
        if (verbose) {
            printf("kg: %zu/%d\n", i, DATA_POINTS - 2);
        }

        before = cpucycles();

#ifdef REF_IMPL
        xmssmt_keypair(pk, sk);
#else
        xmssmt_keypair_jazz(pk, sk);
#endif

        after = cpucycles();
        observations[i] = (after - cpucycles_overhead) - before;
    }

    uint64_t median_val = median(observations, DATA_POINTS);
    uint64_t avg_val = average(observations, DATA_POINTS);
    write_results(BENCH_FILE, "xmssmt_keypair", median_val, avg_val);
}

void xmssmt_bench_sign(const xmss_params *params, uint32_t oid) {
    assert(params != NULL);

    uint8_t m[MESSAGE_SIZE];
    uint8_t pk[XMSS_OID_LEN + params->pk_bytes];
    uint8_t sk[XMSS_OID_LEN + params->sk_bytes];
    uint8_t sm[params->sig_bytes + MESSAGE_SIZE];
    size_t smlen;

    uint64_t observations[DATA_POINTS];

    uint64_t before, after;

    uint64_t cpucycles_overhead = overhead_of_cpucycles_call();

    if (!file_exists(BENCH_FILE)) {
        write_csv_header(BENCH_FILE);
    }

    // First we need to generate a valid keypair
    xmssmt_keypair(pk, sk, oid);

    for (size_t i = 0; i + 1 < DATA_POINTS; i++) {
        if (verbose) {
            printf("sign: %zu/%d\n", i, DATA_POINTS - 2);
        }

        before = cpucycles();

#ifdef REF_IMPL
        xmssmt_sign(sk, sm, (unsigned long long *)&smlen, m, MESSAGE_SIZE);
#else
        xmssmt_sign_jazz(sk, sm, &smlen, m, MESSAGE_SIZE);
#endif

        after = cpucycles();
        observations[i] = (after - cpucycles_overhead) - before;
    }

    uint64_t median_val = median(observations, DATA_POINTS);
    uint64_t avg_jasmin = average(observations, DATA_POINTS);
    write_results(BENCH_FILE, "xmssmt_sign", median_val, avg_jasmin);
}

void xmssmt_bench_verify(const xmss_params *params, uint32_t oid) {
    assert(params != NULL);

    uint8_t m[MESSAGE_SIZE];
    uint8_t pk[XMSS_OID_LEN + params->pk_bytes];
    uint8_t sk[XMSS_OID_LEN + params->sk_bytes];
    uint8_t sm[params->sig_bytes + MESSAGE_SIZE];
    size_t mlen;

    uint64_t observations[DATA_POINTS];

    uint64_t before, after;

    uint64_t cpucycles_overhead = overhead_of_cpucycles_call();

    if (!file_exists(BENCH_FILE)) {
        write_csv_header(BENCH_FILE);
    }

    // First we need to generate a keypair
    xmssmt_keypair(pk, sk, oid);

    for (size_t i = 0; i + 1 < DATA_POINTS; i++) {
        if (verbose) {
            printf("verify: %zu/%d\n", i, DATA_POINTS - 2);
        }

        before = cpucycles();
#ifdef REF_IMPL
        xmssmt_sign_open(m, (unsigned long long *)&mlen, sm, params->sig_bytes + MESSAGE_SIZE, pk);
#else
        xmssmt_sign_open_jazz(m, &mlen, sm, params->sig_bytes + MESSAGE_SIZE, pk);
#endif

        after = cpucycles();
        observations[i] = (after - cpucycles_overhead) - before;
    }

    uint64_t median_val = median(observations, DATA_POINTS);
    uint64_t avg_jasmin = average(observations, DATA_POINTS);
    write_results(BENCH_FILE, "xmssmt_verify", median_val, avg_jasmin);
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

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

        for (int i = 0; i < RUNS; i++) {
            xmssmt_bench_kg(&params, oid);
            xmssmt_bench_sign(&params, oid);
            xmssmt_bench_verify(&params, oid);
        }
    } else {
        fprintf(stderr, "not implemented for the single tree version");
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}