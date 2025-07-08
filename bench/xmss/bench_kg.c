#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "macros.h"
#include "params.h"
#include "xmss.h"

#ifndef DATA_POINTS
#define DATA_POINTS 10000
#endif

#ifndef OUTPUT_FILE
#define OUTPUT_FILE "csv/xmssmt_kg.csv"
#endif

#ifndef IMPL
#define IMPL "XMSSMT-SHA2_20/2_256"
#endif

#ifndef MESSAGE_SIZE
#define MESSAGE_SIZE 65
#endif

#ifndef RUNS
#define RUNS 1
#endif

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

extern int xmssmt_keypair_jazz(uint8_t *pk, uint8_t *sk);

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

bool verbose = true;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

static int starts_with(const char *str, const char *prefix) {
    return strncmp(str, prefix, strlen(prefix)) == 0;
}

static bool file_exists(const char *filename) {
    assert(filename != NULL);

    FILE *file = fopen(filename, "r");

    if (file) {
        fclose(file);
        return true;
    }
    return false;
}

static char *get_op_name(const char *op) {
    assert(op != NULL);

#ifdef REF
    const char *suffix = "_ref";
#endif

#ifdef LOOP
    const char *suffix = "_loop";
#endif

#ifdef UNROLLED
    const char *suffix = "_unrolled";
#endif

#ifdef JASMIN_BASE
    const char *suffix = "_jasmin";
#endif

    size_t len = strlen(op) + strlen(suffix) + 1;

    char *result = malloc(len);
    if (result == NULL) {
        perror("malloc failed");
        exit(EXIT_FAILURE);
    }

    strcpy(result, op);
    strcat(result, suffix);

    return result;
}

static char *get_impl_name(char *buf, size_t buf_size) {
    memset(buf, 0, buf_size);

#ifdef REF
    snprintf(buf, buf_size, "ref");
#endif

#ifdef LOOP
    snprintf(buf, buf_size, "loop");
#endif

#ifdef UNROLLED
    snprintf(buf, buf_size, "unrolled");
#endif

#ifdef JASMIN_BASE
    snprintf(buf, buf_size, "jasmin");
#endif

    return buf;
}

void write_csv_header(const char *filename, const char *op) {
    assert(filename != NULL);
    assert(op != NULL);

    FILE *file = fopen(filename, "w");

    if (!file) {
        perror("Failed to open file");
        exit(EXIT_FAILURE);
    }

#ifdef MEDIAN_ONLY
    fprintf(file, "op;median\n");
#else
    fprintf(file, "op;median;avg\n");
#endif
    fclose(file);
}

void write_results(const char *filename, const char *op, uint64_t median, uint64_t avg) {
    assert(filename != NULL);
    assert(op != NULL);

    FILE *file = fopen(filename, "a");
    if (file == NULL) {
        perror("Failed to open file");
        exit(EXIT_FAILURE);
    }

    const char *op_name = get_op_name(op);

#ifdef MEDIAN_ONLY
    fprintf(file, "%s;%" PRIu64 "\n", op_name, median);
#else
    fprintf(file, "%s;%" PRIu64 ";%" PRIu64 "\n", op_name, median, avg);
#endif

    free((void *)op_name);

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

    char buf[256] = {0};

    if (!file_exists(xstr(OUTPUT_FILE))) {
        write_csv_header(xstr(OUTPUT_FILE), "keypair");
    }

    for (size_t i = 0; i + 1 < DATA_POINTS; i++) {
        if (verbose) {
            printf("kg [%s]: %zu/%d\n", get_impl_name(buf, 256), i, DATA_POINTS);
        }

        before = cpucycles();

#ifdef REF
        xmssmt_keypair(pk, sk, oid);
#else
        xmssmt_keypair_jazz(pk, sk);
#endif

        after = cpucycles();
        observations[i] = (after - cpucycles_overhead) - before;
    }

    uint64_t median_val = median(observations, DATA_POINTS);

#ifdef MEDIAN_ONLY
    write_results(xstr(OUTPUT_FILE), "keypair", median_val, 0);
#else
    uint64_t avg = average(observations, DATA_POINTS);
    write_results(xstr(OUTPUT_FILE), "keypair", median_val, avg);
#endif
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
        }
    } else {
        fprintf(stderr, "not implemented for the single tree version");
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}
