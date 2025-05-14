#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "params.h"
#include "xmss.h"

#ifndef DATA_POINTS
#define DATA_POINTS 10000
#endif

#ifndef IMPL
#define IMPL "XMSSMT-SHA2_20/2_256"
#endif

#ifndef XMSSMT_KG_FILE
#define XMSSMT_KG_FILE "csv/xmssmt_kg.csv"
#endif

#ifndef XMSS_KG_FILE
#define XMSS_KG_FILE "csv/xmss_kg.csv"
#endif

#ifndef XMSSMT_SIGN_FILE
#define XMSSMT_SIGN_FILE "csv/xmssmt_sign.csv"
#endif

#ifndef XMSS_SIGN_FILE
#define XMSS_SIGN_FILE "csv/xmss_sign.csv"
#endif

#ifndef XMSSMT_VERIFY_FILE
#define XMSSMT_VERIFY_FILE "csv/xmssmt_verify.csv"
#endif

#ifndef XMSS_VERIFY_FILE
#define XMSS_VERIFY_FILE "csv/xmss_verfify.csv"
#endif

#ifndef MESSAGE_SIZE
#define MESSAGE_SIZE 65
#endif

#ifndef RUNS
#define RUNS 1
#endif

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

bool verbose = true;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

static int starts_with(const char *str, const char *prefix) {
    return strncmp(str, prefix, strlen(prefix)) == 0;
}

bool file_exists(const char *filename) {
    assert(filename != NULL);

    FILE *file = fopen(filename, "r");

    if (!file) {
        fclose(file);
        return true;
    }
    return false;
}

void write_csv_header(const char *filename, const char *op) {
    assert(filename != NULL);
    assert(op != NULL);

    FILE *file = fopen(filename, "w");

    if (file == NULL) {
        perror("Failed to open file");
        exit(EXIT_FAILURE);
    }

    fprintf(file, "op;median_ref;avg_ref;median_jasmin;avg_jasmin\n");
    fclose(file);
}

void write_results(const char *filename, const char *op, uint64_t median_ref, uint64_t avg_ref,
                   uint64_t median_jasmin, uint64_t avg_jasmin) {
    assert(filename != NULL);
    assert(op != NULL);

    FILE *file = fopen(filename, "a");
    if (file == NULL) {
        perror("Failed to open file");
        exit(EXIT_FAILURE);
    }

    fprintf(file, "%s;%" PRIu64 ";%" PRIu64 ";%" PRIu64 ";%" PRIu64 "\n", op, median_ref, avg_ref,
            median_jasmin, avg_jasmin);
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

int main(void) { return EXIT_SUCCESS; }