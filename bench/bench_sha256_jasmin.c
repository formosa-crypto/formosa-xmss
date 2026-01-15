#include <openssl/sha.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "alignedcalloc.c"
#include "bench.h"
#include "macros.h"

#ifndef TIMINGS
#warning "TIMINGS not defined, defaulting to 10000"
#define TIMINGS 10000
#endif

#ifndef INLEN
#warning "INLEN not defined, defaulting to 1024"
#define INLEN 1024
#endif

extern void sha256_in_ptr_jazz(uint8_t *out, const uint8_t *in, size_t inlen);
extern void sha256_32(uint8_t *out, const uint8_t *in);
extern void sha256_64(uint8_t *out, const uint8_t *in);

void bench_sha256_ptr(void) {
    uint8_t *out_orig, *in_orig;
    uint8_t *out = alignedcalloc(&out_orig, SHA256_DIGEST_LENGTH);
    uint8_t *in = alignedcalloc(&in_orig, INLEN);
    size_t inlen = INLEN;

    BENCHMARK_N_TIMES(TIMINGS, "results/sha256_jasmin_ptr.txt", sha256_in_ptr_jazz(out, in, INLEN));

    free(out_orig);
    free(in_orig);
}

void bench_sha256_array(void) {
    uint8_t *out_orig, *in_orig;
    uint8_t *out = alignedcalloc(&out_orig, SHA256_DIGEST_LENGTH);
    uint8_t *in = alignedcalloc(&in_orig, 64);

    BENCHMARK_N_TIMES(TIMINGS, "results/sha256_jasmin_32.txt", sha256_32(out, in));
    BENCHMARK_N_TIMES(TIMINGS, "results/sha256_jasmin_64.txt", sha256_64(out, in));

    free(out_orig);
    free(in_orig);
}

void bench_sha2_openssl(size_t inlen) {
    uint8_t *out_orig, *in_orig;
    uint8_t *out = alignedcalloc(&out_orig, SHA256_DIGEST_LENGTH);
    uint8_t *in = alignedcalloc(&in_orig, inlen);

    char filename[64];
    snprintf(filename, sizeof(filename), "results/sha256_openssl_%zu.txt", inlen);

    BENCHMARK_N_TIMES(TIMINGS, filename, SHA256(in, inlen, out));

    free(out_orig);
    free(in_orig);
}

int main(void) {
    bench_sha256_ptr();
    bench_sha256_array();
    bench_sha2_openssl(32);
    bench_sha2_openssl(64);
    return EXIT_SUCCESS;
}
