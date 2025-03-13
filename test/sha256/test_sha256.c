#include <assert.h>
#include <inttypes.h>
#include <openssl/sha.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "randombytes.h"

#ifndef MAX_INLEN
#define MAX_INLEN 128
#endif

#ifndef TESTS
#define TESTS 1000
#endif

#ifdef INLEN
extern void sha256_jazz(uint8_t *out, const uint8_t *in);

void test_sha256_array(void);

void test_sha256_array(void) {
    bool verbose = true;

    uint8_t in[INLEN] = {0};
    uint8_t result_jasmin[SHA256_DIGEST_LENGTH] = {0};
    uint8_t result_ref[SHA256_DIGEST_LENGTH] = {0};

    for (int i = 0; i < TESTS; i++) {
        randombytes(in, INLEN);
        sha256_jazz(result_jasmin, in);
        SHA256(in, INLEN, result_ref);

        assert(memcmp(result_jasmin, result_ref, 32) == 0);
    }

    if (verbose) {
        printf("SHA256 (Array size = %d): OK\n", INLEN);
    }
}
#else
extern void sha256_in_ptr_jazz(uint8_t *out, const uint8_t *in, size_t inlen);

void test_sha256_ptr(void);

void test_sha256_ptr(void) {
    bool verbose = true;

    uint8_t in[MAX_INLEN] = {0};
    uint8_t result_jasmin[SHA256_DIGEST_LENGTH] = {0};
    uint8_t result_ref[SHA256_DIGEST_LENGTH] = {0};

    for (size_t inlen = 1; inlen <= MAX_INLEN; inlen++) {
        for (int i = 0; i < TESTS; i++) {
            randombytes(in, inlen);
            sha256_in_ptr_jazz(result_jasmin, in, inlen);
            SHA256(in, inlen, result_ref);

            assert(memcmp(result_jasmin, result_ref, 32) == 0);
        }

        if (verbose) {
            printf("SHA256 ptr (size = %ld): OK\n", inlen);
        }
    }
}
#endif

int main(void) {
#ifdef INLEN
    // Here we test the impl working over arrays
    test_sha256_array();
#else
    // Here we test the impl working over external memory
    test_sha256_ptr();
#endif

    return EXIT_SUCCESS;
}