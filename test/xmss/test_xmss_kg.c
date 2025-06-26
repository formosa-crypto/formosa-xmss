#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "macros.h"
#include "params.h"
#include "print.h"
#include "randombytes.h"
#include "xmss.h"

#ifndef IMPL
#error IMPL not defined
#endif

#ifndef TESTS
#define TESTS 100
#endif

extern int xmssmt_keypair_jazz(uint8_t *pk, uint8_t *sk);

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

static int starts_with(const char *str, const char *prefix) {
    if (!str || !prefix) {
        return -1;
    }

    return strncmp(str, prefix, strlen(prefix)) == 0;
}

static size_t longestCommonPrefixSize(const uint8_t *array1, const uint8_t *array2, size_t length) {
    size_t prefixLength = 0;

    for (size_t i = 0; i < length; i++) {
        if (array1[i] == array2[i]) {
            prefixLength++;
        } else {
            return prefixLength;
        }
    }

    return prefixLength;
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void test_randombytes(void) {
    // Test that the randombytes and randombytes1 streams are equal

#define BUF_SIZE 1024

    uint8_t x0[BUF_SIZE] = {0};
    uint8_t x1[BUF_SIZE] = {0};

    resetrandombytes();
    resetrandombytes1();

    for (int i = 0; i < TESTS; i++) {
        randombytes(x0, BUF_SIZE);
        randombytes1(x1, BUF_SIZE);

        assert(memcmp(x0, x1, BUF_SIZE) == 0);
    }

#undef BUF_SIZE

    puts("randombytes == randombytes1: OK");
}

void test_xmssmt_keypair(void) {
    // The C impl calls randombytes and the Jasmin impl calls randombytes1
    // We assume that both randombytes and randombytes1 output the same bytes (this test is only run
    // after the test that checks if randombytes == randombytes1)

    bool verbose = true;

    xmss_params p;
    uint32_t oid;

    if (xmssmt_str_to_oid(&oid, xstr(IMPL)) == -1) {
        fprintf(stderr, "Failed to generate oid from impl name\n");
        exit(-1);
    }

    if (xmssmt_parse_oid(&p, oid) == -1) {
        fprintf(stderr, "Failed to generate params from oid\n");
        exit(-1);
    }

    /* Format sk: [OID || (32bit) idx || SK_SEED || SK_PRF || PUB_SEED || root] */
    /* Na SK, na verdade a root ta a seguir ao idx */
    /* Format pk: [OID || root || PUB_SEED] */
    uint8_t pk_ref[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk_ref[XMSS_OID_LEN + p.sk_bytes];
    uint8_t pk_jasmin[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk_jasmin[XMSS_OID_LEN + p.sk_bytes];
    int res_jasmin, res_ref;

    for (int i = 0; i < TESTS; i++) {
        if (verbose) {
            printf("[xmssmt keypair] Test %d/%d\n", i + 1, TESTS);
        }

        res_ref = xmssmt_keypair(pk_ref, sk_ref, oid);
        res_jasmin = xmssmt_keypair_jazz(pk_jasmin, sk_jasmin);

        assert(res_jasmin == res_ref);

        assert(memcmp(pk_ref, pk_jasmin, sizeof(uint32_t)) == 0);  // Compare the OID on the pk
        assert(memcmp(sk_ref, sk_jasmin, sizeof(uint32_t)) == 0);  // Compare the OID on the sk

        if (verbose) {
            if (memcmp(pk_ref, pk_jasmin, XMSS_OID_LEN + p.pk_bytes) != 0) {
                printf("Longest match on the pk: %ld bytes\n",
                       longestCommonPrefixSize(pk_ref, pk_jasmin, XMSS_OID_LEN + p.pk_bytes));

                if (memcmp(pk_ref + XMSS_OID_LEN + p.n, pk_jasmin + XMSS_OID_LEN + p.n, p.n) == 0) {
                    puts("Pub seed matches on the PK");
                } else {
                    puts("Pub seed does not match on the PK");
                }
            }
        }

        assert(memcmp(sk_ref, sk_jasmin, XMSS_OID_LEN + p.sk_bytes) == 0);  // Compare the whole key
        assert(memcmp(pk_ref, pk_jasmin, XMSS_OID_LEN + p.pk_bytes) == 0);  // Compare the whole key
    }
}

int main(void) {
    test_randombytes();

    if (starts_with(xstr(IMPL), "XMSSMT")) {
        test_xmssmt_keypair();
    } else {
        fprintf(stderr, "Not implemented for single tree version");
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}
