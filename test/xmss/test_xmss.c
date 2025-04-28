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

#ifndef MSG_LEN
#define MSG_LEN 1024
#endif

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

extern int xmssmt_keypair_jazz(uint8_t *pk, uint8_t *sk);

extern int xmssmt_sign_jazz(uint8_t *sk, uint8_t *sm, size_t *smlen, const uint8_t *m, size_t mlen);

extern int xmssmt_sign_open_jazz(uint8_t *m, size_t *mlen, const uint8_t *sm, size_t smlen,
                                 const uint8_t *pk);

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

static int starts_with(const char *str, const char *prefix) {
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

    bool debug = true;

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
        if (debug) {
            printf("[xmssmt keypair] Test %d/%d\n", i + 1, TESTS);
        }

        res_ref = xmssmt_keypair(pk_ref, sk_ref, oid);

        if (debug && false) {
            puts("Ref finished");
        }

        res_jasmin = xmssmt_keypair_jazz(pk_jasmin, sk_jasmin);

        assert(res_jasmin == res_ref);

        assert(memcmp(pk_ref, pk_jasmin, sizeof(uint32_t)) == 0);  // Compare the OID on the pk
        assert(memcmp(sk_ref, sk_jasmin, sizeof(uint32_t)) == 0);  // Compare the OID on the sk

        if (debug) {
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

void test_xmssmt_sign_open(void) {
    bool debug = true;

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

    uint8_t m[MSG_LEN];
    uint8_t pk[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk[XMSS_OID_LEN + p.sk_bytes];
    uint8_t sm[p.sig_bytes + MSG_LEN];
    size_t smlen;
    size_t _mlen_ref, _mlen_jasmin;
    int res_ref, res_jasmin;

    for (int i = 0; i < TESTS; i++) {
        size_t mlen = MSG_LEN;
        if (debug) {
            printf("[xmssmt sign open] Test %d/%d (msg len = %ld/%d)\n", i + 1, TESTS, mlen,
                   MSG_LEN);
        }

        // First we need to generate a keypair and a valid signature
        xmssmt_keypair(pk, sk, oid);
        xmssmt_sign(sk, sm, (unsigned long long *)&smlen, m, mlen);

        res_ref = xmssmt_sign_open_jazz(m, &_mlen_ref, sm, smlen,
                                        pk);  // Obs: Verifying does not update the SK
        res_jasmin = xmssmt_sign_open_jazz(m, &_mlen_jasmin, sm, smlen,
                                           pk);  // Obs: Verifying does not update the SK

        assert(_mlen_ref == mlen);
        assert(_mlen_jasmin == mlen);
        assert(_mlen_jasmin == _mlen_ref);
        assert(res_ref == 0);
        assert(res_jasmin == 0);
        assert(res_jasmin == res_ref);
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
