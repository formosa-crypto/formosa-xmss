#include <assert.h>
#include <inttypes.h>
#include <math.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "macros.h"
#include "new_xmss.h"
#include "params.h"
#include "print.h"
#include "randombytes.h"
#include "xmss.h"
#include "xmss_core.h"

#ifndef IMPL
#error IMPL must be defined
#endif

#ifndef TESTS
#define TESTS 10
#endif

static int starts_with(const char *str, const char *prefix) {
    return strncmp(str, prefix, strlen(prefix)) == 0;
}

void test_api(xmss_params *p) {
    assert(p != NULL);

#define XMSS_MLEN 32
    bool debug = true;

    uint8_t pk_ref[p->pk_bytes];
    uint8_t pk_test[p->pk_bytes];

    uint8_t sk_ref[p->sk_bytes];
    uint8_t sk_test[p->sk_bytes];

    uint8_t seed[3 * p->n];

    unsigned char m_ref[XMSS_MLEN];
    unsigned char sm_ref[p->sig_bytes + XMSS_MLEN], sm_new[p->sig_bytes + XMSS_MLEN];
    unsigned long long smlen_ref, smlen_new;

    for (size_t i = 0; i < 3 * p->n; i++) {
        seed[i] = 42;
    }

    /*
    TODO: Test with KG
    // Test KG
    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("KG: Test %d/%d\n", i + 1, TESTS);
        }

        xmssmt_core_seed_keypair(p, pk_ref, sk_ref, seed);
        xmssmt_core_seed_keypair_new(p, pk_test, sk_test, seed);

        if (memcmp(pk_ref, pk_test, p->pk_bytes) != 0) {
            print_str_u8("root ref", pk_ref, sizeof(uint8_t) * p->n);
            print_str_u8("root test", pk_test, sizeof(uint8_t) * p->n);

            print_str_u8("pub_seed ref", pk_ref + p->n, sizeof(uint8_t) * p->n);
            print_str_u8("pub_seed test", pk_test + p->n, sizeof(uint8_t) * p->n);
        }

        // the pub seed is the same
        assert(memcmp(pk_ref + p->n, pk_test + p->n, sizeof(uint8_t) * p->n) == 0);

        // the whole public key is the same
        assert(memcmp(pk_ref, pk_test, sizeof(uint8_t) * p->pk_bytes) == 0);

        assert(memcmp(sk_ref, sk_test, sizeof(uint8_t) * p->sk_bytes) == 0);
    }
*/

    // Test Sign
    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("Test: Sign %d/%d\n", i + 1, TESTS);
        }

        // First we generate a keypair to sign
        xmssmt_core_seed_keypair(p, pk_ref, sk_ref, seed);

        memcpy(sk_test, sk_ref, p->sk_bytes);

        // Make sure the keypair is the same (we only need the sk)
        assert(memcmp(sk_ref, sk_test, p->sk_bytes) == 0);

        randombytes((uint8_t *)m_ref, XMSS_MLEN);

        xmssmt_core_sign(p, sk_ref, sm_ref, &smlen_ref, m_ref, XMSS_MLEN);
        xmssmt_core_sign_new(p, sk_test, sm_new, &smlen_new, m_ref, XMSS_MLEN);

        // the index of the sk was updated after signing
        assert(memcmp(sk_test, sk_ref, p->sk_bytes) == 0);

        // smlen was set correctly
        assert(smlen_new == smlen_ref);
    }

    // OBS: We dont test verify because it does not depend on treehash

#undef XMSS_MLEN
}

int main(void) {
    xmss_params p;
    uint32_t oid;

    if (starts_with(xstr(IMPL), "XMSSMT")) {
        if (xmssmt_str_to_oid(&oid, xstr(IMPL)) == -1) {
            fprintf(stderr, "[multi tree]: Failed to generate oid from impl name\n");
            exit(-1);
        }

        if (xmssmt_parse_oid(&p, oid) == -1) {
            fprintf(stderr, "[multi tree]: Failed to generate params from oid\n");
            exit(-1);
        }
    } else {
        if (xmss_str_to_oid(&oid, xstr(IMPL)) == -1) {
            fprintf(stderr, "[single tree]: Failed to generate oid from impl name\n");
            exit(-1);
        }

        if (xmss_parse_oid(&p, oid) == -1) {
            fprintf(stderr, "[single tree]: Failed to generate params from oid\n");
            exit(-1);
        }
    }

    test_api(&p);

    return EXIT_SUCCESS;
}