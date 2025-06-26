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

extern int xmssmt_sign_jazz(uint8_t *sk, uint8_t *sm, size_t *smlen, const uint8_t *m, size_t mlen);

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

static int starts_with(const char *str, const char *prefix) {
    if (!str || !prefix) {
        return -1;
    }

    return strncmp(str, prefix, strlen(prefix)) == 0;
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

static int valid_idx(const xmss_params *p, uint32_t idx) {
    if (!p) {
        assert(false);
    }

    return idx < ((1ULL << p->full_height) - 1);
}

void test_xmssmt_sign(void) {
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

    uint8_t pk[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk_ref[XMSS_OID_LEN + p.sk_bytes];
    uint8_t sk_jasmin[XMSS_OID_LEN + p.sk_bytes];
    uint8_t sm_ref[p.sig_bytes + MSG_LEN];
    uint8_t sm_jasmin[p.sig_bytes + MSG_LEN];
    size_t smlen_ref, smlen_jasmin;

    uint8_t m[MSG_LEN];

    int res_ref, res_jasmin;

    // Generate a keypair
    xmssmt_keypair(pk, sk_ref, oid);

    for (int i = 0; i < TESTS; i++) {
        if (verbose) {
            printf("[xmssmt sign] Test %d/%d (msg len = %d)\n", i + 1, TESTS, MSG_LEN);
        }

        // Make sure we can still use the secret key to sign
        if (!valid_idx(&p, (uint32_t)i)) {
            fprintf(stderr, "Invalid index %d\n", i);
            exit(EXIT_FAILURE);
        }

        randombytes(m, MSG_LEN);  // Generate a random message

        // copy the sk_ref to sk_jasmin
        // This is to ensure that both implementations use the same key when signing
        memcpy(sk_jasmin, sk_ref, sizeof(sk_jasmin));

        res_ref = xmssmt_sign(sk_ref, sm_ref, (unsigned long long *)&smlen_ref, m, MSG_LEN);
        res_jasmin = xmssmt_sign_jazz(sk_jasmin, sm_jasmin, &smlen_jasmin, m, MSG_LEN);

        assert(res_ref == res_jasmin);
        assert(res_jasmin == 0);
        assert(res_ref == 0);
        assert(memcmp(sm_ref, sm_jasmin, p.sig_bytes + MSG_LEN) == 0);
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

int main(void) {
    if (starts_with(xstr(IMPL), "XMSSMT")) {
        test_xmssmt_sign();
    } else {
        fprintf(stderr, "Not implemented for single tree version");
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}
