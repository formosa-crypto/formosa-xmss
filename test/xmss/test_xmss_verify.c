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

extern int xmssmt_sign_open_jazz(uint8_t *m, size_t *mlen, const uint8_t *sm, size_t smlen,
                                 const uint8_t *pk);

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

static int starts_with(const char *str, const char *prefix) {
    if (!str || !prefix) {
        return -1;
    }

    return strncmp(str, prefix, strlen(prefix)) == 0;
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void test_xmssmt_sign_open(void) {
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

    if (verbose) { puts("A"); }

    uint8_t m[MSG_LEN];
    uint8_t pk[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk[XMSS_OID_LEN + p.sk_bytes];
    uint8_t sm[p.sig_bytes + MSG_LEN];
    size_t smlen;
    size_t _mlen_ref, _mlen_jasmin;
    int res_ref, res_jasmin;

    if (verbose) { puts("B"); }

    for (int i = 0; i < TESTS; i++) {
        if (verbose) {
            printf("[xmssmt sign open] Test %d/%d (msg len = %d)\n", i + 1, TESTS, MSG_LEN);
        }

        // First we need to generate a keypair and a valid signature
        xmssmt_keypair(pk, sk, oid);
        xmssmt_sign(sk, sm, (unsigned long long *)&smlen, m, MSG_LEN);

        if (verbose) { puts("C"); }

        res_ref = xmssmt_sign_open(m, (unsigned long long *)&_mlen_ref, sm, smlen,
                                   pk);  // Obs: Verifying does not update the SK
        res_jasmin = xmssmt_sign_open_jazz(m, &_mlen_jasmin, sm, smlen,
                                           pk);  // Obs: Verifying does not update the SK

        if (verbose) { puts("D"); }

        assert(_mlen_ref == MSG_LEN);
        assert(_mlen_jasmin == MSG_LEN);
        assert(_mlen_jasmin == _mlen_ref);
        assert(res_ref == 0);
        assert(res_jasmin == 0);
        assert(res_jasmin == res_ref);

        if (verbose) { puts("E"); }
    }

    if (verbose) { puts("F"); }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

int main(void) {
    bool verbose = true;

    if (verbose) { puts("G"); }

    if (starts_with(xstr(IMPL), "XMSSMT")) {
        if (verbose) { puts("H1"); }
        test_xmssmt_sign_open();
        if (verbose) { puts("H2"); }
    } else {
        if (verbose) { puts("Ha"); }
        fprintf(stderr, "Not implemented for single tree version");
        if (verbose) { puts("Hb"); }
        return EXIT_FAILURE;
    }
    
    if (verbose) { puts("I"); }

    return EXIT_SUCCESS;
}
