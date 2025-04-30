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

#ifndef RUNS
#define RUNS 1
#endif

#ifndef MSG_LEN
#define MSG_LEN 1024
#endif

extern int xmssmt_keypair_jazz(uint8_t *pk, uint8_t *sk);

extern int xmssmt_sign_jazz(uint8_t *sk, uint8_t *sm, size_t *smlen, const uint8_t *m, size_t mlen);

extern int xmssmt_sign_open_jazz(uint8_t *m, size_t *mlen, const uint8_t *sm, size_t smlen,
                                 const uint8_t *pk);

xmss_params setup_params(void) {
    xmss_params p;
    uint32_t oid;

    if (xmssmt_str_to_oid(&oid, xstr(IMPL)) == -1) {
        fprintf(stderr, "Failed to generate oid from impl name\n");
        exit(EXIT_FAILURE);
    }

    if (xmssmt_parse_oid(&p, oid) == -1) {
        fprintf(stderr, "Failed to generate params from oid\n");
        exit(EXIT_FAILURE);
    }

    return p;
}

int main(void) {
    xmss_params p = setup_params();

    uint8_t m[MSG_LEN] = {0};
    uint8_t pk[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk[XMSS_OID_LEN + p.sk_bytes];
    uint8_t sm[p.sig_bytes + MSG_LEN];
    uint8_t mout[p.sig_bytes + MSG_LEN];
    uint64_t smlen;
    uint64_t mlen = MSG_LEN;

    for (int i = 0; i < RUNS; i++) {
        xmssmt_keypair_jazz(pk, sk);
        xmssmt_sign_jazz(sk, sm, &smlen, m, mlen);
        int res = xmssmt_sign_open_jazz(mout, &mlen, sm, smlen, pk);
    }

    // TODO: Test an invalid signature so that the first branch of __set_result is triggered

    return EXIT_SUCCESS;
}
