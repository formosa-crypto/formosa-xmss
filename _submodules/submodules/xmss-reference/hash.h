#ifndef XMSS_HASH_H
#define XMSS_HASH_H

#include <stdint.h>
#include "params.h"

void addr_to_bytes(unsigned char *bytes, const uint32_t addr[8]);

int prf(const xmss_params *params,
        unsigned char *out, const unsigned char *in,
        const unsigned char *key, unsigned int keylen);

int h_msg(const xmss_params *params,
          unsigned char *out,
          const unsigned char *in, unsigned long long inlen,
          const unsigned char *key, const unsigned int keylen);

int hash_h(const xmss_params *params,
           unsigned char *out, const unsigned char *in,
           const unsigned char *pub_seed, uint32_t addr[8]);

int hash_f(const xmss_params *params,
           unsigned char *out, const unsigned char *in,
           const unsigned char *pub_seed, uint32_t addr[8]);

#endif
