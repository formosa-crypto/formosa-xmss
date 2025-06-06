#ifndef XMSS_WOTS_H
#define XMSS_WOTS_H

#include <stdint.h>

#include "params.h"

// for testing
void wots_checksum(const xmss_params *params, int *csum_base_w, const int *msg_base_w);

// for testing
void expand_seed(const xmss_params *params, unsigned char *outseeds, const unsigned char *inseed,
                 const unsigned char *pub_seed, uint32_t addr[8]);

// for testing
void gen_chain(const xmss_params *params, unsigned char *out, const unsigned char *in,
               unsigned int start, unsigned int steps, const unsigned char *pub_seed,
               uint32_t addr[8]);

/**
 * WOTS key generation. Takes a 32 byte seed for the private key, expands it to
 * a full WOTS private key and computes the corresponding public key.
 * It requires the seed pub_seed (used to generate bitmasks and hash keys)
 * and the address of this WOTS key pair.
 *
 * Writes the computed public key to 'pk'.
 */
void wots_pkgen(const xmss_params *params, unsigned char *pk, const unsigned char *seed,
                const unsigned char *pub_seed, uint32_t addr[8]);

/**
 * Takes a n-byte message and the 32-byte seed for the private key to compute a
 * signature that is placed at 'sig'.
 */
void wots_sign(const xmss_params *params, unsigned char *sig, const unsigned char *msg,
               const unsigned char *seed, const unsigned char *pub_seed, uint32_t addr[8]);

/**
 * Takes a WOTS signature and an n-byte message, computes a WOTS public key.
 *
 * Writes the computed public key to 'pk'.
 */
void wots_pk_from_sig(const xmss_params *params, unsigned char *pk, const unsigned char *sig,
                      const unsigned char *msg, const unsigned char *pub_seed, uint32_t addr[8]);

#endif
