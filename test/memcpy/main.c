#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "print.h"
#include "randombytes.h"

#ifndef INLEN
#error INLEN not defined
#endif

#ifndef TESTS
#define TESTS 10000
#endif

extern void copy(const unsigned char *src, uint8_t *dst, size_t offset);

void test__memcpy_u8pu8_offset_0(void) {
    
    for (int i = 0; i < TESTS; i++) {
        uint8_t src[INLEN] = {0};
        uint8_t dst_jasmin[INLEN] = {0};
        randombytes(src, INLEN);
        copy(src, dst_jasmin, 0);


        if (memcmp(dst_jasmin, src, INLEN) != 0) {
            for (size_t j = 0; j < INLEN; j++) {
                if (src[j] != dst_jasmin[j]) {
                    printf("index %ld is different\nsrc[index]=%d and dest[index]=%d\n\n", j, src[j],
                           dst_jasmin[j]);
                }
            }
            print_str_u8("src", src, INLEN);
            print_str_u8("dst_jasmin", dst_jasmin, INLEN);
        }

        assert(memcmp(dst_jasmin, src, INLEN) == 0);
    }
}

int main(void) {
    test__memcpy_u8pu8_offset_0();
    printf("[INLEN=%d: OK]\n", INLEN);
    return 0;
}