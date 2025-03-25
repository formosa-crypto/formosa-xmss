#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <sys/random.h>
#include <stdbool.h>

#ifndef TESTS
#define TESTS 10000
#endif

extern void memcpy_nbyes(unsigned char *dest, unsigned char *src);

void random_32_bytes(unsigned char buf[32]) {
    if (getrandom(buf, 32, 0) != 32) {
        perror("getrandom failed");
        exit(EXIT_FAILURE);
    }
}

int main(void) {
    bool verbose = true;
    unsigned char out_ref[32] = {0};
    unsigned char out_jasmin[32] = {0};
    unsigned char in[32];

    for (int i = 0; i < TESTS; i++) {
        if (verbose) { printf("Test %d/%d\n", i+1, TESTS); }
        random_32_bytes(in);
        memcpy(out_ref, in, 32);
        memcpy_nbyes(out_jasmin, in);
        assert(memcmp(out_ref, out_jasmin, 32) == 0);
    }

    return EXIT_SUCCESS;
}