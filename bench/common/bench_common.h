#ifndef BENCH_COMMON_H
#define BENCH_COMMON_H

#include <inttypes.h>
#include <stdlib.h>

uint64_t min_array(const uint64_t *, size_t);
uint64_t median(uint64_t *, size_t); /* Note: The first argument is not const */
uint64_t average(const uint64_t *, size_t);
uint64_t overhead_of_cpucycles_call(void);

#endif
