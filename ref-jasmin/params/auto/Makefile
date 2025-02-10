# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

# --------------------------------------------------------------------------------------------------

REF_SOURCES := $(filter-out %xmss_core_fast.c, $(wildcard ../../../submodules/xmss-reference/*.c))

# --------------------------------------------------------------------------------------------------

default: bin/gen_params
run: bin/gen_params.out

# --------------------------------------------------------------------------------------------------

bin/gen_params: | bin/
	$(CC) $(CFLAGS) -o $@ -I../../../submodules/xmss-reference/ gen_params.c $(REF_SOURCES) $(LDLIBS)

bin/gen_params.out: bin/gen_params
	@./$<
	# We only consider the implementations that use sha-2 as the underlying hash function
	-$(RM) -r ../params-xmss-shake*
	-$(RM) -r ../params-xmssmt-shake*

# --------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	-$(RM) -r bin/

distclean:
	find ../ -type f -name 'params-*' -delete
