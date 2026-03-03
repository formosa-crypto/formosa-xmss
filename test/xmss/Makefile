# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

JASMIN   ?= jasminc 
JAZZCT   ?= jasmin-ct
JAZZCTFLAGS ?= --infer
JFLAGS   ?= -g ${JADDFLAGS} # -g so its easier to debug when using valgrind
JINCLUDE ?= -I XMSS="../../ref-jasmin/" -I Stdlib="../../ref-jasmin/stdlib"

JASMINPATH := JASMINPATH="XMSS=../../ref-jasmin/:Stdlib=../../ref-jasmin/stdlib"

VALGRIND := valgrind
VALGRIND_FLAGS ?= --leak-check=full --show-leak-kinds=all --track-origins=yes --verbose --error-exitcode=1

# --------------------------------------------------------------------------------------------------

BIN := bin/test_xmssmt-sha2_20_2_256_kg \
       bin/test_xmssmt-sha2_20_2_256_sign \
	   bin/test_xmssmt-sha2_20_2_256_verify

OUT := $(addsuffix .out, $(BIN))

test_kg: bin/test_xmssmt-sha2_20_2_256_kg.out
test_sign: bin/test_xmssmt-sha2_20_2_256_sign.out
test_verify: bin/test_xmssmt-sha2_20_2_256_verify.out

default: test

asm: bin/test_xmssmt-sha2_20_2_256.s
# bin/test_xmssmt-sha2_20_2_256_kg.s \
# bin/test_xmssmt-sha2_20_2_256_sign.s \
# bin/test_xmssmt-sha2_20_2_256_verify.s

test: $(BIN)
run: $(OUT)

checkCT: test_xmss-sha2_20_2_256.jazz test_xmss.jazz
	$(JASMINPATH) $(JAZZCT) $(JAZZCTFLAGS) $<

# --------------------------------------------------------------------------------------------------

REF_SOURCES   := $(filter-out ../../submodules/xmss-reference/xmss_core_fast.c ../../submodules/xmss-reference/randombytes.c, $(wildcard ../../submodules/xmss-reference/*.c))
SOURCES := ../common/notrandombytes.c ../common/print.c

# --------------------------------------------------------------------------------------------------

bin/test_xmssmt-sha2_20_2_256.s: test_xmss-sha2_20_2_256.jazz test_xmss.jazz | bin/
	$(JASMIN) $(JINCLUDE) $(JFLAGS) -o $@ $<

bin/test_xmssmt-sha2_20_2_256_kg.s: test_xmss-sha2_20_2_256.jazz test_xmss.jazz | bin/
	$(JASMIN) $(JINCLUDE) $(JFLAGS) -slice xmssmt_keypair_jazz -o $@ $<

bin/test_xmssmt-sha2_20_2_256_sign.s: test_xmss-sha2_20_2_256.jazz test_xmss.jazz | bin/
	$(JASMIN) $(JINCLUDE) $(JFLAGS) -slice xmssmt_sign_jazz -o $@ $<

bin/test_xmssmt-sha2_20_2_256_verify.s: test_xmss-sha2_20_2_256.jazz test_xmss.jazz | bin/
	$(JASMIN) $(JINCLUDE) $(JFLAGS) -slice xmssmt_sign_open_jazz -o $@ $<

# --------------------------------------------------------------------------------------------------

bin/test_xmssmt-sha2_20_2_256_valgrind: bin/test_xmssmt-sha2_20_2_256.s
	$(CC) -g -O0 -o $@ -I../common -I../ -DIMPL=XMSSMT-SHA2_20/2_256  -DTESTS=2 \
	test_valgrind.c $(SOURCES) $(REF_SOURCES) $< $(LDLIBS)

bin/test_xmssmt-sha2_20_2_256_%: bin/test_xmssmt-sha2_20_2_256_%.s
	$(CC) $(CFLAGS) -o $@ -I../common -I../ -DIMPL=XMSSMT-SHA2_20/2_256 \
	test_xmss_$*.c $(SOURCES) $(REF_SOURCES) $< $(LDLIBS)

# --------------------------------------------------------------------------------------------------

bin/%.out: bin/%
	@./$<

# --------------------------------------------------------------------------------------------------

check_valgrind: bin/test_xmssmt-sha2_20_2_256_valgrind
	$(VALGRIND) $(VALGRIND_FLAGS) $<

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	-$(RM) -r bin/

.PHONY: clean_executables
clean_executables:
	find bin/ -type f -executable -delete || true
