# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

JASMIN   ?= jasminc
JAZZCT   ?= jasmin-ct
JAZZCTFLAGS ?= --infer
JFLAGS   ?= ${JADDFLAGS}
JINCLUDE ?= -I XMSS="../../ref-jasmin/" -I Stdlib="../../ref-jasmin/stdlib"

JASMINPATH := JASMINPATH="XMSS=../../ref-jasmin/:Stdlib=../../ref-jasmin/stdlib"

# --------------------------------------------------------------------------------------------------

default: test
asm: bin/test_xmssmt-sha2_20_2_256.s
test: bin/test_xmssmt-sha2_20_2_256
run: bin/test_xmssmt-sha2_20_2_256.out

checkCT: test_treehash-sha2_20_2_256.jazz test_treehash.jazz
	$(JASMINPATH) $(JAZZCT) $(JAZZCTFLAGS) $< >/dev/null 2>&1 || { echo "Jasmin CT check failed"; exit 1; }

# --------------------------------------------------------------------------------------------------

REF_SOURCES := $(wildcard ../*.c) 
SOURCES := test_treehash.c ../common/notrandombytes.c ../common/print.c ../new_treehash/new_xmss.c
TEST_FLAGS := -DTEST_TREEHASH -DTEST_AUTH_PATH -DTEST_TREESIG -DDEBUG

# --------------------------------------------------------------------------------------------------

.PRECIOUS: bin/test_xmssmt-sha2_20_2_256.s
bin/test_xmssmt-sha2_20_2_256.s: test_treehash-sha2_20_2_256.jazz test_treehash.jazz | bin/
	$(JASMIN) $(JINCLUDE) $(JFLAGS) -o $@ $<

bin/test_xmssmt-sha2_20_2_256: bin/test_xmssmt-sha2_20_2_256.s
	$(CC) $(CFLAGS) -o $@ -I../common -I../ -I ../new_treehash/ -DIMPL=XMSSMT-SHA2_20/2_256 $(TEST_FLAGS) \
	$(SOURCES) $(REF_SOURCES) $< $(LDLIBS)

# --------------------------------------------------------------------------------------------------

bin/%.out: bin/%
	@./$<

# --------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	-$(RM) -r bin/

.PHONY: clean_executables
clean_executables:
	find bin/ -type f -executable -delete || true
