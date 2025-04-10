# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

JASMIN   ?= jasminc
JAZZCT   ?= jasmin-ct
JFLAGS   ?= -nowarning ${JADDFLAGS}
JINCLUDE ?= -I XMSS:../../ref-jasmin/ -I Stdlib:../../ref-jasmin/stdlib

# --------------------------------------------------------------------------------------------------

default: test
asm: bin/test_treehash.s
test: bin/test_treehash
run: bin/test_treehash.out

# --------------------------------------------------------------------------------------------------

REF_SOURCES := $(wildcard ../*.c)
SOURCES := test_treehash.c ../common/notrandombytes.c ../common/print.c
TEST_FLAGS := -DTEST_TREEHASH -DTEST_AUTH_PATH -DTEST_TREESIG

# --------------------------------------------------------------------------------------------------

.PRECIOUS: bin/test_treehash.s
bin/test_treehash.s: test_treehash.jazz | bin/
	echo "from XMSS require \"params/params-xmssmt-sha2_20_2_256.jinc\"" > tmp
	cat $< >> tmp
	$(JASMIN) $(JINCLUDE) $(JFLAGS) -o $@ tmp
	-$(RM) tmp

bin/test_treehash: bin/test_treehash.s
	$(CC) $(CFLAGS) -o $@ -I../common -I../ -DIMPL=XMSSMT-SHA2_20/2_256 $(TEST_FLAGS) \
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
