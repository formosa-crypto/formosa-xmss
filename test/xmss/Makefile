# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

JASMIN   ?= jasminc
JAZZCT   ?= jasmin-ct
JAZZCTFLAGS ?= --infer
JFLAGS   ?= -nowarning ${JADDFLAGS}
JINCLUDE ?= -I XMSS:../../ref-jasmin/ -I Stdlib:../../ref-jasmin/stdlib

JASMINPATH := JASMINPATH="XMSS=../../ref-jasmin/:Stdlib=../../ref-jasmin/stdlib"

# --------------------------------------------------------------------------------------------------

default: test
asm: bin/test_xmssmt-sha2_20_2_256.s
test: bin/test_xmssmt-sha2_20_2_256
run: bin/test_xmssmt-sha2_20_2_256.out

checkCT: test_xmss.jazz
	echo "from XMSS require \"params/params-xmssmt-sha2_20_2_256.jinc\"" > tmp
	cat $< >> tmp
	$(JASMINPATH) $(JAZZCT) $(JAZZCTFLAGS) tmp # >/dev/null 2>&1 #  || { rm tmp ; echo "Jasmin CT check failed"; exit 1; }
	rm tmp

# --------------------------------------------------------------------------------------------------

REF_SOURCES   := $(filter-out ../../submodules/xmss-reference/xmss_core_fast.c ../../submodules/xmss-reference/randombytes.c, $(wildcard ../../submodules/xmss-reference/*.c))
SOURCES := test_xmss.c ../common/notrandombytes.c ../common/print.c

# --------------------------------------------------------------------------------------------------

.PRECIOUS: bin/test_xmssmt-sha2_20_2_256.s
bin/test_xmssmt-sha2_20_2_256.s: test_xmss.jazz | bin/
	echo "from XMSS require \"params/params-xmssmt-sha2_20_2_256.jinc\"" > tmp
	cat $< >> tmp
	$(JASMIN) $(JINCLUDE) $(JFLAGS) -o $@ tmp || rm tmp # remove the file even when compilation fails
	rm tmp

bin/test_xmssmt-sha2_20_2_256: bin/test_xmssmt-sha2_20_2_256.s
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
