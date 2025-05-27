# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic

JASMIN   ?= jasminc
JAZZCT   ?= jasmin-ct
JAZZCTFLAGS ?= --infer
JFLAGS   ?= ${JADDFLAGS}
JINCLUDE ?= -I XMSS="../../ref-jasmin/"
JASMINPATH := JASMINPATH="XMSS=../../ref-jasmin/:Stdlib=../../ref-jasmin/stdlib"

# --------------------------------------------------------------------------------------------------

SOURCE_FILES := test_hash_address.c ../../submodules/xmss-reference/hash_address.c \
           ../common/notrandombytes.c ../common/print.c

# --------------------------------------------------------------------------------------------------

default: bin/test_hash_address
run: bin/test_hash_address.out

asm: bin/test_hash_address.s

checkCT: test_hash_address.jazz
	$(JASMINPATH) $(JAZZCT) $(JAZZCTFLAGS) $< >/dev/null 2>&1 || { echo "Jasmin CT check failed"; exit 1; }

# --------------------------------------------------------------------------------------------------

.PRECIOUS: bin/test_hash_address.s
bin/%.s: %.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) $< -o $@

bin/%: bin/%.s | bin/
	$(CC) $(CFLAGS) -o $@ -I../common -I../ $(SOURCE_FILES) $<

bin/%.out: bin/%
	@./$<

# --------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	-$(RM) -r bin/
