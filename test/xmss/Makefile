# -*- Makefile -*-

CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

JASMIN   ?= jasminc
JFLAGS   ?= -nowarning ${JADDFLAGS}
JINCLUDE ?= -I XMSS:../../ref-jasmin/ -I Stdlib:../../ref-jasmin/stdlib

ASM := 	bin/test_xmssmt_sha2_20_2_256.s

asm: $(ASM)

bin/test_xmssmt_sha2_20_2_256.s: test_xmss.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ $<

bin/: 
	mkdir -p $@

.PHONY: clean
clean:
	-$(RM) -r bin/
