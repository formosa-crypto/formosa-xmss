# -*- Makefile -*-

CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

JASMIN   ?= jasminc
JFLAGS   ?= -nowarning ${JADDFLAGS}
JINCLUDE ?= -I XMSS:../../ref-jasmin/ -I Stdlib:../../ref-jasmin/stdlib

ASM := 	bin/test_xmssmt_sha2_20_2_256.s

asm: $(ASM)
jpp: bin/test_xmssmt_sha2_20_2_256.jpp

bin/test_xmssmt_sha2_20_2_256.s: test_xmss.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ $<

bin/test_xmssmt_sha2_20_2_256.jpp: test_xmss.jazz | bin/
	jpp $(JINCLUDE) -out $@ -in $<

bin/: 
	mkdir -p $@

.PHONY: clean
clean:
	-$(RM) -r bin/
