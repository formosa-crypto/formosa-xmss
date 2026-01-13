# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------
CC     ?= clang
CFLAGS ?= -fno-omit-frame-pointer -g -O0
LDFLAGS ?= -lcrypto

JASMINC  := /nix/store/bcmvw624ggng7la1jqk9i8brrsra6w3j-jasmin-compiler-2025.06.1-bin/bin/jasminc
JFLAGS   := -nowarning -g ${JADDFLAGS}
JINCLUDE := -I XMSS="../ref-jasmin/" -I Stdlib="../ref-jasmin/stdlib"

# This uses key:value but jasmin uses key=value
JPP_INCLUDE := -I XMSS:"../ref-jasmin/" -I Stdlib:"../ref-jasmin/stdlib"

COMMON := $(filter-out common/jasmin_syscall.c, $(wildcard common/*))

C_SOURCES := ../test/wots.c ../test/hash.c ../test/hash_address.c ../test/utils.c ../test/params.c ../test/fips202.c ../test/xmss_core.c ../test/xmss_commons.c ../test/xmss.c ../test/common/notrandombytes.c ../test/common/print.c 

# --------------------------------------------------------------------------------------------------

JPP_TARGETS := jpp_processed/sha256.jpp jpp_processed/xmss.jpp

# --------------------------------------------------------------------------------------------------

all: symlinks bin/bench_sha256_jasmin bin/bench_wots bin/bench_xmss_jasmin bin/bench_xmss_impl_c bin/bench_xmss_impl_jasmin
run: results/ bin/bench_sha256_jasmin.out bin/bench_xmss.out bin/bench_xmss_impl_c.out bin/bench_xmss_impl_jasmin.out 

process: ${JPP_TARGETS}

# --------------------------------------------------------------------------------------------------

SYMLINK_RULE = ln -sf $< $@

.PHONY: symlinks clean
symlinks: xmss.jazz wots.jazz

# --------------------------------------------------------------------------------------------------
# Setup
# --------------------------------------------------------------------------------------------------

asm/ bin/ results/ jpp_processed/: 
	mkdir -p $@

jpp:
	wget https://raw.githubusercontent.com/formosa-crypto/formosa-25519/cafb7fb534bbecf93b69346788f22c16e662a133/scripts/releaser/jpp \
	&& chmod +x jpp

jpp_processed/xmss.jpp: xmss.jazz | jpp_processed/ jpp

jpp_processed/%.jpp: %.jazz | jpp_processed/ jpp
	cat params.jinc $< > $<.tmp
	./jpp -v $(JPP_INCLUDE) -in $<.tmp -out $@
	-$(RM) $<.tmp
	
asm/sha256.s: sha256.jazz params.jinc | asm/
	{ echo "require \"params.jinc\"" ; cat $< ; } > $<.tmp
	$(JASMINC) $(JINCLUDE) $(JFLAGS) -o $@ $<.tmp
	-$(RM) $<.tmp

asm/wots.s: wots.jazz params.jinc | asm/
	{ echo "require \"params.jinc\"" ; cat $< ; } > $<.tmp
	$(JASMINC) $(JINCLUDE) $(JFLAGS) -o $@ $<.tmp
	-$(RM) $<.tmp

asm/xmss.s: xmss.jazz params.jinc | asm/
	{ echo "require \"params.jinc\"" ; cat $< ; } > $<.tmp
	$(JASMINC) $(JINCLUDE) $(JFLAGS) -o $@ $<.tmp
	-$(RM) $<.tmp

asm/treehash.s: treehash.jazz params.jinc | asm/
	{ echo "require \"params.jinc\"" ; cat $< ; } > $<.tmp
	$(JASMINC) $(JINCLUDE) $(JFLAGS) -o $@ $<.tmp
	-$(RM) $<.tmp

params.jinc: ../ref-jasmin/params/params-xmssmt-sha2_20_2_256.jinc
	$(SYMLINK_RULE)

xmss.jazz: ../ref-jasmin/xmss.jazz
	$(SYMLINK_RULE)

wots.jazz: ../test/wots/test_wots.jazz
	$(SYMLINK_RULE)

treehash.jazz: ../test/treehash/test_treehash.jazz
	$(SYMLINK_RULE)

# --------------------------------------------------------------------------------------------------

bin/bench_sha256_jasmin: bench_sha256_jasmin.c asm/sha256.s | bin/ asm/
	$(CC) $(CFLAGS) -I common -o $@ $^ $(COMMON) $(LDFLAGS)

bin/bench_wots: bench_wots.c asm/wots.s | bin/ asm/
	$(CC) $(CFLAGS) -DBENCH_SHA2 -I common -I ../test -I ../test/common $(C_SOURCES) -o $@ $^ $(COMMON) $(LDFLAGS)

bin/bench_xmss_c: bench_xmss.c | bin/ asm/
	$(CC) $(CFLAGS) -DBENCH_SHA2 -DBENCH_C -I common -I ../test -I ../test/common $(C_SOURCES) -o $@ $^ $(COMMON) $(LDFLAGS)

bin/bench_xmss_jasmin: bench_xmss.c asm/xmss.s asm/sha256.s | bin/ asm/
	$(CC) $(CFLAGS) -DBENCH_SHA2 -DBENCH_JASMIN -I common -I ../test -I ../test/common $(C_SOURCES) -o $@ $^ $(COMMON) $(LDFLAGS)

bin/bench_xmss_impl_c: bench_xmss_impl.c | bin/ asm/
	$(CC) $(CFLAGS) -DBENCH_C -I common -I ../test -I ../test/common $(C_SOURCES) -o $@ $^ $(COMMON) $(LDFLAGS)

bin/bench_xmss_impl_jasmin: bench_xmss_impl.c asm/xmss.s asm/sha256.s | bin/ asm/
	$(CC) $(CFLAGS) -DBENCH_JASMIN -I common -I ../test -I ../test/common $(C_SOURCES) -o $@ $^ $(COMMON) $(LDFLAGS)

bin/bench_treehash_treesig_c: bench_treehash_treesig.c asm/treehash.s | bin/ asm/
	$(CC) $(CFLAGS) -DBENCH_C -DBENCH_TREEHASH_KG -I common -I ../test -I ../test/common $(C_SOURCES) -o $@ $^ $(COMMON) $(LDFLAGS)

bin/bench_treehash_treesig_jasmin: bench_treehash_treesig.c asm/treehash.s | bin/ asm/
	$(CC) $(CFLAGS) -DBENCH_JASMIN -DBENCH_TREEHASH_KG -I common -I ../test -I ../test/common $(C_SOURCES) -o $@ $^ $(COMMON) $(LDFLAGS)

# --------------------------------------------------------------------------------------------------

bin/%.out: bin/%
	@./$<

clean:
	-$(RM) -r asm/ bin/ *.tmp