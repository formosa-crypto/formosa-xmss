# -*- Makefile -*-

JASMIN   ?= jasminc
JFLAGS   ?= -nowarning ${JADDFLAGS}
JINCLUDE := -I XMSS:../ref-jasmin -I Stdlib:../ref-jasmin/stdlib

CC     := clang-14
CFLAGS := -march=native -O3 -fomit-frame-pointer -fwrapv -Qunused-arguments -fPIC -fPIE
AS     ?= as

########################################################################################################################

# ASM := 	bin/bench_xmssmt_sha2_20_2_256.s \
# 		bin/bench_xmssmt_sha2_20_2_256_loop_u8.s \
# 		bin/bench_xmssmt_sha2_20_2_256_loop_u16.s \
# 		bin/bench_xmssmt_sha2_20_2_256_loop_u32.s \
# 		bin/bench_xmssmt_sha2_20_2_256_loop_u64.s \
# 		bin/bench_xmssmt_sha2_20_2_256_loop_u128.s \
# 		bin/bench_xmssmt_sha2_20_2_256_loop_u256.s \
# 		bin/bench_xmssmt_sha2_20_2_256_unrolled_u8.s \
# 		bin/bench_xmssmt_sha2_20_2_256_unrolled_u16.s \
# 		bin/bench_xmssmt_sha2_20_2_256_unrolled_u32.s \
# 		bin/bench_xmssmt_sha2_20_2_256_unrolled_u64.s \
# 		bin/bench_xmssmt_sha2_20_2_256_unrolled_u128.s \
# 		bin/bench_xmssmt_sha2_20_2_256_unrolled_u256.s

ASM := 	bin/bench_xmssmt_sha2_20_2_256.s \
		bin/bench_xmssmt_sha2_20_2_256_loop_u64.s \
		bin/bench_xmssmt_sha2_20_2_256_unrolled_u64.s \

BIN := $(ASM:.s=)
OUT := $(BIN:=.out)

########################################################################################################################

asm: $(ASM)
bin: $(BIN)
run: $(OUT)

########################################################################################################################

SOURCE_FILES := $(wildcard ./common/*.c) $(wildcard ./randombytes/*.c)
REF_FILES    := $(filter-out ../submodules/xmss-reference/randombytes.c ../submodules/xmss-reference/xmss_core_fast.c, $(wildcard ../submodules/xmss-reference/*.c)) 

########################################################################################################################

bin/bench_xmssmt_sha2_20_2_256.s: jasmin/xmss.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ $<

bin/bench_xmssmt_sha2_20_2_256_loop_u8.s: jasmin/xmss.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ -stack-zero loop -stack-zero-size u8 $<

bin/bench_xmssmt_sha2_20_2_256_loop_u16.s: jasmin/xmss.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ -stack-zero loop -stack-zero-size u16 $<

bin/bench_xmssmt_sha2_20_2_256_loop_u32.s: jasmin/xmss.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ -stack-zero loop -stack-zero-size u32 $<

bin/bench_xmssmt_sha2_20_2_256_loop_u64.s: jasmin/xmss.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ -stack-zero loop -stack-zero-size u64 $<

bin/bench_xmssmt_sha2_20_2_256_loop_u128.s: jasmin/xmss.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ -stack-zero loop -stack-zero-size u128 $<

bin/bench_xmssmt_sha2_20_2_256_loop_u256.s: jasmin/xmss.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ -stack-zero loop -stack-zero-size u256 $<

bin/bench_xmssmt_sha2_20_2_256_unrolled_u8.s: jasmin/xmss.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ -stack-zero unrolled -stack-zero-size u8 $<

bin/bench_xmssmt_sha2_20_2_256_unrolled_u16.s: jasmin/xmss.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ -stack-zero unrolled -stack-zero-size u16 $<

bin/bench_xmssmt_sha2_20_2_256_unrolled_u32.s: jasmin/xmss.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ -stack-zero unrolled -stack-zero-size u32 $<

bin/bench_xmssmt_sha2_20_2_256_unrolled_u64.s: jasmin/xmss.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ -stack-zero unrolled -stack-zero-size u64 $<

bin/bench_xmssmt_sha2_20_2_256_unrolled_u128.s: jasmin/xmss.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ -stack-zero unrolled -stack-zero-size u128 $<

bin/bench_xmssmt_sha2_20_2_256_unrolled_u256.s: jasmin/xmss.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ -stack-zero unrolled -stack-zero-size u256 $<

########################################################################################################################

bin/bench_xmssmt_sha2_20_2_256_ref: bench_ref.c | bin/
   $(CC) $(CFLAGS) -o $@ -I./common/ -I./randombytes/ -I../submodules/xmss-reference/ -DIMPL=\"XMSSMT-SHA2_20/2_256\" \
   $(SOURCE_FILES) $(REF_FILES)  $< -lcrypto

bin/bench_xmssmt_sha2_20_2_256_loop_u64: bench_jasmin.c  bin/bench_xmssmt_sha2_20_2_256_loop_u64.s | bin/
   $(CC) $(CFLAGS) -o $@ -I./common/ -I./randombytes/ -I../submodules/xmss-reference/ -DSTACK_ZERO="loop" -DSTACK_ZERO_SIZE="u64" -DIMPL=XMSSMT-SHA2_20/2_256 $(SOURCE_FILES) $<

bin/bench_xmssmt_sha2_20_2_256_unrolled_u64: bench_jasmin.c  bin/bench_xmssmt_sha2_20_2_256_unrolled_u64.s | bin/
   $(CC) $(CFLAGS) -o $@ -I./common/ -I./randombytes/ -I../submodules/xmss-reference/ -DSTACK_ZERO="unrolled" -DSTACK_ZERO_SIZE="u64" -DIMPL=XMSSMT-SHA2_20/2_256 $(SOURCE_FILES) $<

########################################################################################################################

.PHONY: print_results
print_results:
	printf 'foo\n'


########################################################################################################################

bin/%.out: bin/%
	@./$<

########################################################################################################################

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	-$(RM) -r bin/ 

.PHONY: clean_binary
clean_binary:
	find bin/ -type f -executable -delete
