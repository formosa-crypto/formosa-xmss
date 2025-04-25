#- * - Makefile - * -

AS     := as
CC     := clang-14
CFLAGS := -march=native -O3 -fomit-frame-pointer -fwrapv -fPIC -fPIE
LDLIBS = -lcrypto

JASMIN   ?= jasminc
JFLAGS   ?= -nowarning ${JADDFLAGS}
JINCLUDE := -I XMSS:../../ref-jasmin -I Stdlib:../../ref-jasmin/stdlib

word_sizes := u8 u16 u32 u64 u128 u256
zeroization_strategies := loop unrolled

default: build

ASM := $(foreach size, $(word_sizes), \
        $(foreach strategy, $(zeroization_strategies), \
            bin/hash_$(strategy)_$(size).s))

OBJ := $(patsubst %.s,%.o,$(ASM))

BIN := $(foreach size, $(word_sizes), \
        $(foreach strategy, $(zeroization_strategies), \
            bin/bench_hash_$(strategy)_$(size)))

OUT := $(addsuffix .out, $(BIN))

build: $(BIN)
asm: $(ASM)
obj: $(OBJ)
run: $(OUT)

REF_SOURCES   := $(filter-out ../../submodules/xmss-reference/xmss_core_fast.c, $(wildcard ../../submodules/xmss-reference/*.c))
BENCH_SOURCES := $(wildcard ../common/*.c)
IDIRS         := -I ../common/ -I ../../submodules/xmss-reference/

SOURCES := $(REF_SOURCES) $(BENCH_SOURCES)

bin/%.o: bin/%.s
	$(AS) -o $@ $<

bin/hash.s: hash.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ $<

bin/hash_loop_u8.s: hash.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -stack-zero loop -stack-zero-size u8 -o $@ $< 

bin/hash_unrolled_u8.s: hash.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -stack-zero unrolled -stack-zero-size u8 -o $@ $< 

bin/hash_loop_u16.s: hash.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -stack-zero loop -stack-zero-size u16 -o $@ $< 

bin/hash_unrolled_u16.s: hash.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -stack-zero unrolled -stack-zero-size u16 -o $@ $< 

bin/hash_loop_u32.s: hash.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -stack-zero loop -stack-zero-size u32 -o $@ $< 

bin/hash_unrolled_u32.s: hash.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -stack-zero unrolled -stack-zero-size u32 -o $@ $< 

bin/hash_loop_u64.s: hash.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -stack-zero loop -stack-zero-size u64 -o $@ $< 

bin/hash_unrolled_u64.s: hash.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -stack-zero unrolled -stack-zero-size u64 -o $@ $< 

bin/hash_loop_u128.s: hash.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -stack-zero loop -stack-zero-size u128 -o $@ $< 

bin/hash_unrolled_u128.s: hash.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -stack-zero unrolled -stack-zero-size u128 -o $@ $< 

bin/hash_loop_u256.s: hash.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -stack-zero loop -stack-zero-size u256 -o $@ $< 

bin/hash_unrolled_u256.s: hash.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -stack-zero unrolled -stack-zero-size u256 -o $@ $< 

bin/bench_hash: bin/hash.s bench_hash.c 
	$(CC) $(CFLAGS) -o $@ $(IDIRS) $(SOURCES) $^ $(LDLIBS)

bin/bench_hash_loop_u8: bin/hash_loop_u8.s bench_hash.c
	$(CC) $(CFLAGS) -o $@ $(IDIRS) -DZEROIZATION_STRATEGY=loop -DZEROIZATION_SIZE=u8 -DFILENAME=results_loop_u8.txt $(SOURCES) $^ $(LDLIBS)

bin/bench_hash_unrolled_u8: bin/hash_unrolled_u8.s bench_hash.c
	$(CC) $(CFLAGS) -o $@ $(IDIRS) -DZEROIZATION_STRATEGY=unrolled -DZEROIZATION_SIZE=u8 -DFILENAME=results_unrolled_u8.txt $(SOURCES) $^ $(LDLIBS)

bin/bench_hash_loop_u16: bin/hash_loop_u16.s bench_hash.c
	$(CC) $(CFLAGS) -o $@ $(IDIRS) -DZEROIZATION_STRATEGY=loop -DZEROIZATION_SIZE=u16 -DFILENAME=results_loop_u16.txt $(SOURCES) $^ $(LDLIBS)

bin/bench_hash_unrolled_u16: bin/hash_unrolled_u16.s bench_hash.c
	$(CC) $(CFLAGS) -o $@ $(IDIRS) -DZEROIZATION_STRATEGY=unrolled -DZEROIZATION_SIZE=u16 -DFILENAME=results_unrolled_u16.txt $(SOURCES) $^ $(LDLIBS)

bin/bench_hash_loop_u32: bin/hash_loop_u32.s bench_hash.c
	$(CC) $(CFLAGS) -o $@ $(IDIRS) -DZEROIZATION_STRATEGY=loop -DZEROIZATION_SIZE=u32 -DFILENAME=results_loop_u32.txt $(SOURCES) $^ $(LDLIBS)

bin/bench_hash_unrolled_u32: bin/hash_unrolled_u32.s bench_hash.c
	$(CC) $(CFLAGS) -o $@ $(IDIRS) -DZEROIZATION_STRATEGY=unrolled -DZEROIZATION_SIZE=u32 -DFILENAME=results_unrolled_u32.txt $(SOURCES) $^ $(LDLIBS)

bin/bench_hash_loop_u64: bin/hash_loop_u64.s bench_hash.c
	$(CC) $(CFLAGS) -o $@ $(IDIRS) -DZEROIZATION_STRATEGY=loop -DZEROIZATION_SIZE=u64 -DFILENAME=results_loop_u64.txt $(SOURCES) $^ $(LDLIBS)

bin/bench_hash_unrolled_u64: bin/hash_unrolled_u64.s bench_hash.c
	$(CC) $(CFLAGS) -o $@ $(IDIRS) -DZEROIZATION_STRATEGY=unrolled -DZEROIZATION_SIZE=u64 -DFILENAME=results_unrolled_u64.txt $(SOURCES) $^ $(LDLIBS)

bin/bench_hash_loop_u128: bin/hash_loop_u128.s bench_hash.c
	$(CC) $(CFLAGS) -o $@ $(IDIRS) -DZEROIZATION_STRATEGY=loop -DZEROIZATION_SIZE=u128 -DFILENAME=results_loop_u128.txt $(SOURCES) $^ $(LDLIBS)

bin/bench_hash_unrolled_u128: bin/hash_unrolled_u128.s bench_hash.c
	$(CC) $(CFLAGS) -o $@ $(IDIRS) -DZEROIZATION_STRATEGY=unrolled -DZEROIZATION_SIZE=u128 -DFILENAME=results_unrolled_u128.txt $(SOURCES) $^ $(LDLIBS)

bin/bench_hash_loop_u256: bin/hash_loop_u256.s bench_hash.c
	$(CC) $(CFLAGS) -o $@ $(IDIRS) -DZEROIZATION_STRATEGY=loop -DZEROIZATION_SIZE=u256 -DFILENAME=results_loop_u256.txt $(SOURCES) $^ $(LDLIBS)

bin/bench_hash_unrolled_u256: bin/hash_unrolled_u256.s bench_hash.c
	$(CC) $(CFLAGS) -o $@ $(IDIRS) -DZEROIZATION_STRATEGY=unrolled -DZEROIZATION_SIZE=u256 -DFILENAME=results_unrolled_u256.txt $(SOURCES) $^ $(LDLIBS)

bin/%.out: bin/%
	@./$<

results.txt: 
	awk 'NR==1 || $$0 != "Function;Average;Median"' *.txt > $@

.PHONY: show_results show_object_size
show_results: results.txt
	@../scripts/print_results.py

show_object_size: $(OBJ)
	@../scripts/print_object_size.py "bin/"

bin/:
	mkdir -p $@ 

.PHONY: clean
clean:
	-$(RM) -r bin/
