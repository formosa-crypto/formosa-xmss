# -*- Makefile -*-

CC     := clang-14
CFLAGS := -march=native -O3 -fomit-frame-pointer -fwrapv -Qunused-arguments -fPIC -fPIE
LDLIBS   = -lcrypto

JASMIN   ?= jasminc
JFLAGS   ?= -nowarning ${JADDFLAGS}
JINCLUDE := -I XMSS:../../ref-jasmin -I Stdlib:../../ref-jasmin/stdlib

OBJ := $(patsubst %.s,%.o,$(ASM))

BIN := bin/bench_kg bin/bench_kg_loop bin/bench_kg_unrolled bin/bench_kg_ref \
	  bin/bench_sign bin/bench_sign_loop bin/bench_sign_unrolled bin/bench_sign_ref \
	  bin/bench_verify bin/bench_verify_loop bin/bench_verify_unrolled bin/bench_verify_ref

OUT := $(addsuffix .out, $(BIN))

default: build
build: $(BIN)
asm: $(ASM)
run: $(OUT)

REF_SOURCES   := $(filter-out ../../submodules/xmss-reference/xmss_core_fast.c, $(wildcard ../../submodules/xmss-reference/*.c))
BENCH_SOURCES := $(wildcard ../common/*.c)
IDIRS         := -I ../common/ -I ../../submodules/xmss-reference/

SOURCES := $(REF_SOURCES) $(BENCH_SOURCES)

bin/xmss.s: xmss.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ $<

bin/xmss_loop_u64.s: xmss.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -stack-zero loop -stack-zero-size u64 -o $@ $< 

bin/xmss_unrolled_u64.s: xmss.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -stack-zero unrolled -stack-zero-size u64 -o $@ $< 

bin/bench_xmss: bin/xmss.s bench_xmss.c 
	$(CC) $(CFLAGS) -o $@ $(IDIRS) $(SOURCES) $^ $(LDLIBS)

bin/bench_%: bench_%.c bin/xmss.s
	$(CC) $(CFLAGS) -o $@ $(IDIRS) -DOUTPUT_FILE=results.csv -DJASMIN_BASE $(SOURCES) $^ $(LDLIBS)

bin/bench_%_ref: bench_%.c
	$(CC) $(CFLAGS) -o $@ $(IDIRS) -DOUTPUT_FILE=results.csv -DREF $(SOURCES) $^ $(LDLIBS)

bin/bench_%_loop: bench_%.c bin/xmss_loop_u64.s
	$(CC) $(CFLAGS) -o $@ $(IDIRS) -DOUTPUT_FILE=results.csv -DLOOP $(SOURCES) $^ $(LDLIBS)

bin/bench_%_unrolled: bench_%.c bin/xmss_unrolled_u64.s
	$(CC) $(CFLAGS) -o $@ $(IDIRS) -DOUTPUT_FILE=results.csv -DUNROLLED $(SOURCES) $^ $(LDLIBS)


bin/%.out: bin/%  
	@./$<

bin/:
	mkdir -p $@ 

.PHONY: clean
clean:
	-$(RM) -r bin/ 
