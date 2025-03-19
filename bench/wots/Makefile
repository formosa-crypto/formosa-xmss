# -*- Makefile -*-

CC     := clang-14
CFLAGS := -march=native -O3 -fomit-frame-pointer -fwrapv -Qunused-arguments -fPIC -fPIE
LDLIBS   = -lcrypto

JASMIN   ?= jasminc
JFLAGS   ?= -nowarning ${JADDFLAGS}
JINCLUDE := -I XMSS:../../ref-jasmin -I Stdlib:../../ref-jasmin/stdlib

default: build
asm: bin/wots.s
build: bin/bench_wots
run: bin/bench_wots.out

REF_SOURCES   := $(filter-out ../../submodules/xmss-reference/xmss_core_fast.c ../../submodules/xmss-reference/wots.c, $(wildcard ../../submodules/xmss-reference/*.c))
BENCH_SOURCES := $(wildcard ../common/*.c)
IDIRS         := -I ../common/ -I ../../submodules/xmss-reference/

SOURCES := $(REF_SOURCES) $(BENCH_SOURCES)

bin/wots.s: wots.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ $<

bin/bench_wots: bin/wots.s bench_wots.c 
	$(CC) $(CFLAGS) -o $@ $(IDIRS) $(SOURCES) $^ $(LDLIBS)

bin/%.out: bin/%
	@./$<

results.txt: bin/bench_wots
	@./$< 

.PHONY: show_results
show_results: results.txt
	@./print_results.py

bin/:
	mkdir -p $@ 

.PHONY: clean
clean:
	-$(RM) -r bin/
