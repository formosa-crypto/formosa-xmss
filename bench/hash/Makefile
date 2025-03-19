# -*- Makefile -*-

CC     := clang-14
CFLAGS := -march=native -O3 -fomit-frame-pointer -fwrapv -Qunused-arguments -fPIC -fPIE
LDLIBS   = -lcrypto

JASMIN   ?= jasminc
JFLAGS   ?= -nowarning ${JADDFLAGS}
JINCLUDE := -I XMSS:../../ref-jasmin -I Stdlib:../../ref-jasmin/stdlib

default: build
asm: bin/hash.s
build: bin/bench_hash
run: bin/bench_hash.out

REF_SOURCES   := $(filter-out ../../submodules/xmss-reference/xmss_core_fast.c, $(wildcard ../../submodules/xmss-reference/*.c))
BENCH_SOURCES := $(wildcard ../common/*.c)
IDIRS         := -I ../common/ -I ../../submodules/xmss-reference/

SOURCES := $(REF_SOURCES) $(BENCH_SOURCES)

bin/hash.s: hash.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ $<

bin/bench_hash: bin/hash.s bench_hash.c 
	$(CC) $(CFLAGS) -o $@ $(IDIRS) $(SOURCES) $^ $(LDLIBS)

bin/%.out: bin/%
	@./$<

results.txt: bin/bench_hash
	@./$< 

.PHONY: show_results
show_results: results.txt
	@./print_results.py

bin/:
	mkdir -p $@ 

.PHONY: clean
clean:
	-$(RM) -r bin/
