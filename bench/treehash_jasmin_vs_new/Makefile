# -*- Makefile -*-

CC     := clang-14
CFLAGS := -march=native -O3 -fomit-frame-pointer -fwrapv -fPIC -fPIE
LDLIBS = -lcrypto

JASMIN   ?= jasminc
JFLAGS   ?= -nowarning ${JADDFLAGS}
JINCLUDE := -I XMSS:../../ref-jasmin -I Stdlib:../../ref-jasmin/stdlib

default: build
asm: bin/treehash.s
build: bin/bench_treehash
run: bin/bench_treehash.out

REF_SOURCES   := $(filter-out ../../submodules/xmss-reference/xmss_core_fast.c, $(wildcard ../../submodules/xmss-reference/*.c))
BENCH_SOURCES := $(wildcard ../common/*.c)
IDIRS         := -I ../common/ -I ../../submodules/xmss-reference/

SOURCES := $(REF_SOURCES) $(BENCH_SOURCES)

bin/treehash.s: treehash.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ $<

bin/bench_treehash: bin/treehash.s bench_treehash.c 
	$(CC) $(CFLAGS) -o $@ $(IDIRS) $(SOURCES) $^ $(LDLIBS)

bin/%.out: bin/%
	@./$<

results.txt: bin/bench_treehash
	@./$< 

.PHONY: show_results
show_results: results.txt
	@../scripts/print_results.py

bin/:
	mkdir -p $@ 

.PHONY: clean
clean:
	-$(RM) -r bin/
