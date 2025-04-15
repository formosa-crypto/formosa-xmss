# -*- Makefile -*-

CC     := clang-14
CFLAGS := -march=native -O3 -fomit-frame-pointer -fwrapv -Qunused-arguments -fPIC -fPIE
LDLIBS   = -lcrypto

JASMIN   ?= jasminc
JFLAGS   ?= -nowarning ${JADDFLAGS}
JINCLUDE := -I XMSS:../../ref-jasmin -I Stdlib:../../ref-jasmin/stdlib

default: build
asm: bin/xmss.s
build: bin/bench_xmss
run: bin/bench_xmss.out

REF_SOURCES   := $(filter-out ../../submodules/xmss-reference/xmss_core_fast.c, $(wildcard ../../submodules/xmss-reference/*.c)) \
                 ../randombytes/jasmin_syscall.c
BENCH_SOURCES := $(wildcard ../common/*.c)
IDIRS         := -I ../common/ -I ../randombytes -I ../../submodules/xmss-reference/

SOURCES := $(REF_SOURCES) $(BENCH_SOURCES)

bin/xmss.s: xmss.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -o $@ $<

bin/bench_xmss: bin/xmss.s bench_xmss.c 
	$(CC) $(CFLAGS) -DIMPL="XMSSMT-SHA2_20/2_256" -o $@ $(IDIRS) $(SOURCES) $^ $(LDLIBS)

bin/%.out: bin/%
	@./$<

results.txt: bin/bench_xmss
	@./$< 

.PHONY: show_results
show_results: results.txt
	@../scripts/print_results.py

bin/:
	mkdir -p $@ 

.PHONY: clean
clean:
	-$(RM) -r bin/
