# -*- Makefile -*-

# ----------------------------------------------------------------------------------------------------------------------

CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

JASMIN   ?= jasminc
JAZZCT   ?= jazzct
JFLAGS   ?= -nowarning ${JADDFLAGS}
JINCLUDE ?= -I XMSS:../../ref-jasmin/ -I Stdlib:../../ref-jasmin/stdlib

# ----------------------------------------------------------------------------------------------------------------------

default: build

IMPL := sha2_20_2_256
TEST := $(addprefix bin/test_xmss_commons_, $(IMPL))

build: $(TEST)
asm:   $(addsuffix .s, $(TEST))
run:   $(addsuffix .out, $(TEST))


# ----------------------------------------------------------------------------------------------------------------------

REF_SOURCES := $(wildcard ../*.c)

SOURCES := test_xmss_commons.c ../common/notrandombytes.c ../common/print.c

TEST_FLAGS := -DTEST_LTREE -DTEST_COMPUTE_ROOT -DTEST_GEN_LEAF_WOTS # -DTEST_XMSS_CORE_SIGN_OPEN # -DDEBUG

# --------------------------------------------------------------------------------------------------

.PRECIOUS: bin/%.s
bin/%.s: test_xmss_commons.jazz | bin/
	echo "from XMSS require \"params/params-xmssmt-sha2_20_2_256.jinc\"" > tmp
	cat $< >> tmp
	$(JASMIN) $(JINCLUDE) $(JFLAGS) -o $@ tmp
	-$(RM) tmp

$(TEST):
bin/%: bin/%.s | bin/
	$(CC) $(CFLAGS) -o $@ -I../common -I../ -DIMPL=XMSSMT-SHA2_20/2_256 $(TEST_FLAGS) \
	$(SOURCES) $(REF_SOURCES) $< $(LDLIBS)

# --------------------------------------------------------------------------------------------------

bin/%.out: bin/%
	@./$<

# --------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	-$(RM) -r bin/

.PHONY: clean_executables
clean_executables:
	find bin/ -type f -executable -delete || true

