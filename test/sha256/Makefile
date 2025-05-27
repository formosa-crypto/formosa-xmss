# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

JASMIN   ?= jasminc
JFLAGS   ?= -nowarning ${JADDFLAGS}
JINCLUDE ?= -I XMSS="../../ref-jasmin/"

# --------------------------------------------------------------------------------------------------

INLEN_LIST ?= 1 31 32 33 63 64 65 95 96 97 127 128 129 135 136 137 159 160 \
161 191 192 193 223 224 225 255 256 257 270 271 272

TLIST := $(INLEN_LIST)

TESTS     := $(addprefix bin/test_SHA256_, $(TLIST)) bin/test_sha256_ptr
OUT       := $(addsuffix .out, $(TESTS))
ASM_FILES := $(addsuffix .s, $(TESTS))

# --------------------------------------------------------------------------------------------------

default: $(TESTS)
run: $(OUT)
asm: $(ASM_FILES)

SOURCES := ../common/notrandombytes.c ../common/print.c

# --------------------------------------------------------------------------------------------------

$(ASM_FILES):
.PRECIOUS: bin/%.s
bin/test_SHA256_%.s: test_sha256.jazz | bin/
	echo "param int INLEN = $*;" > tmp_$*
	cat $< >> tmp_$*
	$(JASMIN) $(JINCLUDE) $(JFLAGS) -o $@ tmp_$* || rm tmp_$* # remove the file even when compilation fails
	rm tmp_$*

bin/test_sha256_ptr.s: test_sha256.jazz | bin/
	echo "param int INLEN = 42;" > tmp # placeholder 
	cat $< >> tmp
	$(JASMIN) $(JINCLUDE) $(JFLAGS) -o $@ tmp || rm tmp # remove the file even when compilation fails
	rm tmp


$(TESTS):
bin/test_SHA256_%: bin/test_SHA256_%.s test_sha256.c | bin/
	$(CC) $(CFLAGS) -o $@ -DINLEN=$* -I../common -I../ $^ $(SOURCES) $(LDLIBS)

bin/test_sha256_ptr: bin/test_sha256_ptr.s test_sha256.c | bin/
	$(CC) $(CFLAGS) -o $@ -I../common -I../ $^ $(SOURCES) $(LDLIBS)

$(OUT): 
bin/%.out: bin/%
	@./$<

# --------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	-$(RM) -r bin/ tmp*
