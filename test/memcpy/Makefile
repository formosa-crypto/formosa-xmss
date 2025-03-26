default: build

INLEN_VAL := $(shell seq 10 1024)
TESTS     := $(addprefix bin/memcpy_, $(INLEN_VAL))

build: $(TESTS)
asm: $(addsuffix .s, $(TESTS))
run: $(addsuffix .out, $(TESTS))

bin/: 
	mkdir -p $@ 

bin/memcpy_%.s: memcpy.jazz | bin/
	echo "param int INLEN = $*;" >> tmp_$*
	cat $< >> tmp_$*
	jasminc -o $@ tmp_$*
	-$(RM) tmp_$*

bin/memcpy_%: main.c bin/memcpy_%.s | bin/
	gcc -o $@ -DINLEN=$* -I../common/ ../common/notrandombytes.c ../common/print.c $^ 

%.out: %
	@./$<

.PHONE: clean
clean:
	-$(RM) -r bin/