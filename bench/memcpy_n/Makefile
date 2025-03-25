
default: build

asm: bin/memcpy_nbytes.s
build: bin/test_memcpy_nbytes
run: bin/test_memcpy_nbytes.out

bin/memcpy_nbytes.s: memcpy_nbytes.jazz | bin/
	jasminc -o $@ $<

bin/test_memcpy_nbytes: main.c bin/memcpy_nbytes.s
	gcc -o $@ $^

%.out: %
	@./$< 

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	-$(RM) -r bin/
