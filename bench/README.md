

- Compile the jasmin implementations

```bash
make -j$(nproc) asm         
```

- Compile the benchmark C files

```bash
make -j$(nproc) build
```

- Run the benchmarks

```
make print_results # printf 'impl;kg;sign;verify\n'; for i in $^; do ./$$i; done
```

- Print results including the object size

```
./print_results.py < $(printf 'impl;kg;sign;verify\n'; for i in $^; do ./$$i; done)
```

- Print the results to a latex table (`-obj_size` flag to also include the object size in the table)

```
./print_results.py -tex [-obj_size] < $(printf 'impl;kg;sign;verify\n'; for i in $^; do ./$$i; done)
```
