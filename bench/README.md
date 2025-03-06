

- Compile the jasmin implementations

```bash
make -j$(nproc) asm         
```

- Compile the benchmark C files

```bash
make -j$(nproc) bench_files
```

- Run the benchmarks

```
make run
```

- Print results including the object size

```
./print_results.py < $(make run)
```

- Print the results to a latex table (`-obj_size` flag to also include the object size in the table)

```
./print_results.py -tex [-obj_size] < $(make run)
```
