# Tool Dependencies

This project currently uses the following tool versions:

 - EasyCrypt: f8fab1dc5541a84b416df172522809efe8419c37
 - Jasmin & ECLib: release-2025.06
 - A recent C compiler (for building the test)
 - Valgrind (for running the valgrind test)

# Working with Docker

We provide a Docker image that includes all required dependencies.
The docker can be built under Linux-x64 or MacOS-Silicon.

To build it, run:

    make docker

This command creates a ready-to-use Docker image and copies the
contents of this archive into the container.

To enter the Docker container, run:

    make run-docker

This will start an interactive shell inside the container. The
working directory will contain a copy of this archive.

# Running the EasyCrypt security & correctness proofs

To check the proofs, run:

    make -C proof

# Running the test-suite / valgrind memory checker / bench

All the tests must be ran on an x64 architecture.

## Running the test-suite

To run the tests, run:

    make -C test/{subdir} run

where `{subdir}` is one of:

 - `sha256`: runs the tests for the SHA-256 implementation.
 - `hash`: runs the tests for THASH and other hash-based operations
 - `hash_address`: runs the tests for operations on addresses
 - `wots`: runs the tests for WOTS+
 - `treehash`: runs the tests for Treehash (Jasmin implementation)
 - `new_treehash`: runs the tests for a C implementation of Treehash matching the RFC
 - `xmss`: runs the tests for XMSS

## Running Valgrind on the implementation

You can check for memory issues with Valgrind by running:

    make -C test/xmss/ check_valgrind

## Running the benchmarks

You can run the benchmarks by running (all benchmarks refer to the
XMSSMT-SHA2_20/2_256 parameter set):

    make -C bench/ {target}.out

where `{target}` is one of:

- `bin/bench_sha256_jasmin`: Benchmarks Jasmin implementation of
  SHA-2 against OpenSSL, for input sizes of 32 and 64 bytes. The
  results are written to the files:

  - `results/sha256_jasmin_ptr.txt`
  - `results/sha256_jasmin_32.txt`
  - `results/sha256_jasmin_64.txt`
  - `results/sha256_openssl_32.txt`
  - `results/sha256_openssl_64.txt`

- `bin/bench_wots`: Benchmarks the Jasmin and C implementations of WOTS+.
  The results are written to the files:

  - `results/expand_seed_jazz.txt`
  - `results/wots_checksum_jazz.txt`
  - `results/gen_chain_jazz.txt`
  - `results/wots_pkgen_jazz.txt`
  - `results/wots_sign_jazz.txt`
  - `results/wots_pk_from_sig_jazz.txt`
  - `results/expand_seed_c.txt`
  - `results/wots_checksum_c.txt`
  - `results/gen_chain_c.txt`
  - `results/wots_pkgen_c.txt`
  - `results/wots_sign_c.txt`
  - `results/wots_pk_from_sig_c.txt`

- `bin/bench_sha2_in_xmss_c`: Benchmarks cycles consumed by SHA-256
  (C implementation using OpenSSL SHA-2). Results are written to file:

  - `results/bench_xmss_sha2_calls_c.csv`

- `bin/bench_sha2_in_xmss_jasmin`: Benchmarks cycles consumed by SHA-256
  (C implementation using Jasmin's SHA-2). The difference from
  `bin/bench_sha2_in_xmss_c` is that this version uses Jasmin's optimized
  assembly implementations. Results are written to the file:

  - `results/bench_xmss_sha2_calls_jasmin.csv`

- `bin/bench_xmss_impl_c`: Benchmarks the three XMSS-MT API operations:
  key generation,  signature generation and verification for the C reference
  implementation. Results are written to the files:

  - `results/bench_keygen_c.txt`
  - `results/bench_sign_c.txt`
  - `results/bench_verify_c.txt`

- `bin/bench_xmss_impl_jasmin`: Benchmarks the three XMSS-MT API
  operations: key generation, signature generation and verification for the
  Jasmin implementation (without zeroization). Results are written to
  the files:

  - `results/bench_keygen_jasmin.txt`
  - `results/bench_sign_jasmin.txt`
  - `results/bench_verify_jasmin.txt`

- `bin/bench_xmss_impl_jasmin_zero_loop`: Benchmarks the three XMSS-MT API
  operations: key generation, signature generation and verification for
  the Jasmin implementation with loop-based zeroization. Results are written
  to the files

  - `results/bench_keygen_jasmin_zero_loop.txt`
  - `results/bench_sign_jasmin_zero_loop.txt`
  - `results/bench_verify_jasmin_zero_loop.txt`

- `bin/bench_xmss_impl_jasmin_zero_unroll`: Benchmarks the three XMSS-MT API
  operations: key generation, signature generation and verification for the
  Jasmin implementation with unrolled zeroization. Results are written
  to the files:

  - `results/bench_keygen_jasmin_zero_unroll.txt`
  - `results/bench_sign_jasmin_zero_unroll.txt`
  - `results/bench_verify_jasmin_zero_unroll.txt`

- `bin/bench_treehash_c`: Benchmarks the Treehash algorithm for the C
  reference implementation. Results are written to the file:

  - `results/bench_treehash_c.txt`

- `bin/bench_treehash_jasmin`: Benchmarks the Treehash algorithm for the
  Jasmin implementation. Results are written to the file:

  - `results/bench_treehash_jasmin.txt`

## Code size

You can see the code size for each of the jasmin implementations by running:

    make -C bench/ show_code_size
