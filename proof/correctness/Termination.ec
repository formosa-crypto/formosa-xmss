pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import XMSS_IMPL Parameters.

from Jasmin require import JModel.

require import Array67.

(*****************************************************************************************************)
(*** ADDRESS ***)
(*****************************************************************************************************)

lemma zero_addr_ll : islossless M(Syscall).__zero_address_
    by proc ; inline ; wp ; while (true) (8 - i) ; auto => /> /#.

(*****************************************************************************************************)
(*** MEMCPY, MEMSET & MEMCMP ***)
(*****************************************************************************************************)

lemma _x_memcpy_u8u8_32_32_ll : islossless M(Syscall).memcpy_u8u8_N___x_memcpy_u8u8.
proof.
proc; inline*.
auto => />.
while (0 <= to_uint i <= 32) (32 - to_uint i); auto => /> => [&hr | *]; rewrite ultE ?to_uintD /#.
qed.

lemma _x_memcpy_u8u8_64_64_ll : islossless M(Syscall).memcpy_u8u8_2N___x_memcpy_u8u8.
proof.
proc; inline*.
wp.
while (0 <= to_uint i <= 64) (64 - to_uint i); auto => /> => [&hr | *]; rewrite ultE ?to_uintD /#.
qed.

lemma _x_memcpy_u8u8_64_32_ll: islossless M(Syscall).memcpy_u8u8_2N_N___x_memcpy_u8u8.
proof.
proc; inline*.
wp.
while (0 <= to_uint i <= 32) (32 - to_uint i); auto => /> => [&hr | *]; rewrite ultE ?to_uintD /#.
qed.

lemma memcpy_ptr_ll : islossless M(Syscall).__memcpy_u8u8p.
proof.
proc.
while (0 <= i <= 32) (32 - i); auto => /> /#.
qed.

lemma memset_zero_ll : islossless M(Syscall).__memset_zero_u8.
proof.
proc.
do 2! (rcondf 1 => //).
while (0 <= to_uint i <= 4) (4 - to_uint i); auto => /> => [&hr | *]; rewrite ultE ?to_uintD /#.
qed.

lemma memset_4_ll : islossless M(Syscall).memset_idx_bytes____memset_u8.
proof.
proc.
while (0 <= to_uint i <= 3) (3 - to_uint i); auto => /> => [&hr | *]; rewrite ultE ?to_uintD /#.
qed.

lemma memset_128_ll : islossless M(Syscall).memset_i____memset_u8.
proof.
proc.
while (0 <= to_uint i <= 128) (128 - to_uint i); auto => /> => [&hr | *]; rewrite ultE ?to_uintD /#.
qed.
