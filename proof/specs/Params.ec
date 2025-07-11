require import AllCore List RealExp IntDiv.
require Subtype.

from Jasmin require import JModel.

(* Height of the overall Merkle tree *)
(* XMSS_TREE_HEIGHT in the implementation *)
const h : { int | 0 < h } as h_g0.

(* Length of the digest *)
(* const n : { int | 1 <= n } as ge1_n. *)
(*
  Need that 32 bits fit in n bytes (or toByte(., n) might
  truncate 32-bit index
*)
const n : { int | 4 <= n } as ge4_n.
lemma ge1_n : 1 <= n by smt(ge4_n).

op log2_w : { int | log2_w = 2 \/ log2_w = 4 } as logw_vals.

lemma ge0_log2_w : 0 <= log2_w.
proof.
case (log2_w = 2) => [-> //= | ?]; by have ->: log2_w = 4 by smt(logw_vals).
qed.

(* Winternitz parameter: the range of indices into a wots chain *)
op w : int = 2 ^ log2_w.

lemma w_ilog :
    log2_w = ilog 2 w.
proof.
rewrite /w; case (log2_w = 2) => [-> // | ?].
by have ->: log2_w = 4 by smt(logw_vals).
qed.

lemma logK k:
    1%r < k%r => log k%r k%r = 1%r by smt(@RealExp).

lemma w_vals :
  w = 4 \/ w = 16.
proof. by rewrite /w; case (logw_vals) => ->. qed.

lemma log2w_eq : log2_w%r = log2 w%r.
proof.
rewrite /w /log2; case (log2_w = 2) => [-> /= | ?]; [| have ->: log2_w = 4 by smt(logw_vals)].
- by rewrite (: 4%r = 2%r * 2%r) 1:/# logM 1,2:/# !logK.
- by rewrite /= (: 16%r = 8%r * 2%r) 1:/# logM 1,2:/# (: 8%r = 4%r * 2%r) 1:/# logM 1,2:/# (: 4%r = 2%r * 2%r) 1:/# logM 1,2:/# !logK.
qed.


const len1 : int = ceil ((8 * n)%r / log2 w%r).
const len2 : int = floor (log2 (len1 * (w - 1))%r / log2 w%r) + 1.
const len  : int = len1 + len2.

axiom ge1_h : 1 <= h.
axiom h_max : h < 32. (* Overflows may happen unless h is upper bounded *)
(*
  h should fit in 8 * n,
  so 2 ^ h - 1 can be represented in a block of n bytes,
  as otherwise toByte(idx, n) will discard parts.
*)
axiom len8_h : h <= 8 * n.

lemma ge0_h : 0 <= h by smt(ge1_h).

lemma ge0_len1 : 0 <= len1.
proof.
rewrite /len1 -log2w_eq.
(case (log2_w = 2) => [-> /= | ?]; [| have ->: log2_w = 4 by smt(logw_vals)]; have ? : 16%r <= (8 * n)%r / 2%r by smt(@RealExp ge4_n)); smt(ceil_lt ceil_ge).
qed.

lemma g2_len1 : 2 < len1.
proof.
rewrite /len1 -log2w_eq.
(case (log2_w = 2) => [-> /= | ?]; [| have ->: log2_w = 4 by smt(logw_vals)]; have ? : 16%r <= (8 * n)%r / 2%r by smt(@RealExp ge4_n)); smt(ceil_lt ceil_ge).
qed.

lemma g0_len2 : 0 < len2.
proof.
rewrite /len2 /w.
case (log2_w = 2) => [-> /= | ?]; [| have ->: log2_w = 4 by smt(logw_vals)]; smt(g2_len1 le_ln_dw floor_le floor_gt).
qed.

lemma ge0_len2 : 0 <= len2.
proof. smt(g0_len2). qed.

lemma gt2_len : 2 < len by smt(g2_len1 g0_len2).

lemma ge0_len  : 0 <= len by smt(ge0_len1 gt2_len).

lemma ltW32_len : len < W32.modulus. admitted.

subtype nbytes as NBytes = { l : W8.t list | size l = n}.
realize inhabited.
proof.
by (exists (nseq n W8.zero);smt(size_nseq ge1_n)).
qed.

subtype len_nbytes as LenNBytes = { l : nbytes list | size l = len }.
realize inhabited.
proof.
by (exists (nseq len witness); smt(size_nseq ge0_len)).
qed.

subtype onebyte as OneByte = { l : W8.t list | size l = 1 }.
realize inhabited.
proof.
by (exists (nseq 1 witness); smt(size_nseq)).
qed.

subtype threen_bytes as ThreeNBytesBytes = { l : W8.t list | size l = 3 * n }.
realize inhabited.
proof.
by (exists (nseq (3*n) W8.zero);smt(size_nseq ge1_n)).
qed.
