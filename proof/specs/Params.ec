require import AllCore List RealExp IntDiv.
require Subtype.

from Jasmin require import JModel.

(* Height of the overall Merkle tree *)
(* XMSS_TREE_HEIGHT in the implementation *)
const h : { int | 0 < h } as h_g0.

(* Length of the digest *)
const n : { int | 1 <= n } as ge1_n.

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

lemma w_vals :
  w = 4 \/ w = 16.
proof. by rewrite /w; case (logw_vals) => ->. qed.

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

(* TODO: Why are these axioms? *)
lemma ge0_len  : 0 <= len. admitted.
lemma ge0_len1 : 0 <= len1. admitted.

lemma gt2_len : 2 < len. admitted.

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

