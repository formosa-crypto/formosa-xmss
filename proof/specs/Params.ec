require import AllCore List RealExp IntDiv.
require Subtype.

from Jasmin require import JModel.

(* Height of the overall Merkle tree *)
(* XMSS_TREE_HEIGHT in the implementation *)
const h : { int | 0 < h } as h_g0.

(* Maximum number of message bytes *)
const mmb : { int | 1 <= mmb } as ge1_mmb.

(* Length of the digest *)
(*
  Need that 32 bits fit in n bytes (or toByte(., n) might
  truncate 32-bit index
*)
const n : { int | 4 <= n } as ge4_n.

lemma ge1_n : 1 <= n by smt(ge4_n).

op log2_w : { int | log2_w = 2 \/ log2_w = 4 } as logw_vals.

axiom n_lt_2X32: n < 2 ^ (30 - 2 * log2_w).

(* n needs to be such that len fits in 32 bits *)
lemma len32b_n : n <= 954437175.
proof.
apply (StdOrder.IntOrder.ler_trans (2 ^ (30 - 2 * log2_w))); 1: smt(n_lt_2X32).
by case: logw_vals => -> /=.
qed.

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

axiom divisibility_condition: !8 %| len2 * log2_w.

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

lemma eqi_log22i i :
  1 <= i => log 2%r (2%r ^ i) = i%r.
proof.
move => ge1_i; have ge0_i : 0 <= i by smt().
elim: i ge0_i ge1_i => [/#| i ge0_i ih i1].
case (i = 0) => [-> /=|]; 1: by rewrite RField.expr1 logK //.
move=> neqi1; rewrite RField.exprD_nneg 1,2:// logM 1,2:StdOrder.RealOrder.expr_gt0 1,2://.
by rewrite RField.expr1 logK // fromintD /#.
qed.

lemma ltW32_len : len < W32.modulus.
proof.
rewrite /len /len2 /len1 -log2w_eq /w.
case (logw_vals) => -> /=.
+ rewrite -fromint_div 1:dvdz_mulr // mulrC divMr 1:// /= -lt_fromint fromintD.
  apply (StdOrder.RealOrder.ltr_le_trans ((n * 4 + 1)%r + ((log2 (ceil (n * 4)%r * 3)%r / 2%r) + 1%r))).
  rewrite &(StdOrder.RealOrder.ltr_le_add) 1,2:fromintD 1:ceil_lt StdOrder.RealOrder.ler_add 1:floor_le 1://.
  rewrite fromintM /log2 logM 2:// /= 2:RField.mulrDl; 1: smt(ceil_ge ge4_n).
  have ltceil1 : log 2%r (ceil (n * 4)%r)%r < log 2%r (n * 4 + 1)%r.
  + rewrite log_mono_ltr 1:// 1:(StdOrder.RealOrder.ltr_le_trans (n * 4)%r) 1,3:lt_fromint 2:ceil_ge; 1,2: smt(ge1_n).
    by rewrite fromintD ceil_lt.
  have lt2log3 : log 2%r 3%r < 2%r.
  + by rewrite {2}(: 2%r = log 2%r (2%r ^ 2)) 2:RField.expr2 2:log_mono_ltr; 1:smt(@RealExp).
  rewrite (StdOrder.RealOrder.ler_trans ((n * 4 + 1)%r + (log 2%r (n * 4 + 1)%r / 2%r + 2%r))) 1:/#.
  rewrite RField.addrA -StdOrder.RealOrder.ler_subr_addr /=.
  have lei1_logi41: forall i, 4 <= i => log 2%r (i * 4 + 1)%r <= log 2%r (2%r ^ (i + 1)).
  + move => i ge4_i.
    rewrite log_mono 1:// 1:lt_fromint 1:/# 1:StdOrder.RealOrder.expr_gt0 1://.
    have ge0_i: 0 <= i by smt().
    elim: i ge0_i ge4_i => [/#| i ge0_i ih ge4_i1].
    rewrite mulrDl RField.exprD_nneg 1:/# 1:// /= (: 5 = 1 + 4) 1:// addrA fromintD.
    rewrite RField.expr1 /= (: 2%r ^ (i + 1) * 2%r = 2%r ^ (i + 1) + 2%r ^ (i + 1)) 1:/#.
    case (i = 3) => [-> /=| ineq2]; 1:smt(@RField).
    by rewrite StdOrder.RealOrder.ler_add 1:// 1:ih; smt(@StdOrder.RealOrder).
  rewrite -(StdOrder.RealOrder.ler_pmul2l 2%r) 1:// /= RField.mulrDr /=.
  rewrite -(RField.mulrC (inv 2%r)) RField.mulrA /= fromintD fromintM.
  rewrite (StdOrder.RealOrder.ler_trans (4%r * (n%r * 2%r + 1%r) + (n + 1)%r)).
  + by rewrite StdOrder.RealOrder.ler_add 1://; 1,2: smt(ge4_n eqi_log22i).
  rewrite (StdOrder.RealOrder.ler_trans (9%r * n%r + 13%r)) 1:/#.
  rewrite -(StdOrder.RealOrder.ler_subr_addr) -StdOrder.RealOrder.ler_pdivl_mull 1:// /=.
  by rewrite le_fromint len32b_n.
rewrite -fromint_div 1:dvdz_mulr // mulrC divMr 1:// /= 1:-lt_fromint fromintD.
apply (StdOrder.RealOrder.ltr_le_trans ((n * 2 + 1)%r + ((log2 (ceil (n * 2)%r * 15)%r / 4%r) + 1%r))).
rewrite &(StdOrder.RealOrder.ltr_le_add) 1,2:fromintD 1:ceil_lt StdOrder.RealOrder.ler_add 1:floor_le 1://.
rewrite fromintM /log2 logM 2:// /= 2:RField.mulrDl; 1:smt(ceil_ge ge4_n @Real).
have ltceil1 : log 2%r (ceil (n * 2)%r)%r < log 2%r (n * 2 + 1)%r.
+ rewrite log_mono_ltr 1:// 1:(StdOrder.RealOrder.ltr_le_trans (n * 2)%r) 1,3:lt_fromint 2:ceil_ge; 1,2: smt(ge1_n).
  by rewrite fromintD ceil_lt.
have lt4log15 : log 2%r 15%r < 4%r.
+ rewrite (: 4%r = log 2%r (2%r ^ 4)); 1: smt(@RealExp).
  by rewrite (: 4 = 2 + 2) 1:// (RField.exprD_nneg 2%r 2 2) 1,2:// RField.expr2 log_mono_ltr.
rewrite (StdOrder.RealOrder.ler_trans ((n * 2 + 1)%r + (log 2%r (n * 2 + 1)%r / 4%r + 2%r))) 1:/#.
rewrite RField.addrA -StdOrder.RealOrder.ler_subr_addr /=.
have lei1_logi31 : forall i, 3 <= i => log 2%r (i * 2 + 1)%r <= log 2%r (2%r ^ i).
+ move => i ge3_i.
  rewrite log_mono 1:// 1:lt_fromint 1:/# 1:StdOrder.RealOrder.expr_gt0 1://.
  have ge0_i: 0 <= i by smt().
  elim: i ge0_i ge3_i => [/#| i ge0_i ih ge3_i1].
  rewrite mulrDl /= RField.exprD_nneg 1,2:// (: 3 = 1 + 2) 1:// addrA fromintD.
  rewrite RField.expr1 (: 2%r ^ i * 2%r = 2%r ^ i + 2%r ^ i) 1:/#.
  case (i = 2) => [-> /=| ineq2]; 1: smt(@RField).
  by rewrite StdOrder.RealOrder.ler_add 1:// 1:ih; smt(@StdOrder.RealOrder).
rewrite -(StdOrder.RealOrder.ler_pmul2l 4%r) 1:// /= RField.mulrDr /=.
rewrite -(RField.mulrC (inv 4%r)) RField.mulrA /= fromintD fromintM.
rewrite (StdOrder.RealOrder.ler_trans (4%r * (n%r * 2%r + 1%r) + n%r)).
+ rewrite StdOrder.RealOrder.ler_add 1://; 1: smt(ge4_n eqi_log22i).
rewrite (StdOrder.RealOrder.ler_trans (9%r * n%r + 4%r)) 1:/#.
rewrite (StdOrder.RealOrder.ler_trans (9%r * n%r + 8%r)) 1:/#.
by rewrite -(StdOrder.RealOrder.ler_subr_addr) /= -StdOrder.RealOrder.ler_pdivl_mull 1://; smt(len32b_n).
qed.

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
