(* --- Require/Import --- *)
require import AllCore IntDiv List StdOrder.
require (*--*) Subtype.
(*---*) import IntOrder.



(* --- Checksum (slightly more generic than necessary, instantiated below) --- *)
(* --- WOTS-TW with checksum --- *)
(* -- Require/Import -- *)
require import RealExp BitEncoding.
require Word.
import RField BS2Int.
require WOTS_TW Checksum.


(* -- Parameters (copied from WOTS-TW.ec) -- *)
(* Base 2 logarithm of the Winternitz parameter w *)
const log2_w : { int | log2_w = 2 \/ log2_w = 4 \/ log2_w = 8 } as val_log2w.

(* Winternitz parameter (base/radix) *)
const w = 2 ^ log2_w.

(* Winternitz parameter w equals either 4, 16, or 256 *)
lemma val_w : w = 4 \/ w = 16 \/ w = 256.
proof.
rewrite /w; case: val_log2w => [->|]; last case => ->.
+ by left; rewrite expr2.
+ by right; left; rewrite (: 4 = (2 + 2)) 2:exprD_nneg // expr2. 
+ by right; right; rewrite (: 8 = 2 * 2 * 2) // 2!exprM ?expr2.
qed.


(* -- Checksum instantiation -- *)
clone import Checksum as CS with
  op w <- w

  proof gt0_w by smt(val_w).

(* Function to turn an integer (representing a message) into a list of base w digits. *)
op encode_int (l1 n l2 : int) : baseW list =
  int2lbw l1 n ++ checksum l1 n l2.

(* Slight variant of checksum_prop lemma that uses encode_int operator and added lengths *)
(* TODO: build in that l1 = len1 and l2 = len2 and remove all premises on lengths *)
lemma checksum_prop_var (l1 l2 x x' : int) :
     0 <= l1
  => 0 <= l2
  => (w - 1) * l1 < w ^ l2
  => 0 <= x  < w ^ l1
  => 0 <= x' < w ^ l1
  => (forall i, 0 <= i < l1 + l2 => BaseW.val (nth witness (encode_int l1 x l2) i) <= BaseW.val (nth witness (encode_int l1 x' l2) i))
  => x = x'.
proof.
move=> gt0_l1 gt0_l2 l1_l2 rng_x rng_xp @/encode_int all_le.
move: (checksum_prop l1 l2 x x' gt0_l1 gt0_l2 l1_l2 rng_x rng_xp _ _) => // i rng_i.
+ move: (all_le i _); first by smt().
  by rewrite 2!nth_cat ?size_int2lbw 1..4:/# (: i < l1) 1:/#.
move: (all_le (l1 + i) _); first by smt().
by rewrite 2!nth_cat ?size_int2lbw 1..4:/# (: ! l1 + i < l1) /#.
qed.


clone import WOTS_TW as WTW with
  op log2_w <- log2_w,
  op w <- w,

  theory BaseW <- BaseW,

  op encode_msgWOTS <- fun (m : msgWOTS) =>
                          EmsgWOTS.mkemsgWOTS (encode_int len1 (bs2int (rev (DigestBlock.val m))) len2)

  proof val_log2w, two_encodings.
  realize val_log2w by exact: val_log2w.
  realize two_encodings.
    move=> m m' neqm_mp.
    have eq28n_wl1 : 2 ^ (8 * n) = w ^ len1.
    + rewrite /w -exprM; congr.
      rewrite /len1 log2_wP -fromint_div 2:from_int_ceil; first by smt(val_log2w).
      by rewrite -divMr 2:mulKz 3://; first 2 smt(val_log2w).
    move: (checksum_prop_var len1 len2 (bs2int (rev (DigestBlock.val m'))) (bs2int (rev (DigestBlock.val m)))).
    move=> /(_ _ _ _); first 2 by smt(ge1_len1 ge1_len2).
    + rewrite -lt_fromint -fromintXn 1:#smt:(ge1_len2) -rpow_int 1:#smt:(val_w).
      have <- := rpowK w%r ((w - 1) * len1)%r _ _ _; first 3 by smt(val_w ge1_len1).
      apply: rexpr_hmono_ltr; first by smt(val_w).
      split=> [|_]; first by rewrite log_ge0 #smt:(val_w ge1_len1).
      rewrite /len2; pose l1w1 := len1 * (w - 1).
      have ->: log2 l1w1%r / log2 w%r = log w%r l1w1%r; last by smt(floor_bound).
      by rewrite /log2 /log; field; first 2 by smt(ln_eq0 val_w).
    move=> /(_ _ _); first 2 by smt(bs2int_ge0 DigestBlock.valP size_rev bs2int_le2Xs).
    move=> /contra; rewrite negb_forall=> //= /(_ _).
    + rewrite -negP=> /(congr1 (int2bs (8 * n))).
      rewrite -{1}(DigestBlock.valP m') -(size_rev (DigestBlock.val m')) -{1}(DigestBlock.valP m) -(size_rev (DigestBlock.val m)).
      rewrite !bs2intK => /(congr1 rev); rewrite !revK => /(congr1 DigestBlock.insubd).
      by rewrite !DigestBlock.valKd => ->>.
    move=> [] i; rewrite negb_imply (lezNgt (BaseW.val _)) /= => -[Hi Hlt].
    exists i; split; first by exact: Hi.
    rewrite /encode_msgWOTS !EmsgWOTS.getE Hi /= !EmsgWOTS.ofemsgWOTSK //.
    + by rewrite /encode_int size_cat 1:size_int2lbw 3:size_checksum; smt(ge1_len1 ge1_len2 bs2int_ge0).
    by rewrite /encode_int size_cat 1:size_int2lbw 3:size_checksum; smt(ge1_len1 ge1_len2 bs2int_ge0).
  qed.
