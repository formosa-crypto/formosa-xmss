pragma Goals : printall.

require import AllCore.
from Jasmin require import JModel.
require import XMSS_IMPL.

(* CPU FLAGS : of, cf, sf, pf, zf *)

require import Array11.

lemma setcc_false (p : bool) : !p => SETcc p = W8.zero by rewrite /SETcc /#.
lemma setcc_true  (p : bool) :  p => SETcc p = W8.one  by rewrite /SETcc /#.

pred treehash_cond (h : W32.t Array11.t) (o : W64.t) = W64.of_int 2 \ule o /\ 
                                                       (h.[to_uint (o - W64.of_int 2)] = h.[to_uint (o - W64.one)]).

lemma treehash_cond_ll : islossless M(Syscall).__treehash_cond by proc; auto.

(* ============================================================================================================================= *)

lemma cmp_eq_W64 :
    forall (a b : W64.t), (CMP_64 a b).`5 = (a = b).
proof.
move => a b.
case (a = b) => [-> | ?]; rewrite /CMP_64 /rflags_of_aluop /ZF_of //= ?W64.WRingA.subrr //.
(have ?: !(a - b = W64.zero)) => [| /#]; smt(@W64).
qed.

lemma cmp_lt_W64 :
    forall (a b : W64.t), (CMP_64 a b).`2 = (a \ult b).
proof.
move => a b.
rewrite /CMP_64 /rflags_of_aluop /=; smt(@W64).
qed.

lemma cmp_eq_W32 :
    forall (a b : W32.t), (CMP_32 a b).`5 = (a = b).
proof.
move => a b.
case (a = b) => [-> | ?]; rewrite /CMP_32 /rflags_of_aluop /ZF_of //= ?W32.WRingA.subrr //.
(have ?: !(a - b = W32.zero)) => [| /#]; smt(@W32).
qed.

(* ============================================================================================================================= *)

lemma treehash_condition_correct_eq (h : W32.t Array11.t) (o : W64.t) :
    hoare [
    M(Syscall).__treehash_cond :
    arg = (h, o) 
    ==>
    (res = W8.one) = treehash_cond h o
    ].
proof.
proc => /=.
seq 3 : (#pre /\ bc1 = if (W64.of_int 2 \ule offset) then W8.one else W8.zero).
  + auto => /> *.
    by case ((of_int 2)%W64 \ule o) => H; [rewrite setcc_true | rewrite setcc_false] => //; rewrite cmp_eq_W64 cmp_lt_W64 /#. 
if; auto => />; rewrite uleE of_uintK /= => H; [
  have ?: !(2 <= to_uint o) by smt(W8.WRingA.oner_neq0) |
  have ?: (2 <= to_uint o) by smt(W8.WRingA.oner_neq0)
]; rewrite /treehash_cond uleE of_uintK /=; first by smt(W8.WRingA.oner_neq0).
rewrite (: 2 <= to_uint o = true) 1:/# /= /_EQ cmp_eq_W32 /SETcc /= /#.
qed.

lemma treehash_condition_correct_equiv (h : W32.t Array11.t) (o : W64.t) :
    hoare [
    M(Syscall).__treehash_cond :
    arg = (h, o) 
    ==>
    (res = W8.one) <=> treehash_cond h o
    ].
proof.
conseq (: _ ==> (res = W8.one) = treehash_cond h o); first by auto => /> /#. (* Reuse the proof from before *)
proc => /=.
seq 3 : (#pre /\ bc1 = if (W64.of_int 2 \ule offset) then W8.one else W8.zero).
  + auto => /> *.
    by case ((of_int 2)%W64 \ule o) => H; [rewrite setcc_true | rewrite setcc_false] => //; rewrite cmp_eq_W64 cmp_lt_W64 /#. 
if; auto => />; rewrite uleE of_uintK /= => H; [
  have ?: !(2 <= to_uint o) by smt(W8.WRingA.oner_neq0) |
  have ?: (2 <= to_uint o) by smt(W8.WRingA.oner_neq0)
]; rewrite /treehash_cond uleE of_uintK /=; first by smt(W8.WRingA.oner_neq0).
rewrite (: 2 <= to_uint o = true) 1:/# /= /_EQ cmp_eq_W32 /SETcc /= /#.
qed.

lemma treehash_condition_if (h : W32.t Array11.t) (o : W64.t) :
    hoare [
    M(Syscall).__treehash_cond :
    arg = (h, o) 
    ==>
    if treehash_cond h o then res = W8.one else res = W8.zero
    ].
proof.
proc => /=.
seq 3 : (#pre /\ bc1 = if (W64.of_int 2 \ule offset) then W8.one else W8.zero).
  + auto => /> *.
    by case ((of_int 2)%W64 \ule o) => H; [rewrite setcc_true | rewrite setcc_false] => //; rewrite cmp_eq_W64 cmp_lt_W64 /#. 
if; first by auto => />.
- (* 2nd branch: bc1 = W8.zero i.e. 2 <= offset is true *)
   auto => /> *.
   have E: (of_int 2)%W64 \ule o by smt().
   rewrite /treehash_cond /= (: (of_int 2)%W64 \ule o) 1:/# /= /_EQ cmp_eq_W32 !to_uintB //; smt(@W64 pow2_64).
qed.


(* ============================================================================================================================= *)
(* PHOARE VERSION OF THE LEMMAS *)
(* ============================================================================================================================= *)

lemma p_treehash_condition_correct_eq (h : W32.t Array11.t) (o : W64.t) :
    phoare [
    M(Syscall).__treehash_cond :
    arg = (h, o) 
    ==>
    (res = W8.one) = treehash_cond h o
    ] = 1%r by conseq treehash_cond_ll (treehash_condition_correct_eq h o). 

lemma p_treehash_condition_correct_equiv (h : W32.t Array11.t) (o : W64.t) :
    phoare [
    M(Syscall).__treehash_cond :
    arg = (h, o) 
    ==>
    (res = W8.one) <=> treehash_cond h o
    ] = 1%r by conseq treehash_cond_ll (treehash_condition_correct_equiv h o).

lemma p_treehash_condition_if (h : W32.t Array11.t) (o : W64.t) :
    phoare [
    M(Syscall).__treehash_cond :
    arg = (h, o) 
    ==>
    if treehash_cond h o then res = W8.one else res = W8.zero
    ] = 1%r by conseq treehash_cond_ll (treehash_condition_if h o).
