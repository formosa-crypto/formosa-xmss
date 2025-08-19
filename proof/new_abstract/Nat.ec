(* --- Require/Import --- *)
(* -- Built-In (Standard Library) -- *)
require import Int.

(* - Natural numbers - *)
type nat = [
    Zero
  | Succ of nat
].

op intOfNat (n : nat) =
  with n = Zero => 0
  with n = Succ m => intOfNat m + 1.

lemma intOfNat_nonneg (n : nat) : 0 <= intOfNat n.
proof. elim: n => /#. qed.

op natOfInt = fold Succ Zero.

lemma natOfInt_of_le_zero n : n <= 0 => natOfInt n = Zero.
proof. exact : foldle0. qed.

lemma natOfInt_succ_of_zero_le n : 0 <= n => natOfInt (n + 1) = Succ (natOfInt n).
proof. exact : foldS. qed.

lemma natOfInt_zero : natOfInt 0 = Zero. proof. by apply natOfInt_of_le_zero. qed.

lemma natOfInt_intOfNat : forall (n : nat), natOfInt (intOfNat n) = n.
proof.
  elim => /= [ | n hn].
  - by rewrite natOfInt_of_le_zero.
  - by rewrite (natOfInt_succ_of_zero_le _ (intOfNat_nonneg _)) hn.
qed.

lemma intOfNat_natOfInt_of_nonneg : 
  forall (z : int), 0 <= z => intOfNat (natOfInt z) = z.
proof.
  elim => [ | n hn].
  - by rewrite natOfInt_zero.
  - by rewrite (natOfInt_succ_of_zero_le _ hn) /#.
qed.

lemma intOfNat_natOfInt_of_nonpos : 
  forall (z : int), z <= 0 => intOfNat (natOfInt z) = 0.
proof. by move => z hz; rewrite (natOfInt_of_le_zero z hz). qed.

lemma intind (p:int -> bool):
  (p 0) =>
  (forall i, 0 <= i => p i => p (i + 1)) =>
  (forall i, 0 <= i => p i).
proof. 
  move => hp0 hI i hi.
  rewrite -(intOfNat_natOfInt_of_nonneg i hi).
  elim (natOfInt i) => [| j hj].
  - exact hp0.
  - rewrite (hI _ (intOfNat_nonneg _) hj).
qed.

(* - Integers - *)
type myInt = [
    ofNat of nat
  | negSucc of nat
].

op intOfMyInt (z : myInt) =
  with z = ofNat n => intOfNat n
  with z = negSucc n => -(intOfNat n + 1).

op myIntOfInt (z : int) = 
if 0 <= z then ofNat (natOfInt z) else negSucc (natOfInt(- z - 1)).
