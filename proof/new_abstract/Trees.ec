(* --- Require/Import --- *)
(* -- Built-In (Standard Library) -- *)
require import AllCore.

(* --- Generic types/datastructures --- *)
(* - Binary trees - *)
type 'a bintree = [
    Leaf of 'a
  | Node of 'a bintree & 'a bintree
].

(* Computes height, i.e., the number of levels to the furthest leaf, of a binary tree *)
op height (bt : 'a bintree) =
  with bt = Leaf _ => 0
  with bt = Node l r => 1 + max (height l) (height r).

(* Height of a binary tree is always greater than or equal to 0 *)
lemma height_nonneg (bt : 'a bintree):
  0 <= height bt.
proof. by elim: bt => /#. qed.

lemma height_leaf (x : 'a) : height (Leaf x) = 0. 
proof. trivial. qed.

lemma height_node_pos (l r : 'a bintree) : 0 < height (Node l r). 
proof. smt(height_nonneg). qed.

(* Characterize trees of height 0 *)
lemma exists_leaf_of_height_zero ['a] (bt : 'a bintree):
  height bt = 0 => exists x, bt = Leaf x.
proof. by case: bt => /= [x|t1 t2]; [exists x | smt(height_nonneg)]. qed.

(* Characterize trees of non-zero height *)
lemma exists_node_of_height_pos ['a] (bt : 'a bintree):
  0 < height bt => exists t1 t2, bt = Node t1 t2.
proof. by case: bt => [x| t1 t2] => // _; exists t1 t2. qed.

lemma height_zero_iff ['a] (bt : 'a bintree):
  height bt = 0 <=> exists x, bt = Leaf x.
proof. 
  split.
  - by apply exists_leaf_of_height_zero.
  - by move => [x hx]; rewrite hx.
qed.

lemma height_pos_iff ['a] (bt : 'a bintree):
  0 < height bt <=> exists t1 t2, bt = Node t1 t2.
proof. 
  split.
  - by apply exists_node_of_height_pos.
  - by move => [? ? hx]; rewrite hx; apply height_node_pos.
qed.

(*
  Determines whether a binary tree is perfect of a given height.
*)
op perfectOfHeight (bt : 'a bintree) (n : int) =
  with bt = Leaf _ => n = 0
  with bt = Node l r => perfectOfHeight l (n - 1) /\ perfectOfHeight r (n - 1).

lemma height_eq_of_perfectOfHeight (bt : 'a bintree) :
  forall (n : int), perfectOfHeight bt n => height bt = n.
proof.
  elim : bt => // /= ? ? Hl Hr ? [Hl2 Hr2].
  by rewrite (Hl _ Hl2) // (Hr _ Hr2).
qed.

(*
  Determines whether a binary tree is perfect.
*)
op perfect (bt : 'a bintree) = perfectOfHeight bt (height bt).

lemma perfect_leaf (x : 'a) : perfect (Leaf x). proof. trivial. qed.

lemma perfect_node (l r : 'a bintree) :
 perfect (Node l r) <=> height l = height r /\ perfect l /\ perfect r.
proof.
  rewrite /perfect.
  split.
  - move => [Hl Hr].
    by rewrite (height_eq_of_perfectOfHeight _ _ Hl)
    (height_eq_of_perfectOfHeight _ _ Hr) Hl Hr.
  - move => [Hlr [Hl Hr]] /=.
    by rewrite -Hlr Hl Hlr Hr.
qed.

lemma perfect_iff_exists_leaf_or_exists_node (bt : 'a bintree) : 
  perfect bt <=> (exists x, bt = Leaf x) \/ 
  (exists t1 t2, bt = Node t1 t2 /\ height t1 = height t2 /\ perfect t1 /\ perfect t2).
proof.
 case : bt => [x | l r].
 - smt(perfect_leaf).
 - smt(perfect_node).
qed.

(*
  Determines whether a binary tree is fully balanced, i.e.
  whether all leaves are on the same level
*)
op fully_balanced (bt : 'a bintree) =
  with bt = Leaf _ => true
  with bt = Node l r => height l = height r /\ fully_balanced l /\ fully_balanced r.

lemma fully_balanced_iff_perfect (bt : 'a bintree) : fully_balanced bt <=> perfect bt.
proof. by elim bt => // /= ? ? Hl Hr; rewrite Hl Hr perfect_node. qed.
