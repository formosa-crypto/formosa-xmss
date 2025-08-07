pragma Goals : printall.

require import AllCore List IntDiv Distr DList RealExp.
require (*--*) Subtype.

from Jasmin require import JModel.

require import Params Types Address Hash WOTS.

op H_msg_padding_val : W64.t.

op H_msg (t : threen_bytes) (M : msg_t) : nbytes =
  let padding : W8.t list = toByte_64 H_msg_padding_val n in
  Hash (padding ++ ThreeNBytesBytes.val t ++ Msg_t.val M).

(* 4.1.5 L-Trees *)
(* takes as input a WOTS+ public key pk and compresses it to a single 
   n-byte value pk[0].
*)
module LTree = {
  proc ltree (pk : wots_pk, address : adrs, _seed : seed) : nbytes = {
    var pks : nbytes list;
    var pk_i : nbytes;
    var tmp : nbytes;
    var i : int;
    var _len : int;
    var tree_height : int;

    address <- set_tree_height address 0;
    pks <- LenNBytes.val pk;

    _len <- len;
    while (1 < _len) { (* Same as _len > 1 *)
      i <- 0;
      while (i < _len %/ 2) {
        address <- set_tree_index address i;
        pk_i <- nth witness pks (2*i);
        tmp <- nth witness pks (2*i + 1);
        pk_i <@ Hash.rand_hash (pk_i, tmp, _seed, address);
        pks <- put pks i pk_i;
        i <- i + 1;
      }

      if (_len %% 2 = 1) {
        pk_i <- nth witness pks (_len - 1);
        pks <- put pks (_len %/ 2) pk_i;
      }

      _len <- if _len %% 2 = 0 then _len %/ 2 else _len %/ 2 + 1;

      tree_height <- get_tree_height address;
      address <- set_tree_height address (tree_height + 1);
    }

    pk_i <- nth witness pks 0;

    return pk_i;
  }

  proc smoosh2(_seed, i, address, pks) = {
    var pk_i, tmp;

    address <- set_tree_index address i;
    pk_i <- nth witness pks (2*i);
    tmp <- nth witness pks (2*i + 1);
    pk_i <@ Hash.rand_hash (pk_i, tmp, _seed, address);
    pks <- put pks i pk_i;
    i <- i + 1;
    return (i, address, pks);
  }

  proc smoosh_level(_seed, _len, address, pks) = {
    var i, pk_i, tree_height;

    i <- 0;
    while (i < _len %/ 2) {
      (i, address, pks) <@ smoosh2(_seed, i, address, pks);
    }

    if (_len %% 2 = 1) {
      pk_i <- nth witness pks (_len - 1);
      pks <- put pks (_len %/ 2) pk_i;
    }

    _len <- if _len %% 2 = 0 then _len %/ 2 else _len %/ 2 + 1;

    tree_height <- get_tree_height address;
    address <- set_tree_height address (tree_height + 1);
    return (_len, address, pks);
  }

  proc smoosh_modular(pk : wots_pk, address : adrs, _seed : seed) : nbytes = {
    var pks : nbytes list;
    var pk_i : nbytes;
    var tmp : nbytes;
    var i : int;
    var _len : int;
    var tree_height : int;

    address <- set_tree_height address 0;
    pks <- LenNBytes.val pk;

    _len <- len;
    while (1 < _len) { (* Same as _len > 1 *)
      (_len, address, pks) <@ smoosh_level(_seed, _len, address, pks);
    }

    pk_i <- nth witness pks 0;

    return pk_i;
  }
}.

op smoosh2 _seed i address (pks : nbytes list) =
  let address = set_tree_index address i in
  let pk_i = nth witness pks (2 * i) in
  let pk_Si = nth witness pks (2 * i + 1) in
  let pk = rand_hash pk_i pk_Si _seed address in
  let pks = put pks i pk in
  (i + 1, address, pks).

hoare smoosh2_eq s0 i0 a0 p0:
  LTree.smoosh2:
    _seed = s0 /\ i = i0 /\ address = a0 /\ pks = p0
    ==> res = smoosh2 s0 i0 a0 p0.
proof.
proc; wp.
ecall (rand_hash_eq pk_i tmp _seed address).
by auto.
qed.

op smoosh_level _seed _len address0 pks0 =
  let (i, address, pks) =
    fold (fun st=> let (i, address, pks) = st in
                   smoosh2 _seed i address pks)
         (0, address0, pks0)
         (_len %/ 2) in
  let (len, pks) =
    if (_len %% 2 = 1)
    then
      let pk = nth witness pks (_len - 1) in
      (_len %/ 2 + 1, put pks (_len %/ 2) pk)
    else
      (_len %/ 2, pks)
  in
  let tree_height = get_tree_height address in
  let address = set_tree_height address (tree_height + 1) in
  (len, address, pks).

hoare smoosh_level_eq s0 l0 a0 p0:
  LTree.smoosh_level:
       _seed = s0 /\ _len = l0 /\ address = a0 /\ pks = p0
    /\ 0 <= _len
    ==> res = smoosh_level s0 l0 a0 p0.
proof.
proc; wp.
while (0 <= i <= _len %/ 2
    /\ (i, address, pks) = fold (fun st=> let (i, address, pks) = st in smoosh2 _seed i address pks) (0, a0, p0) i).
+ ecall (smoosh2_eq _seed i address pks).
  auto=> /> &0 ge0_i _ ih i_lt_half_len.
  have ->: (smoosh2 _seed i address pks){0}.`1 = i{0} + 1 by done.
  by rewrite foldS //= -ih /#.
auto=> /> ge0_l0; rewrite fold0 //=; split=> [/#|].
move=> address i pks exit ge0_i gei_div2_l0 post.
have ->> {exit gei_div2_l0}: i = l0 %/ 2 by smt().
rewrite /smoosh_level -post //=.
by case: (l0 %% 2 = 1)=> //= /#.
qed.

lemma pi1_smoosh_level_ldiv2 s l a p:
  (smoosh_level s l a p).`1 = ceil (l%r / 2%r).
proof.
rewrite /smoosh_level //=.
elim: (fold _ _ (l %/ 2))=> //=.
move: (edivzP l 2)=> //= [] + H.
have {H} []: l %% 2 = 0 \/ l %% 2 = 1 by smt().
+ move=> ^ + -> //=; rewrite -/(2 %| l)=> /fromint_div <- _.
  by rewrite from_int_ceil.
move=> -> //= {2}->.
rewrite fromintD fromintM RField.mulrDl -RField.mulrA RField.mulrV //=.
smt(@Real).
qed.

op ltree _seed address pk =
  let address = set_tree_height address 0 in
  let pks = LenNBytes.val pk in
  let (_len, address, pks) =
    fold (fun st=> let (_len, address, pks) = st in
                   smoosh_level _seed _len address pks)
         (size pks, address, pks)
         (ceil (log2 (size pks)%r))
  in
  nth witness pks 0.

lemma titi len:
  ceil (len%r / 2%r) = len %/ 2 + len %% 2.
proof. by move: (edivzP len 2); smt(ceil_bound). qed.

lemma toto len:
     1 < len
  => ceil (log2 len%r) = ceil (log2 (ceil (len%r / 2%r))%r) + 1.
proof.
move=> gt1_len; rewrite eqz_leq; split.
+ have ->: ceil (log2 (ceil (len%r / 2%r))%r) + 1
         = ceil (log2 (ceil (len%r / 2%r))%r + 1%r).
  + smt(@Real). (* see floor *)
  have: log2 len%r <= log2 (ceil (len%r / 2%r))%r + 1%r; 2:smt(@Real).
  rewrite -(RealExp.logK 2%r 1%r) // -logM.
  + smt(@Real).
  + smt(@RealExp).
  apply: log_mono=> //.
  + smt().
  + smt(@Real @RealExp).
  + smt(@Real @RealExp).
pose k := ceil (log2 len%r).
have:= (rexpr_hmono_ltr 2%r (k%r - 1%r) (log2 len%r) _ _)=> //.
+ smt(@Real @RealExp).
have:= (rexpr_hmono 2%r (log2 len%r) k%r _ _)=> //.
+ smt(@Real @RealExp).
rewrite rpowK // 1:/#.
move: (edivzP len 2)=> [] lenP H.
have len_mod2_eq0Veq1 {H}: len %% 2 = 0 \/ len %% 2 = 1.
+ smt().
case: len_mod2_eq0Veq1; 1:smt(@Real @RealExp).
move=> len_mod2P; move: lenP; rewrite len_mod2P=> lenP.
rewrite {1 2}lenP -fromintB !rpow_nat // 1,2:#smt:(@Real @RealExp).
rewrite !RField.fromintXn 1,2:#smt:(@Real @RealExp).
rewrite le_fromint lt_fromint.
move=> + _.
rewrite (Ring.IntID.exprSr 2 (k - 1)) 1:#smt:(@Real @RealExp).
rewrite -ltzE StdOrder.IntOrder.ltr_pmul2r // ltzE.
rewrite -{1}len_mod2P -titi.
smt(@Real @RealExp).
qed.

(* ltree smooshes exactly ceil (log2 len) time; by strong induction on ceil (log2 len):
   - if len is 1, this is trivial;
   - if len is 2^n < len <= 2^(n + 1), then the first 2^n nodes smoosh
     down to a single node in exactly n smooshes (induction, yo); and
     the remaining len - 2^n smoosh down to a single node in at most n
     smooshes (induction, yo); then we smoosh those two down with 1
     more smoosh. (If the rightmost nodes smoosh down to a single node
     faster than n smooshes, then that node simply gets carried up
     until the left half is all smooshed down!)
*)
hoare smoosh_modular_eq s0 a0 pk0:
  LTree.smoosh_modular: pk = pk0 /\ _seed = s0 /\ address = a0 ==> res = ltree s0 a0 pk0.
proof.
proc; wp.
while (1 <= _len <= len
    /\ (_len, address, pks) = fold (fun st=> let (l, a, p) = st in smoosh_level _seed l a p) (len, set_tree_height a0 0, LenNBytes.val pk0) (ceil (log2 len%r) - ceil (log2 _len%r))).
+ ecall (smoosh_level_eq _seed _len address pks).
  auto=> /> &0 _ _len_le_len ih gt1_len.
  split=> [/#|_].
  rewrite {-4}pi1_smoosh_level_ldiv2.
  split; 1:smt(@Real).
  have ->: ceil (log2 (ceil (_len{0}%r / 2%r))%r)
         = (ceil (log2 (ceil (_len{0}%r / 2%r))%r) + 1) - 1.
  + done.
  rewrite -toto //.
  rewrite Ring.IntID.opprD oppzK addzA.
  rewrite foldS 1:subz_ge0.
  + move: (log_mono 2%r _len{0}%r len%r _ _ _)=> //.
    + smt().
    + smt().
    rewrite le_fromint _len_le_len //=.
    smt(@Real).
  by move=> //=; rewrite -ih /#.
auto=> />; rewrite fold0 //=; split.
+ smt(gt2_len).
move=> l a p H1 H2.
have <<- {H1 H2}: 1 = l by smt().
move=> ge1_len.
have ->: log2 1%r = 0%r.
+ by rewrite /log2 /log ln1 RField.mul0r.
rewrite from_int_ceil //=.
by rewrite /ltree=> />; rewrite LenNBytes.valP=> <-.
qed.

equiv ltree_smoosh:
  LTree.ltree ~ LTree.smoosh_modular: ={pk, _seed, address} ==> ={res}.
proof. by proc; inline LTree.smoosh_level LTree.smoosh2; sim. qed.

hoare ltree_eq s0 a0 pk0:
  LTree.ltree: pk = pk0 /\ _seed = s0 /\ address = a0 ==> res = ltree s0 a0 pk0.
proof.
conseq ltree_smoosh (smoosh_modular_eq s0 a0 pk0)=> //.
by move=> /> &1; exists (pk, address, _seed){1}.
qed.
