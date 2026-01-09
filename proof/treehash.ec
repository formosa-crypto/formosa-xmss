(* ==================================================================== *)
require import AllCore List Ring IntDiv BitEncoding StdOrder StdBigop.
(*---*) import IntOrder BS2Int.

import Bigint.

(* ==================================================================== *)
abbrev "_.[_]" ['a] (s : 'a list) (i : int) =
  nth witness s i.

(* ==================================================================== *)
type value.
type pseed.

op h : { int | 0 <= h } as ge0_h.

type haddress = { level: int; index: int; }.

op hash : pseed -> haddress -> value -> value -> value.

op reduce_tree : pseed -> value list -> haddress -> value.

axiom reduce_tree_leaf (pseed : pseed) (leaves : value list) (index : int) :
     size leaves = 2^h
  => 0 <= index < 2^h
  => reduce_tree pseed leaves {| level = 0; index = index |} = leaves.[index].

axiom reduce_tree_node (pseed : pseed) (leaves : value list) (lvl : int) (index : int) :
     size leaves = 2^h
  => 0 <= lvl < h
  => 0 <= index < 2^(h - (lvl + 1))
  => reduce_tree pseed leaves {| level = lvl + 1; index = index |} =
       hash pseed {| level = lvl; index = index |} 
         (reduce_tree pseed leaves {| level = lvl; index = 2 * index     |})
         (reduce_tree pseed leaves {| level = lvl; index = 2 * index + 1 |}).

op reduce (pseed : pseed) (leaves : value list) =
  reduce_tree pseed leaves {| level = h; index = 0 |}.

(* -------------------------------------------------------------------- *)
op haddr2off (off : haddress) : int =
  2^(off.`level) * off.`index.

(* -------------------------------------------------------------------- *)
op valid_haddress (addr : haddress) =
  0 <= addr.`level <= h /\ 0 <= addr.`index < 2^(h - addr.`level).

(* -------------------------------------------------------------------- *)
type stack1 = value * int.
type stack  = stack1 list.

(* -------------------------------------------------------------------- *)
module TreeHash = {
  proc th(pseed : pseed, leaves : value list, root : haddress) : value = {
    var idx    : int;
    var stack  : stack;
    var focus  : stack1;
    var top    : value;
    var addr   : haddress;
    var offset : int;

    stack  <- [];
    idx    <- 0;
    offset <- root.`index * 2^(root.`level);
    while (idx < 2^(root.`level)) {
      focus <- (leaves.[offset + idx], 0);
      while (stack <> [] /\ stack.[0].`2 = focus.`2) {
        top   <- stack.[0].`1;
        stack <- behead stack;
        addr  <- {| level = focus.`2; index = (offset + idx) %/ (2^(focus.`2 + 1)) |};
        focus <- (hash pseed addr top focus.`1, focus.`2 + 1);
      }
      stack <- focus :: stack;
      idx   <- idx + 1;
    }
    return stack.[0].`1;
  }

  proc th_abody(
    pseed  : pseed,
    leaves : value list,
    root   : haddress,
    offset : int,
    idx    : int,
    focus  : stack1,
    stack  : stack
  ) = {
    var top    : value;
    var addr   : haddress;

    top   <- stack.[0].`1;
    stack <- behead stack;
    addr  <- {| level = focus.`2; index = (offset + idx) %/ (2^(focus.`2 + 1)) |};
    focus <- (hash pseed addr top focus.`1, focus.`2 + 1);

    return (top, addr, focus, stack);
  }
}.

(* ==================================================================== *)
lemma sum_pow2 (k : int) : 0 <= k =>
  BIA.bigi predT (fun i => 2^i) 0 k = 2^k - 1.
proof.
elim: k => [|k ge0_k ih]; first by rewrite BIA.big_geq ?expr0.
by rewrite BIA.big_int_recr 1:/# /= ih addrAC exprS //#.
qed.

(* ==================================================================== *)
lemma drop_range (k i j : int) : 0 <= k => drop k (range i j) = range (i+k) j.
proof.
move=> ge0_k; case: (i + k < j) => ?; last first.
- by rewrite drop_oversize 1:size_range 1:/# range_geq //#.
rewrite (range_cat (i + k)) ~-1:/# drop_cat ifF.
- by rewrite size_range /#.
- by rewrite size_range ler_maxr 1:/# (_: k - _ = 0) 1:#ring drop0.
qed.

(* -------------------------------------------------------------------- *)
lemma take_range (k i j : int) : 0 <= k <= j - i => take k (range i j) = range i (i + k).
proof.
move=> ?; rewrite (range_cat (i + k)) ~-1:/# take_cat_le.
by rewrite size_range ifT 1:/# take_oversize // size_range /#.
qed.

(* -------------------------------------------------------------------- *)
lemma subseq_size ['a] (s1 s2 : 'a list) :
  subseq s1 s2 => size s1 <= size s2.
proof.
case/subseqP=> m [eq ->]; rewrite size_mask //.
by rewrite &(lez_trans _ _ _ (count_size _ _)) eq.
qed.

(* ==================================================================== *)
op ones (s : bool list) =
  pmap
    (fun ib : _ * _ => if ib.`2 then Some ib.`1 else None)
    (zip (range 0 (size s)) s).

(* -------------------------------------------------------------------- *)
lemma size_ones (s : bool list) : size (ones s) = count ((=) true) s.
proof.
rewrite /ones pmap_map size_map size_filter.
rewrite (map_zip_nth witness witness) /=.
- by rewrite size_range; smt(size_ge0).
rewrite size_range /= ler_maxr 1:&(size_ge0).
rewrite count_map (_ : preim _ _ = (fun i => s.[i])) 1:/#.
rewrite eq_sym -{1}[s](map_nth_range witness).
by rewrite count_map &(eq_count) /preim /= /#.
qed.

(* -------------------------------------------------------------------- *)
lemma size_ones_le (s : bool list) : size (ones s) <= size s.
proof. by rewrite size_ones &(count_size). qed.

(* -------------------------------------------------------------------- *)
lemma ones_nil : ones [] = [].
proof. by rewrite /ones /= range_geq. qed.

(* -------------------------------------------------------------------- *)
lemma ones_seq1 (b : bool) : ones [b] = if b then [0] else [].
proof.
by rewrite /ones /= range_ltn // range_geq //=; case: b.
qed.

(* -------------------------------------------------------------------- *)
lemma ones_nseq0 (n : int) : ones (nseq n false) = [].
proof.
rewrite /ones pmap_map eq_in_filter_pred0 //=.
case=> //= i /mapP[] [i' b] [] /mem_zip [] _.
by rewrite mem_nseq => -[] _ <-.
qed.

(* -------------------------------------------------------------------- *)
lemma ones_nseq1 (n : int) : ones (nseq n true) = range 0 n.
proof.
case: (n < 0).
- by move=> ?; rewrite range_geq -1:nseq0_le //#.
move/lezNgt => ge0_n; rewrite /ones pmap_map eq_in_filter_predT //=.
- case=> //= /mapP[] [i' b] [] /mem_zip [] _.
  by rewrite mem_nseq => -[] _ <-.
rewrite -map_comp /(\o) (map_zip_nth witness witness).
- by rewrite !(size_range, size_nseq) /#.
rewrite !(size_range, size_nseq) /= !ler_maxr ~-1://#.
rewrite -{3}[range 0 n]map_id &(eq_in_map).
by move=> i /mem_range ? /=; rewrite nth_nseq //= nth_range.
qed.

(* -------------------------------------------------------------------- *)
lemma ones_cat (s1 s2 : bool list) :
  ones (s1 ++ s2) = ones s1 ++ map ((+) (size s1)) (ones s2).
proof.
rewrite {1}/ones size_cat (range_cat (size s1)); ~-1:smt(size_ge0).
rewrite zip_cat; first by rewrite size_range; smt(size_ge0).
rewrite pmap_cat -/(ones s1); congr.
rewrite [size _ + size _]addrC range_addr /= zip_mapl.
pose F (ib : _ * _) := if ib.`2 then Some ib.`1 else None.
rewrite pmap_map -map_comp.
pose r := zip _ _; pose s := map _ r.
have ->: s = map (omap ((+) (size s1))) (map F r).
- by rewrite -map_comp &(eq_map) /(\o) /= /#.
rewrite filter_map /ones pmap_map -!map_comp /(\o) /=.
rewrite -/r -/F (_ : preim _ _ = predC1 None).
- by apply/fun_ext; case=> [|?] /=.
by apply: eq_in_map => /= -[|i] /mem_filter @/predC1 /=.
qed.

(* -------------------------------------------------------------------- *)
lemma ge0_ones (s : bool list) : forall x, x \in ones s => 0 <= x.
proof.
move=> x @/ones /pmapP[] [b y] [] /mem_zip /=.
by case=> /mem_range ? _; case: y => //= _ -> /#.
qed.

(* -------------------------------------------------------------------- *)
lemma le_nth_ones (k i : int) (s : bool list) :
  0 <= k => 0 <= i => k + i < size (ones s) => k <= (ones s).[k + i].
proof.
elim: s k i; first by rewrite ones_nil /#.
move=> b s ih k i ge0_k ge0_i.
rewrite -cat1s ones_cat ones_seq1 /= size_cat size_map.
case: b => /= _; last first.
- move=> ^?; move/(ih k i ge0_k ge0_i) /ler_trans; apply.
  by rewrite (nth_map witness) /#.
case: (k + i = 0) => ??; first smt().
rewrite (nth_map witness) 1:/#; case: (k = 0) => [->>|nz_k] /=.
- have /# := ge0_ones s (ones s).[i-1] _.
  by apply: mem_nth; smt().
by have := ih (k - 1) i _ _ _; move=> //#.
qed.

(* -------------------------------------------------------------------- *)
lemma le_size_ones (s : bool list) : all (fun i => i < size s) (ones s).
proof.
apply/allP=> x; rewrite /ones pmap_map => /mapP /= [] i.
rewrite mem_filter /predC1; case: i => //= i -[+ ->>].
by case/mapP=> /= -[j] /= [] //= [+ ->>] - /mem_zip [] /mem_range /#.
qed.

(* -------------------------------------------------------------------- *)
lemma drop_ones (n : int) (s : bool list) : 0 <= n <= size s =>
  let k = size (ones (take n s)) in
  drop k (ones s) = map ((+) n) (ones (drop n s)).
proof.
move=> ? k; rewrite -{1}[s](cat_take_drop n) ones_cat.
rewrite drop_cat_le -/k /= [drop k _]drop_oversize //=.
by rewrite size_take_condle 1:/# ifT 1:/#.
qed.

(* -------------------------------------------------------------------- *)
lemma ones_pow2 (n : int) : 0 <= n =>
  ones (int2bs (n + 1) (2^n)) = [n].
proof.
move=> ge0_n; rewrite int2bs_pow2 ?mem_range 1:/# /ones.
rewrite (_ : n + 1 - 1 - n = 0) 1:#ring nseq0 cats1.
rewrite size_rcons size_nseq ler_maxr // rangeSr //.
rewrite zip_rcons ?(size_nseq, size_range) 1:/#.
rewrite -cats1 pmap_cat /= {1}(_ : n = size (nseq n false)).
- by rewrite size_nseq /#.
- by rewrite -/(ones _) ones_nseq0.
qed.

(* -------------------------------------------------------------------- *)
lemma sorted_ones (s : bool list) : sorted Int.(<) (ones s).
proof.
suff: subseq (ones s) (range 0 (size s)).
- by move=> /(subseq_sorted (Int.(<)) ltz_trans); apply; apply/sorted_range.
apply/subseqP; exists s; rewrite size_range /= ler_maxr //=.
elim/last_ind: s => [|s b ih] /=; first by rewrite ones_nil range_geq.
rewrite -cats1 ones_cat ones_seq1 /= size_cat /= rangeSr // -cats1.
rewrite mask_cat; first by rewrite size_range /= #smt:(size_ge0).
by rewrite -ih /= /#.
qed.

(* ==================================================================== *)
op revones (s : int list) : int =
  BIA.big predT (fun i => 2^i) s.

(* -------------------------------------------------------------------- *)
lemma ge0_revones (s : int list) : 0 <= revones s.
proof. by apply: sumr_ge0 => /= *; apply: expr_ge0. qed.

(* -------------------------------------------------------------------- *)
lemma revones_seq1 (i : int) : revones [i] = 2^i.
proof. by rewrite /revones BIA.big_seq1. qed.

(* -------------------------------------------------------------------- *)
lemma revones_cons (i : int) (s : int list) :
  revones (i :: s) = 2^i + revones s.
proof. by rewrite /revones BIA.big_consT. qed.

(* -------------------------------------------------------------------- *)
lemma revones_cat (s1 s2 : int list) :
  revones (s1 ++ s2) = revones s1 + revones s2.
proof. by rewrite /revones BIA.big_cat. qed.

(* -------------------------------------------------------------------- *)
lemma revones_range (i j : int) : 0 <= i <= j =>
  revones (range i j) = 2^j - 2^i.
proof.
have h: forall k, 0 <= k => revones (range 0 k) = 2^k - 1.
- by move=> k ? @/revones; rewrite sum_pow2.
move=> ?; rewrite (_ : 2^j - 2^i = (2^j-1) - (2^i - 1)) 1:#ring.
rewrite -!h ~-1:/#; rewrite (range_cat i 0 j) ~-1:/#.
by rewrite revones_cat; ring.
qed.

(* -------------------------------------------------------------------- *)
lemma revones_shift (i : int) (s : int list) :
     0 <= i
  => (forall k, k \in s => 0 <= k)
  => revones (map ((+) i) s) = 2^i * revones s.
proof.
move=> ge0_i ge0_s @/revones.
rewrite BIA.big_mapT BIA.mulr_sumr /(\o) /=.
rewrite !BIA.big_seq &(BIA.eq_bigr) /=.
by move=> k /ge0_s ge0_k; rewrite exprD_nneg //#.
qed.

(* -------------------------------------------------------------------- *)
lemma revones_ones (s : bool list) : revones (ones s) = bs2int s.
proof.
elim: s => [|b s ih] /=; first by rewrite bs2int_nil ones_nil.
rewrite -cat1s ones_cat ones_seq1 /= bs2int_cons -ih.
rewrite revones_cat; congr; last first.
- by rewrite revones_shift // 1:&(ge0_ones) expr1.
- by case: b => // _; rewrite revones_seq1 expr0.
qed.

(* -------------------------------------------------------------------- *)
lemma revonesK (h i : int) : 0 <= h => 0 <= i < 2^h =>
  revones (ones (int2bs (h + 1) i)) = i.
proof. by move=> ??; rewrite revones_ones int2bsK ?exprS //#. qed.

(* -------------------------------------------------------------------- *)
lemma dvdz_sum ['a] (f : 'a -> int) (s : 'a list) (v : int) :
     (forall x, x \in s => v %| f x)
  => v %| BIA.big predT f s.
proof.
elim: s => [|x s ih] h; first by rewrite BIA.big_nil dvdz0.
rewrite BIA.big_consT &(dvdzD).
- by apply: h; rewrite mem_head.
- by apply: ih => y y_in_s; apply: h; rewrite mem_behead.
qed.

(* -------------------------------------------------------------------- *)
lemma dvd_pow2_revones (i : int) (s : int list) :
     0 <= i
  => (forall x, x \in s => i <= x)
  => 2^i %| revones s.
proof.
move=> ge0_i h; apply: dvdz_sum => /=.
by move=> x /h le_xi; apply: dvdz_exp2l => /#.
qed.

(* ==================================================================== *)
op stackrel (root : haddress) (pseed : pseed) (leaves : value list) (idx : int) (stk : stack) =
  let s = int2bs (root.`level + 1) idx in

     (ones s = map (fun (stk1 : stack1) => stk1.`2) stk)
  /\ (forall stk1, stk1 \in stk => stk1.`1 =
        let addr = {|
          level = stk1.`2;
          index = 2^(root.`level - stk1.`2) * root.`index + bs2int (false :: drop (stk1.`2 + 1) s);
        |} in
        reduce_tree pseed leaves addr).

(* -------------------------------------------------------------------- *)
lemma stackrel0 (root : haddress) (pseed : pseed) (leaves : value list) :
  stackrel root pseed leaves 0 [].
proof. by split => //=; rewrite int2bs0 ones_nseq0. qed.

(* -------------------------------------------------------------------- *)
lemma stackrelS
  (root   : haddress)
  (pseed  : pseed)
  (leaves : value list)
  (idx    : int)
  (stk    : stack)
:
  let k = index false (int2bs (root.`level + 1) idx) in

     size leaves = 2^h
  => 0 <= idx < 2^(root.`level)
  => valid_haddress root
  => stackrel root pseed leaves idx stk
  => stackrel root pseed leaves (idx + 1) (
          (foldl
            (fun v1 (v2 : value * int) =>
              let addr = {|
                level = v2.`2;
                index = (haddr2off root + idx) %/ 2^(v2.`2 + 1);
              |} in
              hash pseed addr v2.`1 v1)
            leaves.[haddr2off root + idx] (take k stk), k)
       :: drop k stk
     ).
proof.
have ? := ge0_h; move=> k szlves rg_idx okroot [h1 h2]; have le_kh: k <= root.`level.
- have ->: root.`level = size (int2bs (root.`level + 1) idx) - 1.
  - by rewrite size_int2bs /#.
  rewrite ler_subr_addr -ltzE index_mem &(nthP witness).
  exists root.`level; rewrite size_int2bs; split; first smt().
  by rewrite nth_mkseq 1:/# /= pdiv_small.
have ge0_k: 0 <= k by apply: index_ge0.
have ?: 0 <= root.`level by smt().
have ?: k <= size stk.
- rewrite -(size_map snd) -h1 size_ones.
  rewrite int2bs_strikeE // count_cat count_nseq /=.
  by rewrite ler_maxr 1:index_ge0; smt(count_ge0).
split => /=.
- rewrite map_drop -h1 int2bs_strike_succE //= -/k ones_cat.
  rewrite ones_nseq0 size_nseq ler_maxr //=.
  rewrite -cat1s ones_cat /= ones_seq1 /= -map_comp.
  rewrite (_ : _ \o _ = (+) (k + 1)) 1:/#.
  rewrite -drop_ones ?size_int2bs 1:/#; congr.
  rewrite int2bs_strikeE // -/k.
  rewrite take_cat size_nseq ifF 1:/# ler_maxr //.
  rewrite [k+1-k]addrAC /= take0 ones_cat size_cat size_map.
  by rewrite ones_seq1 /= ones_nseq1 size_range /#.
move=> stk1 [->/=|]; last first.
- move=> ^hmemk; have ?: k <= stk1.`2.
  - case/(nthP witness): hmemk => i [rgi <-].
    rewrite (nth_drop witness) ~-1://# -(nth_map _ witness snd).
    - smt(size_drop).    
    rewrite -h1 &(le_nth_ones) 1,2:/# h1 size_map.
    by move: rgi; rewrite size_drop /#.
  move/mem_drop/h2 => -> /=; do 3! congr.
  rewrite int2bs_strikeE // int2bs_strike_succE // -/k.
  rewrite !drop_cat ?size_nseq !ifF ~-1:/#.
  by rewrite !drop_cons !ifT ~-1:/#.
rewrite (_ : false :: _ = drop k (int2bs (root.`level+1) idx)).
- rewrite int2bs_strike_succE // eq_sym {1}int2bs_strikeE //= -/k.
  rewrite drop_cat_le size_nseq ifT 1:/#.
  rewrite drop_oversize ?size_nseq 1:/# /=.
  rewrite -cat1s catA cats1 drop_cat_le.
  rewrite size_rcons size_nseq ifT 1:/# /= eq_sym.
  by rewrite drop_oversize ?(size_rcons, size_nseq) 1:/#.
move=> {stk1}; move: {1 2 4 5 6 7}k (ge0_k) (lezz k).
elim=> [|k0 ge0_k0 ih] le_k0_k.
- rewrite take0 /= reduce_tree_leaf // drop0.
  - rewrite int2bsK ?exprSr ~-1:/#; split=> [|_]; first smt(expr_ge0).
    case: okroot => rg_rt_lvl rg_rt_dx.
    apply: (ltr_le_trans (
      2 ^ root.`level * (2 ^ (h - root.`level) - 1) + 2 ^ root.`level)).
    - by rewrite &(ler_lt_add) 2:/# ler_wpmul2l #smt:(expr_ge0).
    by rewrite &(lerr_eq) mulrBr -exprD_nneg ~-1://# addrCA /= #ring.
  by rewrite int2bsK ?exprS ~-1:/#.
rewrite takeD ~-1://# /= foldl_cat ih 1:/#.
rewrite (drop_take1_nth witness) /=.
- by split=> //#.
rewrite reduce_tree_node //.
- smt().
- split=> [|_]; first by smt(expr_ge0 bs2int_ge0).
  case: okroot=> ok_rt_lvl ok_rt_idx.
  apply: (ltr_le_trans (
      2 ^ (root.`level - (k0 + 1)) * (2 ^ (h - root.`level) - 1)
    + 2 ^ (root.`level - (k0 + 1)))).
  - rewrite &(ler_lt_add); first by rewrite ler_wpmul2l #smt:(expr_ge0).
    rewrite -expz_div ~-1://# ltz_divRL; 1: by apply: expr_gt0.
    - by rewrite dvdz_exp2l /#.
    apply: (ler_lt_trans (bs2int (int2bs (root.`level + 1) idx))).
    - rewrite [bs2int (int2bs _ _)](bs2int_take_drop (k0 + 1)) 1:/#.
      rewrite [_ * 2^_]mulrC lez_addr 1:bs2int_ge0.
      by rewrite int2bsK ?exprSr //#.
  rewrite &(lerr_eq) mulrBr -exprD_nneg ~-1://# /=.
  by rewrite (_ : _ + (h - _) = h - (k0 + 1)) #ring.
congr.
- move/(congr1 (fun s => nth witness s k0)): h1 => /=.
  rewrite (nth_map witness) 1:/# /= {1}int2bs_strikeE //=.
  move: (drop _ _) => s'; rewrite ones_cat /=.
  rewrite nth_cat size_ones count_nseq /= -/k.
  rewrite ifT 1:/# ones_nseq1 nth_range 1:/# /= => <- /=.
  rewrite -bs2int_div 1:/# int2bsK 1:/# //; 1: by rewrite exprS /#.
  rewrite /haddr2off divzDl; first by rewrite dvdz_mulr dvdz_exp2l //#.
  rewrite [_ * root.`index]mulrC -divzpMr 1:dvdz_exp2l ~-1://#.
  by rewrite -expz_div ~-1://# #ring.
- rewrite mulrDr [2*_]mulrA -exprS 1:/# opprD /= -[_+1]addrA /=.
  have ->/= := h2 stk.[k0] _; first by apply: mem_nth => /#.
  rewrite bs2int_cons b2i0 /= (_ : stk.[k0].`2 = k0) //.
  rewrite -(nth_map _ witness snd) 1:/#.
  rewrite -h1 int2bs_strikeE // ones_cat /= nth_cat ifT.
  - by rewrite ones_nseq1 size_range /= -/k 1:/#.
  by rewrite ones_nseq1 nth_range -/k //#.
- rewrite (drop_nth witness) 1:#smt:(size_int2bs).
  rewrite bs2int_cons [_+2*_]addrC; do 2! congr.
  rewrite int2bs_strikeE // nth_cat ifT.
  - by rewrite size_nseq -/k /#.
  by rewrite nth_nseq 1:/# mulrDr mulrA -exprS /#.
qed.

(* ==================================================================== *)

(* Use "real" inductive predicate *)
(* Meanwhile, we use an impredicative encoding of eqvred *)

op eqvred (off : haddress) (pseed : pseed) (s1 s2 : stack) =
  forall (P : stack -> stack -> bool),
     (forall s, P s s)
  => (forall s2 s1 s3, P s1 s2 => P s2 s3 => P s1 s3)
  => (forall s v1 v2 i,
        let addr = {| level = i; index = (haddr2off off + revones (unzip2 s)) %/ 2^(i+1) |} in
        P ((v2, i) :: (v1, i) :: s) ((hash pseed addr v1 v2, i + 1) :: s))
  => P s1 s2.

(* -------------------------------------------------------------------- *)
lemma eqvredW (off : haddress) (pseed : pseed) (P : stack -> stack -> bool) :
     (forall s, P s s)
  => (forall s2 s1 s3, P s1 s2 => P s2 s3 => P s1 s3)
  => (forall s v1 v2 i,
        let addr = {| level = i; index = (haddr2off off + revones (unzip2 s)) %/ 2^(i+1) |} in
        P ((v2, i) :: (v1, i) :: s) ((hash pseed addr v1 v2, i + 1) :: s))
  => forall s1 s2, eqvred off pseed s1 s2 => P s1 s2.
proof. by move=> 3? s1 s2 @/eqvred /(_ P); apply. qed.

(* -------------------------------------------------------------------- *)
lemma eqvred_refl (off : haddress) (pseed : pseed) (s : stack) :
  eqvred off pseed s s.
proof. smt(). qed.

(* -------------------------------------------------------------------- *)
lemma eqvred_trans (off : haddress) (pseed : pseed) (s2 s1 s3 : stack) :
  eqvred off pseed s1 s2 => eqvred off pseed s2 s3 => eqvred off pseed s1 s3.
proof. smt(). qed.

(* -------------------------------------------------------------------- *)
lemma eqvredR (off : haddress) (pseed : pseed) (s : stack) (v1 v2 : value) (i : int) :
  let addr = {| level = i; index = (haddr2off off + revones (unzip2 s)) %/ 2^(i+1) |} in
  eqvred off pseed ((v2, i) :: (v1, i) :: s) ((hash pseed addr v1 v2, i + 1) :: s).  
proof. smt(). qed.

(* -------------------------------------------------------------------- *)
lemma eqvredI
  (off : haddress) (pseed : pseed) (v : value) (i : int)
  (stk1_v : value list) (stk2 stk : stack)
:
  let stk1 = zip stk1_v (range i (i + size stk1_v)) in
  let idx  = revones (unzip2 (stk1 ++ stk2)) in

     0 <= i
  => valid_haddress off
  => i + size stk1_v <= off.`level
  => (forall l, l \in unzip2 stk2 => (i + size stk1) < l)
  => eqvred off pseed ((v, i) :: stk1 ++ stk2) stk
  => exists v' i' stk',
       let k = i' - i in
            stk = (v', i') :: stk'
         /\ 0 <= k <= size stk1
         /\ stk' = (drop k stk1) ++ stk2
         /\ v' = foldl (fun v1 (v2 : _ * _) =>
              let addr = {| level = v2.`2; index = (haddr2off off + idx) %/ 2^(v2.`2 + 1) |}  in
              hash pseed addr v2.`1 v1
            ) v (take k stk1).
proof.
pose P (s1 s2 : stack) :=
  forall (v : value) (i : int) (stk1_v : value list) (stk2 : stack),
    let stk1 = zip stk1_v (range i (i + size stk1_v)) in
    let idx  = revones (unzip2 (stk1 ++ stk2)) in

       0 <= i
    => i + size stk1_v <= off.`level
    => s1 = ((v, i) :: stk1 ++ stk2)
    => (forall l, l \in unzip2 stk2 => (i + size stk1) < l)
    => exists v' i' stk',
         let k = i' - i in (
              s2 = (v', i') :: stk'
           /\ 0 <= k <= size stk1
           /\ stk' = (drop k stk1) ++ stk2
           /\ v' = foldl (fun v1 (v2 : _ * _) =>
                let addr = {| level = v2.`2; index = (haddr2off off + idx) %/ 2^(v2.`2 + 1) |}  in
                hash pseed addr v2.`1 v1
              ) v (take k stk1)
         ).
move=> stk1 idx ge0_i okoff oklvl hhole hred.
(have hW := eqvredW off pseed P _ _ _ _ _ hred; last first);
  try (move=> {idx v i ge0_i stk1_v stk2 stk1 oklvl hhole hred}).
- move: hW => /(_ v i stk1_v stk2 _ _ _ hhole) // [v' i' stk'] *.
  by exists v' i' stk'.

- move=> s @/P => {P} v i stk1_v stk2 stk1 idx ge0_i oklvl s1E hhole.
  exists v i (stk1 ++ stk2) => /=; rewrite s1E /=.
  by rewrite size_ge0 /= drop0 take0.

- move=> s2 s1 s3 ih1 ih2 v i stk1_v stk2 stk1 idx ge0_i oklvl s1E hhole.
  have [v' i' stk'] := ih1 v i stk1_v stk2 ge0_i oklvl s1E hhole.
  (pose k := i' - i)  => -[# s2E ge0_k le_k stk'E].
  rewrite -/stk1 -/idx => v'E; have {le_k}le_k: k <= size stk1_v.
  - move: le_k; rewrite size_zip size_range addrAC /=.
    by rewrite ler_maxr 1:&(size_ge0) /#.
  have ?: size (take k stk1_v) = k.
  - by rewrite size_take_condle // le_k.
  have ?: size (range i i') = k by rewrite size_range /#.
  have := ih2 v' i' (drop k stk1_v) stk2 _ _ _ _.
  - smt().
  - by rewrite size_drop //#.
  - rewrite s2E /= stk'E  (range_cat i') ~-1:/#; congr.
    rewrite drop_zip drop_cat_le size_range ifT 1:/#.
    by congr; rewrite drop_oversize 1:/# /= size_drop /#.
  - move=> vi /hhole; rewrite !size_zip size_range.
    rewrite [i + _ - i]addrAC /= ler_maxr 1:size_ge0 minzz.
    rewrite size_range size_drop // [max _ (size _ - _)]ler_maxr 1:/#.
    by rewrite [i' + _ - i']addrAC /= ler_maxr 1:/# minzz /#.
  case=> [v'' i'' stk'']; (pose k' := i'' - i') => /=.
  move=> [# s3E ge0_k' le_k' stk''E].
  (pose stk1_tl := zip (drop k _) _) => v''E.
  exists v'' i'' stk''; rewrite s3E /=.
  have {le_k'}le_k': k' <= size stk1_v - k.
  - move: le_k'; rewrite size_zip size_range addrAC /=.
    rewrite size_drop // [max 0 (size _ - _)]ler_maxr 1:/#.
    by rewrite ler_maxr 1:/# minzz.
  rewrite {1}/stk1 size_zip size_range addrAC /=.
  rewrite ler_maxr 1:/# minzz; (split; first smt()); split.
  - rewrite stk''E; congr; rewrite /stk1.
    have ->: i'' - i = k + k' by smt().
    rewrite [k + k']addrC -[drop (k' + k) _]drop_drop //.
    rewrite eq_sym (range_cat i') ~-1:/#; congr.
    rewrite drop_zip drop_cat_le ifT 1:/#; congr.
    by rewrite drop_oversize 1:/# /= size_drop /#.
  have ->: i'' - i = k + k' by smt().
  rewrite takeD // foldl_cat -v'E => {v'E}.
  have stk1_tlE: stk1_tl = drop k stk1.
  - rewrite /stk1_tl /stk1 drop_zip.
    rewrite size_drop // ler_maxr 1:/# eq_sym drop_range //#.
  rewrite v''E stk1_tlE &(eq_in_foldl) // => {v''E}; first last.
  move=> v1 [v2 lvl] hmem /=; do 2! congr.
  rewrite /idx eq_sym !map_cat !revones_cat.
  have ?: i' <= lvl < i''.
  - move: hmem; rewrite /stk1 drop_zip take_zip => /mem_zip[] _.
    by rewrite drop_range ~-1:/# take_range ~-1:/# mem_range /#.
  rewrite ![(haddr2off _ + _) %/ _]divzDl; -1: congr.
  - by rewrite /haddr2off dvdz_mulr dvdz_exp2l //#.
  - by rewrite /haddr2off dvdz_mulr dvdz_exp2l //#.
  rewrite divzDr; first rewrite dvd_pow2_revones ~-1:/#.
  - by move=> x /hhole @/stk1; rewrite size_zip size_range /#.
  rewrite divzDr; first rewrite dvd_pow2_revones ~-1:/#.
  - by move=> x /hhole @/stk1; rewrite size_zip size_range /#.
  congr; rewrite map_drop (_ : unzip2 stk1 = range i (i + size stk1_v)).
  - by rewrite /stk1 unzip2_zip 1:#smt:(size_range).
  rewrite drop_range // !revones_range ~-1:/#.
  rewrite !divzDl ?dvdz_exp2l ~-1:/#; congr.
  rewrite !divNz ~-1:expr_gt0 //; do 2! congr.
  rewrite !pdiv_small -1:// subr_ge0 -(ltzE 0) expr_gt0 //=;
    by rewrite ltzE /= ler_weexpn2l /#.

- move=> s v' v_ i_ addr_ @/P v i stk1_v stk2 stk1 idx ge0_i oklvl.
  case=> -[] ->> ->> eq_cat h_hl.
  exists (hash pseed addr_ v' v) (i+1) s => /=.
  have /eq_sym eq_stk1_v := head_behead stk1_v witness _.
  - apply/negP => stk1_v_nil; have stk1_nil: stk1 = [].
    - by rewrite /stk1 stk1_v_nil /= range_geq.
    move: eq_cat; rewrite stk1_nil /=; smt().
  have stk1E: stk1 = (head witness stk1_v, i) :: behead stk1.
  - by rewrite /stk1 eq_stk1_v range_ltn 1:#smt:(size_ge0).
  move: eq_cat; rewrite {1}stk1E => -[] [] ->> _ stk'E.
  rewrite addrAC /= stk1E /= ler_addl size_ge0 /=.
  rewrite drop0 -stk'E take0 /= /addr_; congr => /=.
  rewrite ![(haddr2off _ + _) %/ _]divzDl; -1: congr.
  - by rewrite /haddr2off dvdz_mulr dvdz_exp2l // #smt:(size_ge0).
  - by rewrite /haddr2off dvdz_mulr dvdz_exp2l // #smt:(size_ge0).
  rewrite /idx stk'E {2}stk1E /= revones_cons divzDr.
  - rewrite &(dvd_pow2_revones) 1:/# => x.
    rewrite map_cat mem_cat => -[|/h_hl]; last first.
    - by rewrite stk1E /= #smt:(size_ge0).
    rewrite /stk1 range_ltn /=.
    - by rewrite eq_stk1_v #smt:(size_ge0).
    rewrite {1}eq_stk1_v -cat1s -[i :: _]cat1s zip_cat //=.
    rewrite unzip2_zip 1:(size_range, size_behead) 1:#smt:(size_ge0).
    by rewrite mem_range #smt:(size_ge0).
  rewrite [2^i %/ _]pdiv_small // expr_ge0 //= exprS #smt:(expr_gt0).
qed.

(* -------------------------------------------------------------------- *)
lemma eqvredI_cmpl
  (off : haddress) (pseed : pseed) (v : value) (k : int) (stk1 stk2 : stack)
  (fcs : stack1) (stk : stack)
:
     0 <= k
  => unzip2 stk1 = range 0 k
  => valid_haddress off
  => k <= off.`level
  => (forall l, l \in unzip2 stk2 => k < l)
  => (stk <> [] => (stk.[0]).`2 <> fcs.`2)
  => eqvred off pseed ((v, 0) :: stk1 ++ stk2) (fcs :: stk)
  => let v' = foldl (
       fun v1 (v2 : _ * _) =>
         let addr = {|
           level = v2.`2;
           index = (
             haddr2off off + revones (unzip2 (stk1 ++ stk2)) 
           ) %/ 2^(v2.`2 + 1); |}  in
         hash pseed addr v2.`1 v1
     ) v (take k stk1) in
     fcs :: stk = (v', k) :: stk2.
proof.
move=> ge0_k stk1_sndE okoff oklvl h_hl hfin heqv v'.
have := eqvredI off pseed v 0 (unzip1 stk1) stk2 (fcs :: stk).
have sz_stk1: size stk1 = k.
- by rewrite -(size_map snd) stk1_sndE size_range /#.
(pose stk1_0 := zip _ _) => /=; have -> {stk1_0}: stk1_0 = stk1.
- by rewrite /stk1_0 /= size_map sz_stk1 -stk1_sndE zip_unzip.
move/(_ _ _ _ _) => //.
- by rewrite size_map /#.
- smt().
case=> v'_ i' stk' [#] ->> <<- ? le_i' stkE v'_E.
suff ->>/=: i' = k; first split.
- by rewrite v'_E /v'.
- by rewrite stkE drop_oversize // sz_stk1.
move: le_i'; rewrite sz_stk1 ler_eqVlt => -[] // lt_'i_k.
have := hfin _; last apply: contraR => _.
- by rewrite -size_eq0 stkE size_cat size_drop // #smt:(size_ge0).
rewrite stkE nth_cat size_drop // sz_stk1 ifT 1:/#.
rewrite nth_drop //= -(nth_map _ witness snd) 1:/#.
by rewrite stk1_sndE nth_range /#.
qed.

(* ==================================================================== *)
op ath_inv
  (root   : haddress)
  (pseed  : pseed)
  (focus  : stack1)
  (offset : int)
  (idx    : int)
  (leaves : value list)
  (stack  : stack)
  (stk0   : stack)
=
     offset = root.`index * 2^root.`level
  /\ stackrel root pseed leaves idx stk0
  /\ subseq stack stk0
  /\ (stack <> [] => focus.`2 <= (head witness stack).`2)
  /\ eqvred root pseed ((nth witness leaves (offset + idx), 0) :: stk0) (focus :: stack)
  /\ idx %/ 2^focus.`2 = revones (unzip2 stack) %/ 2^focus.`2.

(* -------------------------------------------------------------------- *)
lemma treehash_ath_body_correct
    (_pseed  : pseed)
    (_leaves : value list)
    (_root   : haddress)
    (_offset : int)
    (_idx    : int)
    (_focus  : stack1)
    (_stack  : stack)
    (stk0    : stack)
  :
     hoare[TreeHash.th_abody :
          arg = (_pseed, _leaves, _root, _offset, _idx, _focus, _stack)
       /\ size _leaves = 2^h
       /\ valid_haddress _root
       /\ 0 <= _idx < 2 ^ _root.`level
       /\ _stack <> []
       /\ _stack.[0].`2 = _focus.`2
       /\ ath_inv _root _pseed _focus _offset _idx _leaves _stack stk0
     ==>
          let focus = res.`3 in
          let stack = res.`4 in
          ath_inv _root _pseed focus _offset _idx _leaves stack stk0
          /\ (let top  = _stack.[0].`1 in
              let addr = {| level = _focus.`2; index = (_offset + _idx) %/ (2^(_focus.`2 + 1)) |} in
                 stack = behead _stack
              /\ focus = (hash _pseed addr top _focus.`1, _focus.`2 + 1))
     ].
proof.
have ? := ge0_h.
proc; auto=> @/ath_inv &hr.
auto=> |> 4? nzstk eqs hstk hsub hfcs h eqidx.
have ?: 0 <= root{hr}.`level by smt().

pose k := List.index false (int2bs (root{hr}.`level + 1) idx{hr}).
have ge0_k: 0 <= k by apply: index_ge0.
have le_k_stk0: k <= size stk0.
- case: (hstk) => + _ - /(congr1 size); rewrite size_map => <-.
  rewrite /k int2bs_strikeE // -/k index_cat mem_nseq /=.
  rewrite size_nseq ler_maxr // index_cons /=.
  rewrite ones_cat ones_nseq1 size_cat size_range size_map.
  by rewrite ler_maxr //=; smt(size_ge0).
have hlt: forall (l : int), l \in unzip2 (drop k stk0) => k < l.
- move=> l; rewrite map_drop.
  case: (hstk) => + _ - <-; rewrite int2bs_strikeE // -/k.
  rewrite ones_cat ones_nseq1 size_nseq ler_maxr 1:/#.
  rewrite -cat1s ones_cat ones_seq1 /= -map_comp.
  rewrite (_: _ \o _ = (+) (k + 1)) 1:/#.
  rewrite drop_cat_le ?size_range ifT 1:/#.
  rewrite drop_oversize ?size_range 1:/# /=.
  by case/mapP => x [] + ->>; smt(ge0_ones).
have stk0_k_sndE: take k (unzip2 stk0) = range 0 k.
- case: (hstk) => + _ - <-; rewrite int2bs_strikeE // -/k.
  rewrite ones_cat ones_nseq1 take_cat_le ?size_range ifT 1://#.
  by rewrite take_oversize  // size_range /#.
have le_stk_root: forall x, x \in stack{hr} => x.`2 < root{hr}.`level.
- case=> v i /(subseq_mem _ _ _ hsub) /(map_f snd) /=; case: hstk => <- _.
  rewrite int2bsS // -cats1 ones_cat ones_seq1 pdiv_small /= 1:/# cats0.
  move=> memi; have := le_size_ones (int2bs root{hr}.`level idx{hr}).
  by move/allP => /(_ _ memi) /=; rewrite size_int2bs ler_maxr 1:/#.
have ge0_stk: forall x, x \in stack{hr} => 0 <= x.`2.
- case=> v i /(subseq_mem _ _ _ hsub) /(map_f snd) /=.
  by case: hstk => <- _; move/ge0_ones.

split.
- apply: (subseq_trans _ _ _ _ hsub).
  by rewrite -{2}[stack{hr}](head_behead _ witness) // subseq_cons.

split.
- have: sorted Int.(<) (unzip2 stack{hr}).
  - move: hsub => /(map_subseq snd).
    move=> /(subseq_sorted (Int.(<)) ltz_trans); apply.
    case: (hstk) => <- _; apply: sorted_ones.
  by rewrite -eqs; case: (stack{hr}) => // x1 [] // x2 stk /= /#.

rewrite andbC -andaE; split.
- have /= :=
    eqvredI
      root{hr} pseed{hr} leaves{hr}.[haddr2off root{hr} + idx{hr}] 0
      (unzip1 (take k stk0)) (drop k stk0) (focus{hr} :: stack{hr})
      // // _ _ _.
  - rewrite /= size_map size_take_condle // ifT //.
    pose bs := int2bs (root{hr}.`level + 1) idx{hr}; have: false \in bs.
    - apply/(nthP witness); exists (root{hr}.`level).
      rewrite /bs size_int2bs ler_maxr 1:/#; split; 1: smt().
      by rewrite nth_mkseq 1:/# /= pdiv_small.
    by rewrite -index_mem -/k; smt(size_int2bs).
  - move=> l /mapP[] [v' i'] /= [] hin <<-. (* FIXME: refactor *)
    rewrite size_zip size_map size_take_condle // ifT 1:/#.
    rewrite size_range ler_maxr 1:/# minzz.
    by move/(map_f snd): hin => /=; apply: hlt.
  - rewrite /= size_map size_take_condle // ifT 1:/#.
    rewrite -stk0_k_sndE -map_take zip_unzip cat_take_drop.
    by rewrite /haddr2off [2^_ * _]mulrC.
  case=> v' i' stk' [#] ->> eqstk ?.
  rewrite size_zip size_map size_take_condle // ifT 1:/#.
  rewrite size_range ler_maxr // minzz => ? ->> _ /=.
  have ne_i'_k: i' <> k.
  - apply/negP => ->>; move: eqstk.
    rewrite -stk0_k_sndE -map_take zip_unzip.
    rewrite drop_oversize ?size_take ~-1:/# /=.
    apply/negP => ->>; have ?: k < size stk0 by smt(drop_oversize).
    move: eqs => /=; rewrite nth_drop //= -(nth_map _ witness snd) 1:/#.
    rewrite &(gtr_eqF) &(hlt) map_drop -{2}[stk0](cat_take_drop k).
    rewrite map_cat nth_cat size_map ifF; 1: by rewrite size_take //#.
    rewrite size_take_condle // ifT 1:/# /= map_drop.
    by rewrite mem_nth ?size_drop 1:/# size_map /#.
  rewrite {1}exprSr // divzMr ?expr_ge0 // eqidx /=.
  rewrite -divzMr ?expr_ge0 // -exprSr //.
  have {eqstk}->: stack{hr} = drop i' stk0.
  - rewrite eqstk -stk0_k_sndE -map_take zip_unzip &(eq_sym).
    rewrite -{1}[stk0](cat_take_drop k) drop_cat_le.
    by rewrite size_take_condle // !ifT ~-1://#.
  case _: (drop i' stk0) => // hd tl eq_stk0_i' /=.
  have tlE: tl = drop (i'+1) stk0.
  - move/(congr1 (drop 1)): eq_stk0_i'.
    by rewrite drop_drop //= drop0 [1+_]addrC.
  rewrite revones_cons divzDr.
  - rewrite &(dvd_pow2_revones) 1:/# => x.
    case/(nthP witness) => i; rewrite size_map tlE.
    case=> [?]; rewrite map_drop nth_drop ~-1://# => <<-.
    case: (hstk) => + _ - <-; apply: le_nth_ones; ~-1:smt().
    case: (hstk) => + _ - /(congr1 size); rewrite size_map => ->.
    by smt(size_drop).
  rewrite pdiv_small // expr_ge0 //=.
  rewrite exprS //; suff: (2^hd.`2 <= 2^i') by smt(expr_gt0).
  apply: ler_weexpn2l => //; suff ->//: hd.`2 = i'.
  move/(congr1 (map snd)): eq_stk0_i' => /=.
  move/(congr1 (head witness)) => /= <-.
  rewrite map_drop -head_drop //; case: (hstk) => + _ - <-.
  rewrite int2bs_strikeE -/k // ones_cat ones_nseq1 nth_cat ifT.
  - by rewrite size_range /#.
  - by rewrite nth_range /#.

move=> {eqidx} eqidx /=; apply: (eqvred_trans _ _ _ _ _ h).
move: hfcs; rewrite -nth0_head.
case _: (focus{hr}) eqidx => v1 i1 /= E1 eqidx lei1.
have ?: 0 <= i1 < root{hr}.`level by smt().
have <- /= := head_behead stack{hr} witness //.
case _: (head witness _) => v2 i2 /=.
rewrite -nth0_head => /(congr1 snd) /=; rewrite eqs E1 /= => <<-.
have /= := eqvredR root{hr} pseed{hr} (behead stack{hr}) v2 v1 i1.
rewrite [_ * 2^_]mulrC -/(haddr2off _) !divzDl ~-1://.
- by rewrite /haddr2off dvdz_mulr dvdz_exp2l /#.
- by rewrite /haddr2off dvdz_mulr dvdz_exp2l /#.
by rewrite -eqidx.
qed.

(* -------------------------------------------------------------------- *)
lemma treehash_ath_body_ll : islossless TreeHash.th_abody.
proof. by proc; islossless. qed.

(* -------------------------------------------------------------------- *)
lemma treehash_ath_body_pcorrect
    (_pseed  : pseed)
    (_leaves : value list)
    (_root   : haddress)
    (_offset : int)
    (_idx    : int)
    (_focus  : stack1)
    (_stack  : stack)
    (stk0    : stack)
  :
     phoare[TreeHash.th_abody :
          arg = (_pseed, _leaves, _root, _offset, _idx, _focus, _stack)
       /\ size _leaves = 2^h
       /\ valid_haddress _root
       /\ 0 <= _idx < 2 ^ _root.`level
       /\ _stack <> []
       /\ _stack.[0].`2 = _focus.`2
       /\ ath_inv _root _pseed _focus _offset _idx _leaves _stack stk0
     ==>
          let focus = res.`3 in
          let stack = res.`4 in
          ath_inv _root _pseed focus _offset _idx _leaves stack stk0
          /\ (let top  = _stack.[0].`1 in
              let addr = {| level = _focus.`2; index = (_offset + _idx) %/ (2^(_focus.`2 + 1)) |} in
                 stack = behead _stack
              /\ focus = (hash _pseed addr top _focus.`1, _focus.`2 + 1))
     ] = 1%r.
proof. move=> *.
by conseq
     treehash_ath_body_ll
     (treehash_ath_body_correct _pseed _leaves _root _offset _idx _focus _stack stk0).
qed.

(* -------------------------------------------------------------------- *)
lemma treehash_correct (_pseed : pseed) (_leaves : value list) (_root : haddress) :
     size _leaves = 2^h
  => valid_haddress _root
  => hoare[TreeHash.th :
         arg = (_pseed, _leaves, _root)
       ==>
         res = reduce_tree _pseed _leaves _root
     ].
proof.
move=> 2?; have ? := ge0_h; have ?: 0 <= _root.`level by smt().

proc; sp.
while (
     0 <= idx <= 2^(root.`level)
  /\ offset = root.`index * 2^root.`level
  /\ pseed = _pseed
  /\ root = _root
  /\ leaves = _leaves
  /\ stackrel _root _pseed leaves idx stack
); last first.
- auto=> |>; rewrite stackrel0 expr_ge0 //=.
  move=> idx stk 3? [h1 h2]; have ->>: idx = 2^(_root.`level) by smt().
  have stk2E: unzip2 stk = [_root.`level].
  - by move: h1; rewrite ones_pow2 //= eq_sym.
  have ?: 0 < size stk by rewrite -(size_map snd) stk2E.
  have := h2 stk.[0] _; first by apply: mem_nth => /=.
  move=> ->; rewrite -(nth_map _ witness snd) //= stk2E /=.
  rewrite int2bs_pow2 ?mem_range 1:/# /=.
  rewrite nseq0 cats1 drop_oversize /=.
  - by rewrite size_rcons size_nseq /#.
  by rewrite /= -nseq1 bs2int_nseq_false expr0 /= /#.

sp; wp => /=; exlim stack => stk0.

while (
     0 <= idx < 2^(root.`level)
  /\ pseed = _pseed
  /\ root = _root
  /\ leaves = _leaves
  /\ ath_inv _root _pseed focus offset idx _leaves stack stk0
); last first.
- auto=> @/ath_inv |> &hr 2? h * /=; split.
  - rewrite subseq_refl eqvred_refl /=; split=> [nt_stk0|].
    - case: h => + _ - ^he /(congr1 (fun s => nth witness s 0)) /=.
      rewrite (nth_map witness) /= -1:-nth0_head.
      - by rewrite ltz_def size_ge0 /= size_eq0.
      move=> <-; apply: (ge0_ones (int2bs (_root.`level + 1) idx{hr})).
      move/(congr1 size): he; rewrite size_map => hsz.
      by rewrite &(mem_nth) /= hsz ltz_def size_ge0 /= size_eq0.
    - rewrite expr0 /=; case: (h) => <- _; rewrite revonesK //#.

  move=> fcs0 stk1 hfin hsub hfcs hred hidx; split; first by smt().
  have := stackrelS _root _pseed _leaves idx{hr} stk0 // // // h.
  pose k := List.index _ _; pose v := foldl _ _ _.
  suff //: (v, k) :: drop k stk0 = fcs0 :: stk1.

  have ge0_k: 0 <= k by apply: index_ge0.
  pose v0 := _leaves.[haddr2off _root + idx{hr}].
  have := eqvredI_cmpl _root _pseed v0 k (take k stk0) (drop k stk0) fcs0 stk1 ge0_k.
  move/(_ _ _ _ _ _ _) => //.
  - rewrite map_take; case: (h) => <- _; rewrite int2bs_strikeE //.
    rewrite ones_cat take_cat_le ifT.
    - by rewrite size_ones -/k count_nseq /= ler_maxr.
    by rewrite ones_nseq1 -/k take_oversize ?size_range //#.
  - pose bs := int2bs (_root.`level + 1) idx{hr}; have: false \in bs.
    - apply/(nthP witness); exists (_root.`level).
      rewrite /bs size_int2bs ler_maxr 1:/#; split; 1: smt().
      by rewrite nth_mkseq 1:/# /= pdiv_small.
    by rewrite -index_mem -/k; smt(size_int2bs).
  - move=> l; rewrite map_drop; case: (h) => <- _; rewrite int2bs_strikeE //.
    rewrite -/k ones_cat drop_cat_le ifT -1:drop_oversize /=;
      ~-1: by rewrite ones_nseq1 /= size_range /#.
    rewrite size_nseq ler_maxr 1:/# -cat1s ones_cat.
    rewrite ones_seq1 /= -map_comp.
    rewrite (_ : _ \o _ = (+) (k + 1)) 1:/#.
    case/mapP=> i [hi ->]; rewrite ltzE ler_addl.
    by move/ge0_ones: hi.
  - smt().
  - by rewrite -cat1s -catA cat_take_drop /v0 /haddr2off [2^_ * _]mulrC.
  - move=> -> /= @/v; rewrite take_take /= cat_take_drop -/v0.
    case: (h) => <- _; apply: eq_foldl => //=.
    by move=> *; rewrite revonesK.

proc change [1..4] : {
  (top, addr, focus, stack) <@ TreeHash.th_abody(
    pseed, leaves, root, offset, idx, focus, stack);
}; first by inline {2} *; auto.

exlim offset, idx, focus, stack => _offset _idx _focus _stack.
call (treehash_ath_body_correct _pseed _leaves _root _offset _idx _focus _stack stk0).
by auto.
qed.

(* ==================================================================== *)
lemma treehash_ll : islossless TreeHash.th.
proof.
proc.
sp.
while true (2^(root.`level) - idx).
- move=> z; wp; while true (size stack).
  - by move=> z'; auto=> &hr |> * /#.
  - auto=> &hr |> *; split.
    - by rewrite ler_eqVlt ltrNge size_ge0 /= size_eq0 /#.
    - smt().
- by auto=> &hr |> /#.
qed.

(* ==================================================================== *)
lemma treehash_pcorrect (_pseed : pseed) (_leaves : value list) (_root : haddress) :
     size _leaves = 2^h
  => valid_haddress _root
  => phoare[TreeHash.th :
         arg = (_pseed, _leaves, _root)
       ==>
         res = reduce_tree _pseed _leaves _root
     ] = 1%r.
proof.
by move=> *; conseq treehash_ll (treehash_correct _pseed _leaves _root _ _).
qed.
