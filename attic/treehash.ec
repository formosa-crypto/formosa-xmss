(* ==================================================================== *)
require import AllCore List Ring IntDiv BitEncoding StdOrder StdBigop.
(*---*) import IntOrder BS2Int.

(* ==================================================================== *)
abbrev "_.[_]" ['a] (s : 'a list) (i : int) =
  nth witness s i.

(* ==================================================================== *)
op h : { int | 0 <= h } as ge0_h.

type value.
type pseed.

type haddress = { level: int; index: int; }.

op hash : pseed -> haddress -> value -> value -> value.

op reduce_tree : pseed -> value list -> haddress -> value.

axiom reduce_tree_leaf (pseed : pseed) (leaves : value list) (index : int) :
  reduce_tree pseed leaves {| level = 0; index = index |} = leaves.[index].

axiom reduce_tree_node (pseed : pseed) (leaves : value list) (h : int) (index : int) :
  0 <= h => 
  reduce_tree pseed leaves {| level = h + 1; index = index |} =
    hash pseed {| level = h; index = index |} 
      (reduce_tree pseed leaves {| level = h; index = 2 * index     |})
      (reduce_tree pseed leaves {| level = h; index = 2 * index + 1 |}).

op reduce (pseed : pseed) (leaves : value list) =
  reduce_tree pseed leaves {| level = h; index = 0 |}.

(* -------------------------------------------------------------------- *)
type stack1 = value * int.
type stack  = stack1 list.

(* -------------------------------------------------------------------- *)
module TreeHash = {
  proc th(pseed : pseed, leaves : value list) : value = {
    var index : int;
    var stack : stack;
    var focus : stack1;
    var top   : value;
    var addr  : haddress;

    stack <- [];
    index <- 0;
    while (index < 2^h) {
      focus <- (leaves.[index], 0);
      while (stack <> [] /\ stack.[0].`2 = focus.`2) {
        top   <- stack.[0].`1;
        stack <- behead stack;
        addr  <- {| level = focus.`2; index = index %/ (2^(focus.`2 + 1)) |};
        focus <- (hash pseed addr top focus.`1, focus.`2 + 1);
      }
      stack <- focus :: stack;
      index <- index + 1;
    }
    return stack.[0].`1;
  }  
}.

(* ==================================================================== *)
lemma sum_pow2 (k : int) : 0 <= k =>
  Bigint.BIA.bigi predT (fun i => 2^i) 0 k = 2^k - 1.
proof.
elim: k => [|k ge0_k ih]; first by rewrite Bigint.BIA.big_geq ?expr0.
by rewrite Bigint.BIA.big_int_recr 1:/# /= ih addrAC exprS //#.
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


(* ==================================================================== *)
op revones (s : int list) : int =
  Bigint.BIA.big predT (fun i => 2^i) s.

(* -------------------------------------------------------------------- *)
lemma ge0_revones (s : int list) : 0 <= revones s.
proof. by apply: Bigint.sumr_ge0 => /= *; apply: expr_ge0. qed.

(* -------------------------------------------------------------------- *)
lemma revones_cat (s1 s2 : int list) :
  revones (s1 ++ s2) = revones s1 + revones s2.
proof. by rewrite /revones Bigint.BIA.big_cat. qed.

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
lemma dvdz_sum ['a] (f : 'a -> int) (s : 'a list) (v : int) :
     (forall x, x \in s => v %| f x)
  => v %| Bigint.BIA.big predT f s.
proof.
elim: s => [|x s ih] h; first by rewrite Bigint.BIA.big_nil dvdz0.
rewrite Bigint.BIA.big_consT &(dvdzD).
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
op stackrel (pseed : pseed) (leaves : value list) (idx : int) (stk : stack) =
  let s = int2bs (h + 1) idx in

     (ones s = map (fun (stk1 : stack1) => stk1.`2) stk)
  /\ (forall stk1, stk1 \in stk => stk1.`1 =
        let addr = {|
          level = stk1.`2;
          index = (bs2int (false :: drop (stk1.`2 + 1) s));
        |} in
        reduce_tree pseed leaves addr).

(* -------------------------------------------------------------------- *)
lemma stackrel0 (pseed : pseed) (leaves : value list) : stackrel pseed leaves 0 [].
proof. by split => //=; rewrite int2bs0 ones_nseq0. qed.

(* -------------------------------------------------------------------- *)
lemma stackrelS (pseed : pseed) (leaves : value list) (idx : int) (stk : stack) :
  let k = index false (int2bs (h + 1) idx) in

     0 <= idx < 2^h
  => stackrel pseed leaves idx stk
  => stackrel pseed leaves (idx + 1) (
          (foldl
            (fun v1 (v2 : value * int) =>
              let addr = {| level = v2.`2; index = idx %/ 2^(v2.`2 + 1); |} in
              hash pseed addr v2.`1 v1)
            leaves.[idx] (take k stk), k)
       :: drop k stk
     ).
proof.
move=> k rg_idx [h1 h2]; have ? := ge0_h; have le_kh: k <= h.
- have ->: h = size (int2bs (h + 1) idx) - 1 by rewrite size_int2bs /#.
  rewrite ler_subr_addr -ltzE index_mem &(nthP witness).
  exists h; rewrite size_int2bs; split; first smt().
  by rewrite nth_mkseq 1:/# /= pdiv_small.
have ge0_k: 0 <= k by apply: index_ge0.
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
rewrite (_ : false :: _ = drop k (int2bs (h+1) idx)).
- rewrite int2bs_strike_succE // eq_sym {1}int2bs_strikeE //= -/k.
  rewrite drop_cat_le size_nseq ifT 1:/#.
  rewrite drop_oversize ?size_nseq 1:/# /=.
  rewrite -cat1s catA cats1 drop_cat_le.
  rewrite size_rcons size_nseq ifT 1:/# /= eq_sym.
  by rewrite drop_oversize ?(size_rcons, size_nseq) 1:/#.
move=> {stk1}; move: {1 2 4 5 6}k (ge0_k) (lezz k).
elim=> [|k0 ge0_k0 ih] le_k0_k.
- rewrite take0 /= reduce_tree_leaf drop0.
  by rewrite int2bsK ?exprSr //#.
rewrite takeD ~-1://# /= foldl_cat ih 1:/#.
rewrite (drop_take1_nth witness) /=.
- by split=> //#.
rewrite reduce_tree_node //; congr.
- move/(congr1 (fun s => nth witness s k0)): h1 => /=.
  rewrite (nth_map witness) 1:/# /= {1}int2bs_strikeE //=.
  move: (drop _ _) => s'; rewrite ones_cat /=.
  rewrite nth_cat size_ones count_nseq /= -/k.
  rewrite ifT 1:/# ones_nseq1 nth_range 1:/# /= => <- /=.
  by rewrite -bs2int_div 1:/# int2bsK 1:/# //; smt(exprS).
- have -> := h2 stk.[k0] _.
  - by apply: mem_nth => /#.
  suff ->: stk.[k0].`2 = k0 by rewrite bs2int_cons b2i0.
  rewrite -(nth_map _ witness snd) 1:/#.
  rewrite -h1 int2bs_strikeE // ones_cat /= nth_cat ifT.
  - by rewrite ones_nseq1 size_range /= -/k 1:/#.
  by rewrite ones_nseq1 nth_range -/k //#.
- rewrite (drop_nth witness) 1:#smt:(size_int2bs).
  rewrite bs2int_cons [_+2*_]addrC; do 2! congr.
  rewrite int2bs_strikeE // nth_cat ifT.
  - by rewrite size_nseq -/k /#.
  by rewrite nth_nseq 1:/#.
qed.

(* ==================================================================== *)

(* Use "real" inductive predicate *)
(* Meanwhile, we use an impredicative encoding of eqvred *)

op eqvred (pseed : pseed) (s1 s2 : stack) =
  forall (P : stack -> stack -> bool),
     (forall s, P s s)
  => (forall s2 s1 s3, P s1 s2 => P s2 s3 => P s1 s3)
  => (forall s v1 v2 i,
        let addr = {| level = i; index = revones (unzip2 s) |} in
        P ((v2, i) :: (v1, i) :: s) ((hash pseed addr v1 v2, i + 1) :: s))
  => P s1 s2.

(* -------------------------------------------------------------------- *)
lemma eqvredW (pseed : pseed) (P : stack -> stack -> bool) :
     (forall s, P s s)
  => (forall s2 s1 s3, P s1 s2 => P s2 s3 => P s1 s3)
  => (forall s v1 v2 i,
        let addr = {| level = i; index = revones (unzip2 s) |} in
        P ((v2, i) :: (v1, i) :: s) ((hash pseed addr v1 v2, i + 1) :: s))
  => forall s1 s2, eqvred pseed s1 s2 => P s1 s2.
proof. by move=> 3? s1 s2 @/eqvred /(_ P); apply. qed.

(* -------------------------------------------------------------------- *)
lemma eqvred_refl (pseed : pseed) (s : stack) : eqvred pseed s s.
proof. smt(). qed.

(* -------------------------------------------------------------------- *)
lemma eqvred_trans (pseed : pseed) (s2 s1 s3 : stack) :
  eqvred pseed s1 s2 => eqvred pseed s2 s3 => eqvred pseed s1 s3.
proof. smt(). qed.

(* -------------------------------------------------------------------- *)
lemma eqvredR (pseed : pseed) (s : stack) (v1 v2 : value) (i : int) :
  let addr = {| level = i; index = revones (unzip2 s) |} in
  eqvred pseed ((v2, i) :: (v1, i) :: s) ((hash pseed addr v1 v2, i + 1) :: s).  
proof. smt(). qed.

(* -------------------------------------------------------------------- *)
lemma eqvredI (pseed : pseed) (v : value) (i : int) (stk1_v : value list) (stk2 stk : stack) :
  let stk1 = zip stk1_v (range i (i + size stk1_v)) in
  let idx  = revones (unzip2 (stk1 ++ stk2)) in

     0 <= i
  => (forall l, l \in unzip2 stk2 => (i + size stk1) < l)
  => eqvred pseed ((v, i) :: stk1 ++ stk2) stk
  => exists v' i' stk',
       let k = i' - i in
            stk = (v', i') :: stk'
         /\ 0 <= k <= size stk1
         /\ stk' = (drop k stk1) ++ stk2
         /\ v' = foldl (fun v1 (v2 : _ * _) =>
              let addr = {| level = v2.`2; index = idx %/ 2^(v2.`2 + 1) |}  in
              hash pseed addr v2.`1 v1
            ) v (take k stk1).
proof.
pose P (s1 s2 : stack) :=
  forall (v : value) (i : int) (stk1_v : value list) (stk2 : stack),
    let stk1 = zip stk1_v (range i (i + size stk1_v)) in
    let idx  = revones (unzip2 (stk1 ++ stk2)) in

       0 <= i
    => s1 = ((v, i) :: stk1 ++ stk2)
    => (forall l, l \in unzip2 stk2 => (i + size stk1) < l)
    => exists v' i' stk',
         let k = i' - i in (
              s2 = (v', i') :: stk'
           /\ 0 <= k <= size stk1
           /\ stk' = (drop k stk1) ++ stk2
           /\ v' = foldl (fun v1 (v2 : _ * _) =>
                let addr = {| level = v2.`2; index = idx %/ 2^(v2.`2 + 1) |}  in
                hash pseed addr v2.`1 v1
              ) v (take k stk1)
         ).
move=> stk1 idx ge0_i h hred.
(have hW := eqvredW pseed P _ _ _ _ _ hred; last first);
  try (move=> {idx v i ge0_i stk1_v stk2 stk1 h hred}).
- move: hW => /(_ v i stk1_v stk2 _ _ h) // [v' i' stk'] *.
  by exists v' i' stk'.

- move=> s @/P => {P} v i stk1_v stk2 stk1 idx ge0_i s1E h.
  exists v i (stk1 ++ stk2) => /=; rewrite s1E /=.
  by rewrite size_ge0 /= drop0 take0.

- move=> s2 s1 s3 ih1 ih2 v i stk1_v stk2 stk1 idx ge0_i s1E h.
  have [v' i' stk'] := ih1 v i stk1_v stk2 ge0_i s1E h.
  (pose k := i' - i)  => -[# s2E ge0_k le_k stk'E].
  rewrite -/stk1 -/idx => v'E; have {le_k}le_k: k <= size stk1_v.
  - move: le_k; rewrite size_zip size_range addrAC /=.
    by rewrite ler_maxr 1:&(size_ge0) /#.
  have ?: size (take k stk1_v) = k.
  - by rewrite size_take_condle // le_k.
  have ?: size (range i i') = k by rewrite size_range /#.
  have := ih2 v' i' (drop k stk1_v) stk2 _ _ _.
  - smt().
  - rewrite s2E /= stk'E  (range_cat i') ~-1:/#; congr.
    rewrite drop_zip drop_cat_le size_range ifT 1:/#.
    by congr; rewrite drop_oversize 1:/# /= size_drop /#.
  - move=> vi /h; rewrite !size_zip size_range.
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
  rewrite divzDr; first rewrite dvd_pow2_revones ~-1:/#.
  - by move=> x /h @/stk1; rewrite size_zip size_range /#.
  rewrite divzDr; first rewrite dvd_pow2_revones ~-1:/#.
  - by move=> x /h @/stk1; rewrite size_zip size_range /#.
  congr; rewrite map_drop (_ : unzip2 stk1 = range i (i + size stk1_v)).
  - by rewrite /stk1 unzip2_zip 1:#smt:(size_range).
  rewrite drop_range // !revones_range ~-1:/#.
  rewrite !divzDl ?dvdz_exp2l ~-1:/#; congr.
  rewrite !divNz ~-1:expr_gt0 //; do 2! congr.
  rewrite !pdiv_small -1:// subr_ge0 -(ltzE 0) expr_gt0 //=;
    by rewrite ltzE /= ler_weexpn2l /#.

STOP

- move=> s v' v_ addr i_ @/P v i stk1_v stk2 stk1.
  case=> -[] ->> ->> eq_cat h_hl.
  exists (hash pseed witness v' v) (i+1) s => /=.
  have /eq_sym eq_stk1_v := head_behead stk1_v witness _.
  - apply/negP => stk1_v_nil; have stk1_nil: stk1 = [].
    - by rewrite /stk1 stk1_v_nil /= range_geq.
    move: eq_cat; rewrite stk1_nil /=; smt().
  have stk1E: stk1 = (head witness stk1_v, i) :: behead stk1.
  - by rewrite /stk1 eq_stk1_v range_ltn 1:#smt:(size_ge0).
  move: eq_cat; rewrite {1}stk1E => -[] [] ->> _ stk'E.
  rewrite addrAC /= stk1E /= ler_addl size_ge0 /=.
  rewrite drop0 -stk'E take0.
qed.

(* -------------------------------------------------------------------- *)
lemma eqvredI_cmpl (v : value) (k : int) (stk1 stk2 : stack) (fcs : stack1) (stk : stack) :
     0 <= k
  => unzip2 stk1 = range 0 k
  => (forall (vi : _ * _), vi \in stk2 => k < vi.`2)
  => (stk <> [] => (stk.[0]).`2 <> fcs.`2)
  => eqvred ((v, 0) :: stk1 ++ stk2) (fcs :: stk)
  => let v' = foldl (fun v1 v2 => hash v2 v1) v (unzip1 stk1) in
     fcs :: stk = (v', k) :: stk2.
proof.
move=> ge0_k stk1_sndE h_hl hfin heqv v'.
have := eqvredI v 0 (unzip1 stk1) stk2 (fcs :: stk).
have sz_stk1: size stk1 = k.
- by rewrite -(size_map snd) stk1_sndE size_range /#.
(pose stk1_0 := zip _ _) => /=; have -> {stk1_0}: stk1_0 = stk1.
- by rewrite /stk1_0 /= size_map sz_stk1 -stk1_sndE zip_unzip.
move/(_ _ _); ~-1: move=> //#.
case=> v'_ i' stk' [#] ->> <<- ? le_i' stkE v'_E.
suff ->>/=: i' = k; first split.
- by rewrite v'_E /v' take_oversize // sz_stk1.
- by rewrite stkE drop_oversize // sz_stk1.
move: le_i'; rewrite sz_stk1 ler_eqVlt => -[] // lt_'i_k.
have := hfin _; last apply: contraR => _.
- by rewrite -size_eq0 stkE size_cat size_drop // #smt:(size_ge0).
rewrite stkE nth_cat size_drop // sz_stk1 ifT 1:/#.
rewrite nth_drop //= -(nth_map _ witness snd) 1:/#.
by rewrite stk1_sndE nth_range /#.
qed.

(* ==================================================================== *)
lemma treehash_correct (_leaves : value list) :
     size _leaves = 2^h
  => hoare[TreeHash.th : leaves = _leaves ==> res = reduce _leaves].
proof.
have ? := ge0_h; move=> *; proc; sp.

while (
     0 <= index <= 2^h
  /\ stackrel leaves index stack
); last first.
- auto=> |>; rewrite stackrel0 expr_ge0 //=.
  move=> idx stk 3? [h1 h2]; have ->>: idx = 2^h by smt().
  have stk2E: unzip2 stk = [h].
  - by move: h1; rewrite ones_pow2 //= eq_sym.
  have ?: 0 < size stk by rewrite -(size_map snd) stk2E.
  have := h2 stk.[0] _; first by apply: mem_nth => /=.
  move=> ->; rewrite -(nth_map _ witness snd) //= stk2E /=.
  rewrite int2bs_pow2 ?mem_range 1:/# (_ : 1 + h - 1 - h = 0) 1:#ring.
  rewrite nseq0 cats1 drop_oversize /=.
  - by rewrite size_rcons size_nseq /#.
  by rewrite /= -nseq1 bs2int_nseq_false.

sp; wp => /=; exlim stack => stk0.

while (
     0 <= index < 2^h
  /\ stackrel leaves index stk0
  /\ eqvred ((leaves.[index], 0) :: stk0) (focus :: stack)
); last first.
- auto=> |> &hr 2? h *; split; first by apply: eqvred_refl.
  move=> fcs0 stk1 hfin hred; split; first by smt().
  have := stackrelS leaves{hr} index{hr} stk0 // h.
  pose k := List.index _ _; pose v := foldl _ _ _.
  suff //: (v, k) :: drop k stk0 = fcs0 :: stk1.

  have ?: 0 <= k by apply: index_ge0.
  pose v0 := leaves{hr}.[index{hr}].
  have := eqvredI_cmpl v0 k (take k stk0) (drop k stk0) fcs0 stk1.
  move/(_ _ _ _ _ _) => //.
  - rewrite map_take; case: (h) => <- _; rewrite int2bs_strikeE //.
    rewrite ones_cat take_cat_le ifT.
    - by rewrite size_ones -/k count_nseq /= ler_maxr.
    by rewrite ones_nseq1 -/k take_oversize ?size_range //#.
  - move=> vi /(map_f snd) /=; rewrite map_drop.
    case: (h) => <- _; rewrite int2bs_strikeE //.
    rewrite -/k ones_cat drop_cat_le ifT -1:drop_oversize /=;
      ~-1: by rewrite ones_nseq1 /= size_range /#.
    rewrite size_nseq ler_maxr 1:/# -cat1s ones_cat.
    rewrite ones_seq1 /= -map_comp.
    rewrite (_ : _ \o _ = (+) (k + 1)) 1:/#.
    case/mapP=> i [hi ->]; rewrite ltzE ler_addl.
    by move/ge0_ones: hi.
  - smt().
  - by rewrite -cat1s -catA cat_take_drop.

auto=> |> &hr 2? _ h ? eqs; apply: (eqvred_trans _ _ _ h).
have <- /= := head_behead stack{hr} witness //.
case _: (head witness _) => v2 i2 /=.
rewrite -nth0_head => /(congr1 snd) /=; rewrite eqs => <-.
by case: (focus{hr}) => v1 i1 /=; apply: eqvredR.
qed.
