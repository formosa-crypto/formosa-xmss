require import AllCore List Ring IntDiv BitEncoding StdOrder.
(*---*) import IntOrder BS2Int.

lemma zip0l ['a 'b] s: zip<:'a, 'b> [] s = [].
proof. by case: s. qed.

lemma zip0r ['a 'b] s: zip<:'a, 'b> s [] = [].
proof. by case: s. qed.

lemma take_zip ['a 'b] (k : int) (s1 : 'a list) (s2 : 'b list) :
  take k (zip s1 s2) = zip (take k s1) (take k s2).
proof.
elim/natind: k s1 s2.
- by move=> n le0_n s1 s2; rewrite !take_le0.
move=> n ge0_h ih [|x1 s1] [|x2 s2] //=.
- by rewrite zip0l.
- by rewrite zip0r.
- by rewrite !ifF ~-1:/# /= &(ih).
qed.

abbrev "_.[_]" ['a] (s : 'a list) (i : int) =
  nth witness s i.

op ones (s : bool list) =
  pmap
    (fun ib : _ * _ => if ib.`2 then Some ib.`1 else None)
    (zip (range 0 (size s)) s).

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

lemma subseq_ones (s : bool list) :
  subseq (ones s) (range 0 (size s)).
proof.
apply/subseqP; exists s.
- rewrite size_range /= ler_maxr /= 1:#smt:(size_ge0).
rewrite /ones; elim/last_ind: s => /= [|s b ih].
- by rewrite range_geq.
rewrite size_rcons rangeSr 1:size_ge0.
rewrite -!cats1 mask_cat ?size_range 1:#smt:(size_ge0) /=.
rewrite zip_cat ?size_range 1:#smt:(size_ge0) /=.
by rewrite pmap_cat ih /=; congr; case: b.
qed.

lemma ones_nil : ones [] = [].
proof. by rewrite /ones /= range_geq. qed.

lemma ones_seq1 (b : bool) : ones [b] = if b then [0] else [].
proof.
by rewrite /ones /= range_ltn // range_geq //=; case: b.
qed.

lemma ones_nseq0 (n : int) : ones (nseq n false) = [].
proof.
rewrite /ones pmap_map eq_in_filter_pred0 //=.
case=> //= i /mapP[] [i' b] [] /mem_zip [] _.
by rewrite mem_nseq => -[] _ <-.
qed.

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

lemma sorted_range m n : sorted (<) (range m n).
proof.
case: (n <= m); first by move=> ?; rewrite range_geq.
move/ltzNge => h; rewrite range_ltn 1:/# /=.
pose m' := m + 1; have: m < m' by smt().
rewrite (_ : n = m' + (n - m')) 1:#ring.
pose n' := n - m'; have ge0_n': 0 <= n' by smt().
move: (n') (ge0_n') (m) (m') => {m' n' m n h ge0_n'}.
elim => [|n ge0_n ih] m m' lt_mm' /=; first by rewrite range_geq.
rewrite addrA range_ltn 1:/# /= lt_mm' /=.
by rewrite addrAC ih 1:/#.
qed.

lemma sorted_ones (s : bool list) : sorted (<) (ones s).
proof.
rewrite &(subseq_sorted _ _ _ _ (subseq_ones s)).
- by apply: ltz_trans.
- by apply: sorted_range.
qed.

lemma ge0_ones (s : bool list) : forall x, x \in ones s => 0 <= x.
proof.
move=> x @/ones /pmapP[] [b y] [] /mem_zip /=.
by case=> /mem_range ? _; case: y => //= _ -> /#.
qed.

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

lemma drop_ones (n : int) (s : bool list) : 0 <= n <= size s =>
  let k = size (ones (take n s)) in
  drop k (ones s) = map ((+) n) (ones (drop n s)).
proof.
move=> ? k; rewrite -{1}[s](cat_take_drop n) ones_cat.
rewrite drop_cat_le -/k /= [drop k _]drop_oversize //=.
by rewrite size_take_condle 1:/# ifT 1:/#.
qed.

lemma ones_nseq_false (k : int) : ones (nseq k false) = [].
proof.
rewrite /ones pmap_map eq_in_filter_pred0 //.
move=> io /mapP[] [i b] [] /mem_zip [] _.
by rewrite mem_nseq; case=> _ <- /= ->.
qed.

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

lemma int2bs_strike1 (l n : int) :
  let k = index false (int2bs (1+l) n) in

     0 <= l
  => 0 <= n < 2^l
  => int2bs (1+l) n = nseq k true ++ false :: drop (k+1) (int2bs (1+l) n).
proof.
move=> k ??; have ge0_k: 0 <= k by apply: index_ge0.
have le_kl: k <= l.
- have: (int2bs (l+1) n).[l] \in int2bs (l+1) n.
  - by rewrite mem_nth size_int2bs /#.
  rewrite {2}/int2bs nth_mkseq 1:/# /=.
  by rewrite pdiv_small //= -index_mem size_int2bs /#.
rewrite (int2bs_cat k) 1:/#; congr.
- rewrite &(eq_from_nth witness) !(size_int2bs, size_nseq) //.
  move=> i; rewrite ler_maxr // => rgi; rewrite nth_nseq //.
  have := before_index witness false (int2bs (1+l) n) i //.
  by rewrite !nth_mkseq ~-1:/# /= => /negbFE ->.
rewrite drop_cat size_int2bs ifF 1:/# ler_maxr //.
rewrite [k+1-k]addrAC /= int2bs_cons 1:/# /= drop0 /=.
have := nth_index witness false (int2bs (1+l) n) _.
- by rewrite -index_mem size_int2bs //#.
by rewrite -/k nth_mkseq 1:/# /= => ->.
qed.

lemma int2bs_succ (l n : int) :
  let k = index false (int2bs (1+l) n) in

     0 <= l
  => 0 <= n < 2^l
  => int2bs (1+l) (n + 1)
       = nseq k false ++ true :: drop (k + 1) (int2bs (l+1) n).
proof.
move=> k ??; have ge0_k: 0 <= k by apply: index_ge0.
have le_kl: k <= l.
- have: (int2bs (l+1) n).[l] \in int2bs (l+1) n.
  - by rewrite mem_nth size_int2bs /#.
  rewrite {2}/int2bs nth_mkseq 1:/# /=.
  by rewrite pdiv_small //= -index_mem size_int2bs /#.
have [q nE]: exists q, n = q * 2^k + (2^k - 1).
- exists (n %/ (2^k)); rewrite {1}[n](divz_eq _ (2^k)); congr.
  have := int2bsK l n // //.
  rewrite (int2bs_cat k) // bs2int_cat size_int2bs ler_maxr //.
  move/(congr1 (fun x => x %% 2^k)) => /=.
  rewrite [2^k*_]mulrC modzMDr => <-; rewrite pmod_small.
  - rewrite bs2int_ge0 /= (ltr_le_trans _ _ _ (bs2int_le2Xs _)).
    by rewrite size_int2bs /#.
  suff ->: int2bs k n = nseq k true by rewrite bs2int_nseq_true.
  apply/(eq_from_nth witness); first by rewrite size_nseq size_int2bs.
  move=> i; rewrite size_int2bs ler_maxr // => rgi.
  rewrite nth_nseq //= nth_mkseq //=.
  have := before_index witness false (int2bs (1+l) n) i rgi.
  by rewrite nth_mkseq 1:/# /= => /negbFE ->.
have oddq: !odd q.
- rewrite oddPn (_ : q %% 2 = (n %/ 2^k) %% 2).
  - rewrite nE divzMDl 1:expf_eq0 // pdiv_small //=.
    by smt(expr_gt0).
  have ->: (n %/ 2^k %% 2 = 0) = !(int2bs (1+l) n).[k].
  - by rewrite nth_mkseq 1:/#.
  by rewrite nth_index // -index_mem -/k size_int2bs /#.
have ->: n + 1 = (q + 1) * 2^k by rewrite nE #ring.
rewrite (int2bs_cat k) 1:/# mulzK 1:expf_eq0 //.
rewrite -int2bs_mod modzMl int2bs0 addrAC int2bs_cons 1:/# /=.
rewrite dvdzE -oddP oddS oddq /=; do 2! congr.
rewrite (int2bs_cat (k+1) (l+1)) 1:/#.
rewrite (_ : _ - (k+1) = l - k) 1:#ring.
rewrite drop_cat_le size_int2bs ler_maxr 1:/# /=.
rewrite drop_oversize ?size_int2bs 1:/# /=.
rewrite (_ : 1 - k + l - 1 = l - k) 1:#ring; congr.
rewrite exprSr // divz_mul 1:expr_ge0 // nE.
rewrite divzMDl 1:expf_eq0 //.
rewrite [_ %/ 2^k]pdiv_small /=; first smt(expr_gt0).
by rewrite divzDl //= dvdzE -oddPn.
qed.

op h : int.

axiom ge0_h : 0 <= h.

type value.

op hash : value -> value -> value.

op reduce_tree (leaves : value list) (lvl : int) (index : int) : value.

axiom reduce_tree_leaf (leaves : value list) (index : int) :
  reduce_tree leaves 0 index = leaves.[index].

axiom reduce_tree_node (leaves : value list) (h : int) (index : int) : 0 <= h => 
  reduce_tree leaves (h + 1) index =
    hash (reduce_tree leaves h (2 * index)) (reduce_tree leaves h (2 * index + 1)).

op reduce (leaves : value list) =
  reduce_tree leaves h 0.

op stackrel (leaves : value list) (idx : int) (stk : (value * int) list) =
  let s = int2bs (1 + h) idx in

     (ones s = map (fun (stk1 : value * int) => stk1.`2) stk)
  /\ (forall stk1, stk1 \in stk => stk1.`1 =
        reduce_tree leaves stk1.`2 (bs2int (false :: drop (stk1.`2 + 1) s))).

lemma stackrel0 (leaves : value list) : stackrel leaves 0 [].
proof. by split => //=; rewrite int2bs0 ones_nseq0. qed.

lemma stackrelS (leaves : value list) (idx : int) (stk : (value * int) list) :
  let k = index false (int2bs (1 + h) idx) in

     0 <= idx < 2^h
  => stackrel leaves idx stk
  => stackrel leaves (idx + 1) (
          (foldl (fun v1 v2 => hash v2 v1) leaves.[idx] (unzip1 (take k stk)), k)
       :: drop k stk
     ).
proof.
move=> k rg_idx [h1 h2]; have ? := ge0_h; have le_kh: k <= h.
- have ->: h = size (int2bs (1 + h) idx) - 1 by rewrite size_int2bs /#.
  rewrite ler_subr_addr -ltzE index_mem &(nthP witness).
  exists h; rewrite size_int2bs; split; first smt().
  by rewrite nth_mkseq 1:/# /= pdiv_small.
have ge0_k: 0 <= k by apply: index_ge0.
have ?: k <= size stk.
- rewrite -(size_map snd) -h1 size_ones.
  rewrite int2bs_strike1 // count_cat count_nseq /=.
  by rewrite ler_maxr 1:index_ge0; smt(count_ge0).
split => /=.
- rewrite map_drop -h1 int2bs_succ //= -/k ones_cat.
  rewrite ones_nseq_false size_nseq ler_maxr //=.
  rewrite -cat1s ones_cat /= ones_seq1 /= -map_comp.
  rewrite (_ : _ \o _ = (+) (k + 1)) 1:/#.
  rewrite -drop_ones ?size_int2bs 1:/# [1+h]addrC; congr.
  rewrite [h+1]addrC int2bs_strike1 // -/k.
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
  move/mem_drop/h2 => ->; do 3! congr.
  rewrite int2bs_strike1 // int2bs_succ // -/k.
  rewrite !drop_cat ?size_nseq !ifF ~-1:/#.
  by rewrite !drop_cons !ifT ~-1:/# [1+h]addrC.
rewrite (_ : false :: _ = drop k (int2bs (1+h) idx)).
- rewrite int2bs_succ // eq_sym {1}int2bs_strike1 //= -/k.
  rewrite drop_cat_le size_nseq ifT 1:/#.
  rewrite drop_oversize ?size_nseq 1:/# /=.
  rewrite -cat1s catA cats1 drop_cat_le.
  rewrite size_rcons size_nseq ifT 1:/# /= eq_sym.
  by rewrite drop_oversize ?(size_rcons, size_nseq) 1:/# [1+h]addrC.
move=> {stk1}; move: {1 2 4 5 6}k (ge0_k) (lezz k).
elim=> [|k0 ge0_k0 ih] le_k0_k.
- rewrite take0 /= reduce_tree_leaf drop0.
  by rewrite [1+_]addrC int2bsK ?exprSr //#.
rewrite takeD ~-1://# map_cat /= foldl_cat ih 1:/#.
rewrite (drop_take1_nth witness) /=.
- by split=> //#.
rewrite reduce_tree_node //; congr.
- have -> := h2 stk.[k0] _.
  - by apply: mem_nth => /#.
  suff ->: stk.[k0].`2 = k0 by rewrite bs2int_cons b2i0.
  rewrite -(nth_map _ witness snd) 1:/#.
  rewrite -h1 int2bs_strike1 // ones_cat /= nth_cat ifT.
  - by rewrite ones_nseq1 size_range /= -/k 1:/#.
  by rewrite ones_nseq1 nth_range -/k //#.
- rewrite (drop_nth witness) 1:#smt:(size_int2bs).
  rewrite bs2int_cons [_+2*_]addrC; do 2! congr.
  rewrite int2bs_strike1 // nth_cat ifT.
  - by rewrite size_nseq -/k /#.
  by rewrite nth_nseq 1:/#.
qed.

type stack = (value * int) list.

(* Use "real" inductive predicate *)
(* Meanwhile, we use an impredicative encoding of eqvred *)
op eqvred (s1 s2 : stack) =
  forall (P : stack -> stack -> bool),
     (forall s, P s s)
  => (forall s2 s1 s3, P s1 s2 => P s2 s3 => P s1 s3)
  => (forall s v1 v2 i, P ((v2, i) :: (v1, i) :: s) ((hash v1 v2, i + 1) :: s))
  => P s1 s2.

lemma eqvredW (P : stack -> stack -> bool) :
     (forall s, P s s)
  => (forall s2 s1 s3, P s1 s2 => P s2 s3 => P s1 s3)
  => (forall s v1 v2 i, P ((v2, i) :: (v1, i) :: s) ((hash v1 v2, i + 1) :: s))
  => forall s1 s2, eqvred s1 s2 => P s1 s2.
proof. by move=> 3? s1 s2 @/eqvred /(_ P); apply. qed.

lemma eqvred_refl (s : stack) : eqvred s s.
proof. smt(). qed.

lemma eqvred_trans (s2 s1 s3 : stack) :
  eqvred s1 s2 => eqvred s2 s3 => eqvred s1 s3.
proof. smt(). qed.

lemma eqvredR (s : stack) (v1 v2 : value) (i : int) :
  eqvred ((v2, i) :: (v1, i) :: s) ((hash v1 v2, i + 1) :: s).  
proof. smt(). qed.

lemma eqvredI (v : value) (i : int) (stk1_v : value list) (stk2 stk : stack) :
  let stk1 = zip stk1_v (range i (i + size stk1_v)) in

     (forall (vi : _ * _), vi \in stk2 => (i + size stk1) < vi.`2)
  => eqvred ((v, i) :: stk1 ++ stk2) stk
  => exists v' i' stk',
       let k = i' - i in
            stk = (v', i') :: stk'
         /\ 0 <= k <= size stk1
         /\ stk' = (drop k stk1) ++ stk2
         /\ v' = foldl (fun v1 v2 => hash v2 v1) v (unzip1 (take k stk1)).
proof.                (* FIXME: refactor (zip_drop in transitivity) *)
pose P (s1 s2 : stack) :=
  forall (v : value) (i : int) (stk1_v : value list) (stk2 : stack),
    let stk1 = zip stk1_v (range i (i + size stk1_v)) in

       s1 = ((v, i) :: stk1 ++ stk2)
    => (forall (vi : _ * _), vi \in stk2 => (i + size stk1) < vi.`2)
    => exists v' i' stk',
         let k = i' - i in (
              s2 = (v', i') :: stk'
           /\ 0 <= k <= size stk1
           /\ stk' = (drop k stk1) ++ stk2
           /\ v' = foldl (fun v1 v2 => hash v2 v1) v (unzip1 (take k stk1))
         ).
move=> stk1 h hred.
(have hW := eqvredW P _ _ _ _ _ hred; last by smt());
  move=> {v i stk1_v stk2 stk1 h hred}.
- move=> s @/P => {P} v i stk1_v stk2 stk1 s1E h.
  exists v i (stk1 ++ stk2) => /=; rewrite s1E /=.
  by rewrite size_ge0 /= drop0 take0.

- move=> s2 s1 s3 ih1 ih2 v i stk1_v stk2 stk1 s1E h.
  have [v' i' stk'] := ih1 v i stk1_v stk2 s1E h.
  (pose k := i' - i)  => -[# s2E ge0_k le_k stk'E v'E].
  have {le_k}le_k: k <= size stk1_v.
  - move: le_k; rewrite size_zip size_range addrAC /=.
    by rewrite ler_maxr 1:&(size_ge0) /#.
  have ?: size (take k stk1_v) = k.
  - by rewrite size_take_condle // le_k.
  have ?: size (range i i') = k by rewrite size_range /#.
  have := ih2 v' i' (drop k stk1_v) stk2 _ _.
  - rewrite s2E /= stk'E  (range_cat i') ~-1:/#.
    rewrite -{1}[stk1_v](cat_take_drop k).
    rewrite zip_cat 1:/# drop_cat_le size_zip ifT 1:/#.
    rewrite drop_oversize 1:size_zip 1:/# /=.
    by rewrite size_drop // ler_maxr /#.
  - move=> vi /h; rewrite !size_zip size_range.
    rewrite [i + _ - i]addrAC /= ler_maxr 1:size_ge0 minzz.
    rewrite size_range size_drop // [max _ (size _ - _)]ler_maxr 1:/#.
    by rewrite [i' + _ - i']addrAC /= ler_maxr 1:/# minzz /#.
  case=> [v'' i'' stk'']; (pose k' := i'' - i') => /=.
  move=> [# s3E ge0_k' le_k' stk''E v''E].
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
    rewrite eq_sym (range_cat i') ~-1:/#.
    rewrite -{1}[stk1_v](cat_take_drop k) zip_cat 1:/#.
    rewrite drop_cat_le ifT 1:size_zip 1:/#.
    rewrite [drop k _]drop_oversize 1:#smt:(size_zip) /=.
    by do 3! congr; rewrite size_drop // ler_maxr /#.
  have ->: i'' - i = k + k' by smt().
  rewrite takeD // map_cat foldl_cat -v'E v''E; do 3! congr.
  rewrite /stk1 eq_sym -{1}[stk1_v](cat_take_drop k).
  rewrite (range_cat i') ~-1:/# zip_cat 1:/#.
  rewrite drop_cat_le ifT 1:size_zip 1:/#.
  rewrite [drop k _]drop_oversize 1:#smt:(size_zip) /=.
  by rewrite size_drop // ler_maxr /#.

- move=> s v' v_ i_ @/P v i stk1_v stk2 stk1.
  case=> -[] ->> ->> eq_cat h_hl.
  exists (hash v' v) (i+1) s => /=.
  have /eq_sym eq_stk1_v := head_behead stk1_v witness _.
  - apply/negP => stk1_v_nil; have stk1_nil: stk1 = [].
    - by rewrite /stk1 stk1_v_nil /= range_geq.
    move: eq_cat; rewrite stk1_nil /=; smt().
  have stk1E: stk1 = (head witness stk1_v, i) :: behead stk1.
  - by rewrite /stk1 eq_stk1_v range_ltn 1:#smt:(size_ge0).
  move: eq_cat; rewrite {1}stk1E => -[] [] ->> _ stk'E.
  rewrite addrAC /= stk1E /= ler_addl size_ge0 /=.
  by rewrite drop0 -stk'E take0.
qed.

module TreeHash = {
  proc th(leaves : value list) : value = {
    var index : int;
    var stack : (value * int) list;
    var focus : value * int;
    var top   : value;

    stack <- [];
    index <- 0;
    while (index < 2^h) {
      focus <- (leaves.[index], 0);
      while (stack <> [] /\ stack.[0].`2 = focus.`2) {
        top   <- stack.[0].`1;
        stack <- behead stack;
        focus <- (hash top focus.`1, focus.`2 + 1);
      }
      stack <- focus :: stack;
      index <- index + 1;
    }
    return stack.[0].`1;
  }  
}.

lemma L (_leaves : value list) :
     size _leaves = 2^h
  => hoare[TreeHash.th :
         leaves = _leaves
       ==>
         res = reduce _leaves
     ].
proof.
have ? := ge0_h; move=> *; proc; sp.

while (
     0 <= index <= 2^h
  /\ stackrel leaves index stack
); last first.
- auto=> |>; rewrite stackrel0 expr_ge0 //=.
  move=> idx stk 3? [h1 h2]; have ->>: idx = 2^h by smt().
  have stk2E: unzip2 stk = [h].
  - by move: h1; rewrite [1+h]addrC ones_pow2 //= eq_sym.
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
  have take_k_stk0E: take k (unzip2 stk0) = range 0 k.
  - case: (h) => <- _; rewrite int2bs_strike1 //.
    rewrite ones_cat take_cat_le ifT.
    - by rewrite size_ones -/k count_nseq /= ler_maxr.
    by rewrite ones_nseq1 -/k take_oversize ?size_range //#.
  have ?: k <= size stk0.
  - rewrite -(size_map snd); case: (h) => <- _.
    rewrite size_ones int2bs_strike1 // count_cat.
    by rewrite count_nseq /= -/k ler_maxr // #smt:(count_ge0).
  pose v0 := leaves{hr}.[index{hr}].
  have := eqvredI v0 0 (take k (unzip1 stk0)) (drop k stk0) (fcs0 :: stk1).
  (pose stk1_0 := zip _ _) => /=.
  have stk1_0E: stk1_0 = take k stk0.
  - rewrite /stk1_0 /= size_take_condle //.
    rewrite ifT 1:size_map 1:/# eq_sym.
    by rewrite -{1}[stk0]zip_unzip take_zip take_k_stk0E.
  have sz_stk1_0: size stk1_0 = k.
  - by rewrite stk1_0E size_take_condle // ifT.
  move/(_ _ _).
  - move=> vi /(map_f snd) /=; rewrite map_drop.
    case: (h) => <- _; rewrite int2bs_strike1 //.
    rewrite -/k ones_cat drop_cat_le ifT -1:drop_oversize /=;
      ~-1: by rewrite ones_nseq1 /= size_range /#.
    rewrite size_nseq ler_maxr 1:/# -cat1s ones_cat.
    rewrite ones_seq1 /= -map_comp.
    rewrite (_ : _ \o _ = (+) (k + 1)) 1:/#.
    case/mapP=> i [hi ->]; rewrite sz_stk1_0.
    by rewrite ltzE ler_addl; move/ge0_ones: hi.
  - by rewrite stk1_0E cat_take_drop.
  case=> v' i' stk' [# ->> ->> ge0_i' le_i'] stk'E v'E.
  suff i'E: i' = k; first split.
  - by rewrite v'E /v -/v0 i'E /= stk1_0E take_take.
  - by rewrite stk'E stk1_0E i'E drop_take //= take0.
  move: le_i'; rewrite sz_stk1_0 ler_eqVlt => -[] // lt_'i_k.
  apply: contraR hfin => /= _; rewrite stk'E; split.
  - rewrite -size_eq0 size_cat size_drop // sz_stk1_0.
    by rewrite ler_maxr 1:/# #smt:(size_ge0).
  - rewrite nth_cat size_drop // sz_stk1_0 ifT 1:/#.
    rewrite nth_drop //= -(nth_map _ witness snd) 1:/#.
    rewrite stk1_0E map_take take_k_stk0E.
    by rewrite nth_range /#.

auto=> |> &hr 2? _ h ? eqs; apply: (eqvred_trans _ _ _ h).
have <- /= := head_behead stack{hr} witness //.
case _: (head witness _) => v2 i2 /=.
rewrite -nth0_head => /(congr1 snd) /=; rewrite eqs => <-.
by case: (focus{hr}) => v1 i1 /=; apply: eqvredR.
qed.
