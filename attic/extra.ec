require import AllCore List Ring IntDiv BitEncoding StdOrder.
(*---*) import IntOrder BS2Int.

(* All these results are in PRs. This file is going to be removed in a near future *)
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

lemma drop_zip ['a 'b] (k : int) (s1 : 'a list) (s2 : 'b list) :
  drop k (zip s1 s2) = zip (drop k s1) (drop k s2).
proof.
elim/natind: k s1 s2.
- by move=> n le0_n s1 s2; rewrite !drop_le0.
move=> n ge0_h ih [|x1 s1] [|x2 s2] //=.
- by rewrite zip0l.
- by rewrite zip0r.
- by rewrite !ifF ~-1:/# /= &(ih).
qed.

lemma int2bs_strike1 (l n : int) :
  let k = index false (int2bs (1+l) n) in

     0 <= l
  => 0 <= n < 2^l
  => int2bs (1+l) n = nseq k true ++ false :: drop (k+1) (int2bs (1+l) n).
proof.
move=> k ??; have ge0_k: 0 <= k by apply: index_ge0.
have le_kl: k <= l.
- have: (nth witness (int2bs (l+1) n) l) \in int2bs (l+1) n.
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
- have: nth witness (int2bs (l+1) n) l \in int2bs (l+1) n.
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
  have ->: (n %/ 2^k %% 2 = 0) = !nth witness (int2bs (1+l) n) k.
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
