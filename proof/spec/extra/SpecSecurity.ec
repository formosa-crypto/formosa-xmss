require import AllCore IntDiv List Distr DList StdOrder RealExp.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.
require import Array8.

require (****) XMSS_TW.
require import XMSS_PRF.
import Params Types XMSS_Types Hash WOTS Address LTree BaseW.

import IntOrder.

op BitsToBytes (bits : bool list) : W8.t list = map W8.bits2w (chunk W8.size bits).
op BytesToBits (bytes : W8.t list) : bool list = flatten (map W8.w2bits bytes).
op W64toBytes_ext (x : W64.t) (l : int) : W8.t list =
  rev (mkseq (fun i => nth W8.zero (to_list (W8u8.unpack8 x)) i) l).


(* Axiomitize operator for now) *)
(* FIXME: Proper ltree operator *)
op ltree : Top.WOTS.wots_pk -> adrs -> Top.WOTS.seed -> Params.nbytes.
(* FIXME: Prove this with proper operator *)
axiom Eqv_Ltree_ltree (pkWOTS : Top.WOTS.wots_pk) (ad : adrs) (ps : Top.WOTS.seed) :
  hoare[LTree.ltree : arg = (pkWOTS, ad, ps) ==> ltree pkWOTS ad ps = res].

(* Get checksum from XMSS_Checksum and then plug those results
   here *)

clone import XMSS_TW as XMSS_ABSTRACT with
  type mseed <- nbytes,
  op dmseed <- (dmap ((dlist W8.dword Params.n)) NBytes.insubd),
  type mkey <- nbytes * int,
  type msgXMSSTW <- W8.t list,
  type FLXMSSTW.SA.WTW.pseed <- nbytes,
  op FLXMSSTW.SA.WTW.dpseed <- (dmap ((dlist W8.dword n)) NBytes.insubd),
  type FLXMSSTW.SA.WTW.sseed <- nbytes,
  op FLXMSSTW.SA.WTW.dsseed <- (dmap ((dlist W8.dword n)) NBytes.insubd),
  type FLXMSSTW.SA.HAX.Adrs.sT <- adrs,
  op FLXMSSTW.n <- n,
  op FLXMSSTW.h <- h,
  op FLXMSSTW.log2_w <- ilog 2 w,
  op FLXMSSTW.chtype <= 0,
  op FLXMSSTW.pkcotype <= 1,
  op FLXMSSTW.trhtype <= 2,
  op mkg = (fun (ms : nbytes) (i : FLXMSSTW.SA.index) =>
        let padding =  W64toBytes_ext prf_padding_val padding_len in
        let in_0 = toByte (W32.of_int (FLXMSSTW.SA.Index.val i)) 4 in
        (Hash (padding ++ NBytes.val ms ++ in_0), FLXMSSTW.SA.Index.val i)),
  op FLXMSSTW.SA.WTW.prf_sk =
    (fun (ss : nbytes) (psad : nbytes * adrs) =>
     let adbytes = addr_to_bytes (set_key_and_mask psad.`2 0) in
     (DigestBlock.insubd
      (BytesToBits
       (NBytes.val
        (prf_keygen (NBytes.val psad.`1 ++ NBytes.val adbytes) ss))))),
  op FLXMSSTW.SA.WTW.thfc =
    (fun (i : int) (ps : nbytes) (ad : adrs) (x : bool list) =>
     if i = 8 * n then
      (let adbytes0 = addr_to_bytes (set_key_and_mask ad 0) in
       let k = prf adbytes0 ps in
       let adbytes1 = addr_to_bytes (set_key_and_mask ad 1) in
       let bitmask = prf adbytes1 ps in
       (DigestBlock.insubd
        (BytesToBits
         (NBytes.val
          (_F k (NBytes.insubd (bytexor (BitsToBytes x) (NBytes.val bitmask))))))))
     else if i = 8 * n * 2 then
      (let xw = BitsToBytes x in
       let l = take (size xw %/ 2) xw in
       let r = drop (size xw %/ 2) xw in
       (DigestBlock.insubd
        (BytesToBits
         (NBytes.val
          (rand_hash (NBytes.insubd l) (NBytes.insubd r) ps ad)))))
     else if i = 8 * n * len then
      (let wpk = LenNBytes.insubd (map NBytes.insubd (chunk n (BitsToBytes x))) in
       (DigestBlock.insubd
        (BytesToBits
         (NBytes.val
          (ltree wpk ad ps))))) (* FIXME: Proper ltree operator *)
     else witness)
proof FLXMSSTW.val_log2w, FLXMSSTW.dist_adrstypes.
realize FLXMSSTW.val_log2w.
case: w_vals => ->; [left | right; left].
+ by rewrite (: 4 = 2 ^ 2).
by rewrite (: 16 = 2 ^ 4).
qed.
realize FLXMSSTW.dist_adrstypes by trivial.


import FLXMSSTW SA WTW HtS Repro MCORO.

op bs2block(a : nbytes) = DigestBlock.insubd (BytesToBits (NBytes.val a)).
op block2bs(a : dgstblock): nbytes = NBytes.insubd (BitsToBytes (DigestBlock.val a)).

module FakeRO : POracle = {
   var root : nbytes

   proc o(x : (nbytes * int) * W8.t list) : msgFLXMSSTW = {
      var t,idx_bytes;
      idx_bytes <- toByte (W32.of_int x.`1.`2) 4;
      t <- (ThreeNBytesBytes.insubd (NBytes.val x.`1.`1 ++ NBytes.val root ++ idx_bytes));
      return bs2block (H_msg t x.`2);
   }
}.
op skrel(ask : skXMSSTW, sk : xmss_sk) =
   ask.`1 = sk.`sk_seed /\
   ask.`2.`1 = Index.insubd (to_uint sk.`idx) /\
   ask.`2.`2 = sk.`sk_prf  /\
   ask.`2.`3 = sk.`pub_seed_sk
   (* ask.`2.`4 = ??? Why is the address in/not in the sk/pk? *)
   (* ??? = sk.`pk_root Why is the root not in/in the sk? *).

op pkrel(apk : pkXMSSTW, pk : xmss_pk) =
   apk.`1 = DigestBlock.insubd (BytesToBits (NBytes.val pk.`pk_root)) /\
   apk.`2 = pk.`pk_pub_seed
   (* apk.`3 = ??? Why is the address in the sk/pk? *)
   (* ??? = pk.`pk_oid I guess abstract proofs fon't care about oid *).

(* Notes:
- We have a full binary tree with  h+1 levels (height = h), so 2^h leaves
  (and 2^(h + 1) - 1 total nodes, i.e., leaves and inner nodes combined).
- Levels are indexed from bottom to top, leaves at level 0, root at level h
- The length of a full path to a leaf is h
- The length of the path to a node at level l \in [0..h] is h - l (root path is [])
- The path to a leaf can be extracted from the bit representation of its index:
    the i-th leaf can be found at path rev (bits h i)
- throughout we will need the corner case of the leaf with index 2^h when
  we exit the loop, where everything works in a tree of height h+1
*)

type path = bool list.

(* The hamming weight of a path determines the size of the stack *)
op hw (p : path) = count (pred1 true) p.

(* The path of a leaf; we need the corner case of leaf 2^h for exiting the loop *)
op lpath (lidx : int) =
  rev (BS2Int.int2bs (h + (b2i (lidx = 2^h))) lidx).

(*
                     +
               +           +
           +      +     +     +
          0 1    2 3   4 5   6 7 

path to 5 = 1 0 1 => stack contains [0] and [1 0 0]
path to 6 = 1 1 0 => stack contains [0] and [1 0]

*)

(* The paths of all the sibling nodes of 1-bit choices in a leaf path *)
op paths_from_leaf (lidx : int) : path list =
  if (lidx = 2^h) then [[]] (* we get the root *) else

  pmap (fun i =>
    let p = take i (lpath lidx) in
    if   last false p
    then Some (rcons (take (i - 1) p) false)
    else None
  ) (range 0 (h + 1)).

lemma size_lpath (lidx : int) :
  0 <= lidx <= 2^h => size (lpath lidx) = if lidx = 2^h then (h+1) else h.
proof.
by move=> hle @/lpath; rewrite size_rev BS2Int.size_int2bs; smt(h_g0).
qed.

lemma size_lpath_lt (lidx : int) :
  0 <= lidx < 2^h => size (lpath lidx) = h.
proof. by move=> ?; rewrite size_lpath /#. qed.

(* Move to List *)
lemma count_eq_nth ['a] (p : 'a -> bool) (s1 s2 : 'a list) :
     size s1 = size s2
  => (forall k, 0 <= k < size s1 => p (nth witness s1 k) = p (nth witness s2 k))
  => count p s1 = count p s2.
proof. 
elim: s1 s2 => [|x1 s1 ih] [|x2 s2] //=; ~-1:smt(size_ge0).
by move/addzI => eq_sz heqp; rewrite (heqp 0) ?(ih s2); smt(size_ge0).
qed.

lemma paths_from_leaf_root : paths_from_leaf (2^h) = [[]].
proof. by done. qed.

hint simplify paths_from_leaf_root.

lemma lpath_root : lpath (2 ^ h) = true :: nseq h false.
proof.
have h_g0 := h_g0; move=> @/lpath @/b2i /=.
rewrite BS2Int.int2bs_pow2 ?mem_range 1:/# /=.
by rewrite nseq0 rev_cat /= rev_nseq.
qed.

hint simplify lpath_root.

lemma size_pmap ['a 'b] (p : 'a -> 'b option) (s : 'a list) :
  size (pmap p s) = count (fun x => is_some (p x)) s.
proof. by elim: s => //= x s ih; case: (p x) => /=; rewrite ih. qed.

lemma rev_iota i j : rev (iota_ i j) = map (fun k => (i + j) - (k + 1)) (iota_ 0 j).
proof.
elim/natind: j i => [j le0_j|j ge0_j ih] i; first by rewrite !iota0.
rewrite iotaSr // iotaS // rev_rcons map_cons ih /=; split; first smt().
by rewrite (iota_addl 1 0) -map_comp /(\o) /#.
qed.

lemma rev_mkseq ['a] (f : int -> 'a) (n : int) :
  rev (mkseq f n) = mkseq (fun i => f (n - (i + 1))) n.
proof. by rewrite /mkseq -map_rev rev_iota map_comp. qed.

lemma lpath_intdivE (lidx : int) : 0 <= lidx < 2^h =>
  lpath lidx = mkseq (fun i => (lidx %/ 2^(h - (i + 1))) %% 2 <> 0) h.
proof.
move=> rg @/lpath; rewrite [lidx = _]ltr_eqF 1:/# b2i0 /=.
by rewrite /BS2Int.int2bs rev_mkseq.
qed.

lemma hw_lpathE (lidx : int) : 0 <= lidx < 2^h =>
  hw (lpath lidx) = count (fun i => lidx %/ 2^(h - (i + 1)) %% 2 <> 0) (range 0 h).
proof. by move=> hrg; rewrite lpath_intdivE // /hw count_map /#. qed.

lemma pfl_size (lidx : int) :
  0 <= lidx <= 2^h => size (paths_from_leaf lidx) = hw (lpath lidx).
proof.
have h_ge0 := h_g0; move=> [ge0_lidx] /lez_eqVlt [->> /=|lt_lidx].
- by rewrite /hw /= count_nseq iffalse //=.
rewrite /paths_from_leaf iffalse 1:/# size_pmap /=.
rewrite -(eq_in_count (fun i => nth false (false :: lpath lidx) i)) /=.
- move=> i /mem_range rg_i; rewrite fun_if /= (last_nth false).
  rewrite size_take_condle 1:/# iftrue 1:size_lpath_lt ~-1://#.
  by case: (i = 0) => -> //=; rewrite nth_take //#.
rewrite /hw range_ltn 1:/# /= add0z (range_add 0 _ 1) count_map.
rewrite /preim /= -(eq_in_count (nth false (lpath lidx))) /=.
- by move=> i /mem_range /#.
have ->: nth false (lpath lidx) = preim (nth false (lpath lidx)) (pred1 true).
- by apply/fun_ext => i @/preim /#.
rewrite -count_map; congr; have ->: h = size (lpath lidx).
- by rewrite size_lpath_lt //.
by apply: (map_nth_range false (lpath lidx)).
qed.

(* The list of leaves that are under a node given by a path *)
op leaves_from_path (p : path) =
 if 0 <= size p <= h then
    let hsub = h - size p in
    mkseq (fun i => BS2Int.bs2int (rev p) * 2^hsub + i) (2^hsub)
 else witness.

lemma lfp_leaf lidx : 0 <= lidx < 2^h => (leaves_from_path (lpath lidx)) = [lidx].
proof.
move=> rg_lidx @/leaves_from_path; rewrite size_lpath_lt 1:/# /=.
have h_gt0 := h_g0; rewrite iftrue 1:/# mkseq1 /=.
by rewrite /lpath revK BS2Int.int2bsK /#.
qed.

lemma lfp_nil : leaves_from_path [] = range 0 (2^h).
proof.
have h_gt0 := h_g0; rewrite /leaves_from_path ifT 1:/# /=.
by rewrite rev_nil BS2Int.bs2int_nil /= /mkseq id_map //#.
qed.

(* The leaf node corresponding to a leaf path
   The semantics of this needs to be computed from wots using
   operators and then proved equivalent to the imperative code. *)
op leafnode_from_idx(ss ps : Params.nbytes, ad : SA.adrs, lidx : int) : dgstblock.

(* list of all the leaves up to an index, exclusive *)
op leaf_range(ss ps : Params.nbytes, ad : SA.adrs, lidx : int) =
   map (leafnode_from_idx ss ps ad) (range 0 lidx).

lemma leaf_range0 ss ps ad : leaf_range ss ps ad 0 = [].
proof. by rewrite /leaf_range range_geq. qed.

(* The node corresponding to an arbitrary path  *)
op node_from_path (p : bool list, ss ps : Params.nbytes, ad : SA.adrs) : dgstblock =
 if size p = h 
 then leafnode_from_idx ss ps ad (BS2Int.bs2int (rev p))
 else if 0 <= size p <= h 
      then let ls = leaves_from_path p in
           let nls = map (leafnode_from_idx ss ps ad) ls in
           let subtree = list2tree nls in
               (val_bt_trh subtree ps (set_typeidx ad trhtype) 
                   (h - size p) (head witness ls))   
      else witness.

(* The full stack state when one starts to process leaf lidx *)
op stack_from_leaf (lidx : int, ss ps : Params.nbytes, ad : SA.adrs) : (dgstblock * int) list =
  map (fun p => (node_from_path p ss ps ad, (h - size p))) (paths_from_leaf lidx).

lemma sfl_size lidx ss ps ad :
  0 <= lidx <= 2^h => size (stack_from_leaf lidx ss ps ad) = hw (lpath lidx).
proof. by move=> hrg; rewrite /stack_from_leaf size_map pfl_size //#. qed.

(* The list of leaves that fall under the first node in the stack when one starts to process leaf lidx
   The case o lidx=0 is a corner case, as the stack is empty *)
op first_subtree_leaves(lidx : int,ss ps : Params.nbytes, ad : SA.adrs) =
 if lidx = 0 then
   []
 else
   let lps = (paths_from_leaf lidx) in
   let p1 = head witness lps in
   let lp1 = leaves_from_path p1 in
   map (leafnode_from_idx ss ps ad) lp1.

(* The hamming weight of 0 is 0, so stack is empty *)
lemma pfl0 : paths_from_leaf 0 = [].
proof.
have expr_gt0 := expr_gt0; apply/size_eq0.
by rewrite pfl_size 1?hw_lpathE /= -1:count_pred0 //#.
qed.

lemma stack_from_leaf0 ss ps ad : stack_from_leaf 0 ss ps ad = [].
proof. by rewrite /stack_from_leaf pfl0. qed.

(* This op describes the state of the stack in the inner loop, while
   reducing, where o is the current offset = size of stack = sfl ++ [rednode].
   There are two cases: either the hw increased by one, then there
   is nothing to do. Or it has decreased and we enter the loop.
   The loop performs as many iterations as needed to reduce the
   hamming weight of lidx to hamming weight of lidx+1, if any. *)
op stack_increment (lidx : int, ss ps : Params.nbytes, ad : SA.adrs, offset : int) =
  (* the stack configuration is the state encountered for lidx
     with the extra node computed for lidx at the end *)
  let hwi = hw (lpath lidx) in
  let hwi1 = hw (lpath (lidx + 1)) in
  if hwi < hwi1
  (* Then then case only happens when lidx is even, in which
     case we are already in the state we need on exit *)
  then stack_from_leaf lidx ss ps ad ++
          [(node_from_path (lpath lidx) ss ps ad, 0)]
  else
      (* we reach this point with hw1 <= offset <= hw + 1
         we still did not touch the first (offset - 1) positions in the old stack
         the node stored at offset - 1 corresponds to the node reduced along the 
         path to lidx that we can also compute *)
      let oldstack = stack_from_leaf lidx ss ps ad in
      let level = (nth witness oldstack (offset - 2)).`2 in
      let carrypath = (take (h - level) (lpath lidx))
      in (take (offset - 1) (stack_from_leaf lidx ss ps ad)) ++
                        [(node_from_path carrypath ss ps ad, level)].

(* Overflows may happen unless h is upper bounded *)
axiom h_max : h < 32.

lemma l_max : l < 4294967296 
  by rewrite -pow2_32 /l;apply WOTS_TW.gt_exprsbde;  smt(h_g0 h_max). 

require import IntMin.

hint simplify b2i0, b2i1.

lemma hw_rev (p : bool list) : hw (rev p) = hw p.
proof. by rewrite /hw count_rev. qed.

lemma hw_cat (p1 p2 : bool list) : hw (p1 ++ p2) = hw p1 + hw p2.
proof. by rewrite /hw count_cat. qed.

lemma hw_cons (b : bool) (p : bool list) : hw (b :: p) = b2i b + hw p.
proof. by rewrite /hw /pred1; case: b. qed.

hint simplify hw_cons.

lemma hw_nseq (n : int) (b : bool) : 0 <= n => hw (nseq n b) = b2i b * n.
proof. by move=> ge0_n @/hw; rewrite count_nseq /pred1 /=; case: b => //#. qed.

lemma int2bs_enlarge (N1 N2 k : int) :
  0 <= N1 <= N2 => 0 <= k < 2^N1 => 
    BS2Int.int2bs N2 k = BS2Int.int2bs N1 k ++ nseq (N2 - N1) false.
proof.
move=> [ge0_N1 leN] [ge0_k ltk]; apply/(eq_from_nth false).
- by rewrite size_cat size_nseq !BS2Int.size_int2bs 1:/#.
rewrite BS2Int.size_int2bs lez_maxr 1:/# => i rgi.
rewrite nth_cat BS2Int.size_int2bs lez_maxr //.
case: (i < N1) => [lt_iN1|ge_iN1].
- by rewrite /int2bs !nth_mkseq /= //#.
rewrite /int2bs nth_mkseq ?nth_nseq /= ~-1://#.
rewrite pdiv_small // ge0_k /=; suff: 2^N1 <= 2^i by smt().
by apply: ler_weexpn2l => //#.
qed.

lemma hw_cat_pow2 (N k n1 n2 : int) :
     0 <= k
  => 0 <= n1
  => 0 <= n2 < 2^k
  => (n1 * 2^k + n2) < 2^N
  =>   hw (BS2Int.int2bs N (n1 * 2^k + n2))
     = hw (BS2Int.int2bs N n1) + hw (BS2Int.int2bs N n2).
proof.
have ? := expr_gt0; move=> *; have ?: k < N by admit.
rewrite (BS2Int.int2bs_cat k N) ~-1:/# hw_cat addrC; congr.
- rewrite divzMDl 1:/# pdiv_small //=.
  rewrite (int2bs_enlarge (N - k) N) 1://#.
  - split=> // _; apply: (ltr_pmul2r (2^k)); first smt().
    by rewrite -exprD_nneg //#.
  by rewrite hw_cat hw_nseq /= /#.
- rewrite -BS2Int.int2bs_mod modzMDl pmod_small //.
  by rewrite (int2bs_enlarge k N) ~-1://# hw_cat hw_nseq /= //#.
qed.

lemma int2bs_pow2B1 (N k : int) :
  0 <= k <= N => BS2Int.int2bs N (2^k - 1) = nseq k true ++ nseq (N - k) false.
proof.
have ? := expr_gt0; move=> ?; apply: BS2Int.inj_bs2int_eqsize.
- by rewrite BS2Int.size_int2bs size_cat !size_nseq /#.
rewrite BS2Int.int2bsK 1:/#.
- by split=> [|_]; [|rewrite ltzE /= &(ler_weexpn2l)]; smt().
by apply/eq_sym/BS2Int.bs2int_cat_nseq_true_false.
qed.

lemma hw_pow2B1 (N k : int) :
  0 <= k <= N => hw (BS2Int.int2bs N (2^k - 1)) = k.
proof.
move=> rg_k; rewrite int2bs_pow2B1 // /hw count_cat.
by rewrite !count_nseq /pred1 /=; smt().
qed.

lemma hwincSE (N lidx : int) :
     0 <= N
  => 0 <= lidx
  => lidx + 1 < 2^N
  => let k = argmax (fun i => take i (BS2Int.int2bs (N+1) lidx)) (all idfun) in
     hw (BS2Int.int2bs N (lidx + 1)) = hw (BS2Int.int2bs N lidx) + 1 - k.
proof.
move=> ge0_N ge0_ldx lt_lidxS k.
have lt_lidx: lidx < 2 ^ N by smt().
have lt_lidx' : lidx < 2 ^ (N+1) by rewrite exprSr //#.
suff: hw (BS2Int.int2bs (N+1) (lidx + 1)) = hw (BS2Int.int2bs (N+1) lidx) + 1 - k.
- by rewrite !(int2bs_enlarge N (N + 1)) ~-1:/# !hw_cat hw_nseq /#.
move: @k; (pose f i := take i (BS2Int.int2bs (N + 1) lidx)) => k.
have := argmaxP_r f (List.all idfun) 0 (N+1) // _ _ _; 1,2: smt(take0).
- move=> l lt_Nl @/f; apply/negP => /all_nthP.
  move/(_ false N _); first by rewrite size_take ?BS2Int.size_int2bs /#.
  rewrite nth_take ~-1:/# /BS2Int.int2bs nth_mkseq ~-1:/# /idfun /=.
  by rewrite pdiv_small //#.
rewrite -/k => [# ge0_k allones hz]; have: k <= N.
- case: (k <= N) => // /ltzNge => lt_Nk; move/List.allP: allones.
  move/(_ (nth false (BS2Int.int2bs (N + 1) lidx) N)_).
  - rewrite /f -(nth_take _ k) // mem_nth ge0_N /=.
    by rewrite size_take_condle // BS2Int.size_int2bs /#.
  by rewrite /idfun /int2bs nth_mkseq ~-1:/# /= pdiv_small.

move=> le_kN; have: BS2Int.int2bs (N + 1) lidx =
  nseq k true ++ false :: BS2Int.int2bs (N - k) (lidx %/ 2^(k+1)).
- rewrite (BS2Int.int2bs_cat k (N+1)) ~-1://#; congr.
  - rewrite &(eq_from_nth false) BS2Int.size_int2bs ?size_nseq //.
    rewrite lez_maxr // => i rg_i; rewrite nth_nseq //.
    move/all_nthP: allones => /(_ false i _) @/idfun /=.
    - by rewrite /f size_take_condle // BS2Int.size_int2bs /#.
    rewrite /f nth_take ~-1://# /BS2Int.int2bs.
    by rewrite !nth_mkseq ~-1://# => /= ->.
  rewrite (BS2Int.int2bs_cat 1 (N + 1 - k)) ~-1://#.
  rewrite {1}/BS2Int.int2bs mkseq1 /=; split.
  - move/(_ (k + 1) _): hz; ~-1:smt().
    rewrite -has_predC => /hasP[b] [] @/predC @/idfun @/f.
    rewrite (take_nth false) ?BS2Int.size_int2bs ~-1://#.
    rewrite mem_rcons /=; case.
    - by rewrite /BS2Int.int2bs nth_mkseq ~-1://# /= => -> ->.
    by move=> b_in; move/List.allP: allones => /(_ b b_in) /#.
  - rewrite (_ : N + 1 - k - 1 = N - k) 1:#ring.
    by rewrite -divzMr 1?exprSr //; smt(expr_ge0).

move/(congr1 BS2Int.bs2int); rewrite BS2Int.int2bsK ~-1://#.
rewrite -cat1s catA BS2Int.bs2int_cat -nseq1.
rewrite {1}(_ : 1 = (k + 1) - k) 1:#ring.
rewrite BS2Int.bs2int_cat_nseq_true_false ~-1:/#.
rewrite size_cat !size_nseq /= !lez_maxr ~-1:/#.
rewrite BS2Int.int2bsK 1:/#; first split=> [|_].
- by rewrite divz_ge0 // expr_gt0.
- rewrite ltz_divLR; first smt(expr_gt0).
  by rewrite -exprD_nneg //#.

move/lez_eqVlt: le_kN; case=> [->|lt_kz].
- rewrite pdiv_small 1:exprSr ~-1://# /= => -> /=.
  rewrite BS2Int.int2bs_pow2 ?mem_range ~-1://# /=.
  rewrite int2bs_pow2B1 ~-1://# [N+1-N]addrAC /=.
  by rewrite !hw_cat /= !hw_nseq //= #ring.

have: 0 <= lidx %/ (2 ^ (k + 1)) < 2^(N - (k+1)).
- split=> [|_]; first by rewrite divz_ge0; smt(expr_gt0).
  rewrite ltz_divLR; first smt(expr_gt0).
  by rewrite -exprD_nneg //#.

move: (lidx %/ (2^(k+1))) => hi rg_hi ->.
have hlt: hi * 2 ^ (k + 1) + 2 ^ k < 2 ^ (N + 1).
- rewrite [2^(N+1)]exprSr // (_ : 2^N * 2 = 2^N + 2^N) 1:#ring.
  rewrite ltr_le_add //; last by apply: ler_weexpn2l => //#.
  have ->: N = (N - (k + 1) + (k + 1)) by ring.
  rewrite [2^(_ + (k+1))]exprD_nneg ~-1:/#.
  by apply: ltr_pmul2r; smt(expr_gt0).
 
rewrite addrAC ![_ + _*hi]addrC ![_*hi]mulrC !hw_cat_pow2 /=.
- smt(). - smt(). - by rewrite exprSr //=; smt(expr_gt0). (* FIXME *)
- smt(). - smt(). - smt().
- by rewrite exprSr //; smt(expr_gt0). - smt().

rewrite /= -!addrA; congr; rewrite hw_pow2B1 ~-1:/# addrCA /=.
rewrite BS2Int.int2bs_pow2 ?mem_range ~-1://#.
by rewrite hw_cat /= !hw_nseq //#.
qed.

(* hw increases by exactly 1 *)
lemma hwinc lidx :
      0 <= lidx < 2^h
   => hw (lpath lidx) < hw (lpath (lidx+1))
   => hw (lpath (lidx+1)) = hw (lpath lidx) + 1.
proof.
have ? := h_g0; move=> [ge0_lidx lt_lidx]; have: lidx + 1 <= 2^h by smt().
rewrite lez_eqVlt; case; last first.
- move=> lt_Slidx; have := hwincSE h lidx _ _ _; ~-1: by move=> //#.
  rewrite /lpath !hw_rev ![_ = 2^h]ltr_eqF //=; (pose k := argmax _ _) => ->.
  by (have ge0_k: 0 <= k by apply: ge0_argmax) => /#.
- move=> SlidxE @/lpath; rewrite !hw_rev SlidxE /= ltr_eqF //=.
  have ->: lidx = 2^h - 1 by smt().
  rewrite BS2Int.int2bs_pow2 ?mem_range ~-1:/# /= nseq0.
  rewrite int2bs_pow2B1 ~-1:/# /= nseq0 cats0 hw_cat /=.
  by rewrite !hw_nseq ~-1://# /= /hw /= /#.
qed.

(* we don't enter the loop if hw increased *)
lemma hwinc_noentry lidx ss ps ad offset: 
   0 <= lidx < 2^h =>
    hw (lpath lidx) < hw (lpath (lidx + 1)) =>
   let si = stack_increment lidx ss ps ad offset in
    ((size si < 2) \/
     (2 <= size si /\
       (nth witness si (size si - 1)).`2 <>
         (nth witness si (size si - 2)).`2)).
admitted.

(* hw increase implies odd, so last node in paths is the previous leaf *)
lemma hwinc_leaflast lidx : 
   0 <= lidx < 2^h =>
    hw (lpath lidx) < hw (lpath (lidx + 1)) =>
      size (nth witness (paths_from_leaf (lidx + 1)) (hw (lpath lidx))) = h /\
      lidx = BS2Int.bs2int (rev (nth witness (paths_from_leaf (lidx + 1)) (hw (lpath (lidx + 1)) - 1))).
admitted.

(* hw increase implies all previous paths same as before *)
lemma hwinc_pathsprev lidx k : 
   0 <= lidx < 2^h =>
    hw (lpath lidx) < hw (lpath (lidx + 1)) =>
     0 <= k < hw (lpath lidx) =>
      (nth witness (paths_from_leaf (lidx + 1)) k)
      = (nth witness (paths_from_leaf lidx) k).
admitted.

(* hw decrease implies even, so last node in old stack is leaf *)
lemma hwnoinc_leaflast lidx : 
   0 <= lidx < 2^h => 
    hw (lpath (lidx + 1)) <= hw (lpath lidx)  =>
     (0 < hw (lpath lidx) /\ 
     size (nth witness (paths_from_leaf lidx) ((size (paths_from_leaf lidx)) - 1)) = h).
admitted.


(* if inner loop exited, then we have reached the final stack size *)
lemma hwdec_exit lidx ss ps ad offset : 
   0 <= lidx < 2^h =>
   hw (lpath (lidx + 1)) <= hw (lpath lidx) =>
   hw (lpath (lidx + 1)) <= offset <= hw (lpath lidx) + 1 =>
   let si = stack_increment lidx ss ps ad offset in
    ((size si < 2) \/
     (2 <= size si /\
       (nth witness si (size si - 1)).`2 <>
         (nth witness si (size si - 2)).`2)) =>
     (offset = hw (lpath (lidx + 1)) + 1 /\
      size si = hw (lpath (lidx + 1))).
admitted.


(* final state of stack after reduction *)
lemma stack_final lidx ss ps ad :
  0 <= lidx < 2^h =>
  forall k, 0 <= k < hw (lpath (lidx + 1)) =>
  nth witness (stack_increment lidx ss ps ad (hw (lpath (lidx + 1)) + 1))  k =
  nth witness (stack_from_leaf (lidx + 1) ss ps ad) k.
move => ? k *.
case (hw (lpath (lidx + 1)) <= hw (lpath lidx)) => *;last first.
+ rewrite /stack_increment /= ifT 1:/#.
  rewrite nth_cat sfl_size 1:/#.
  case (k < hw (lpath lidx)) => *. 
  +  have := hwinc_pathsprev lidx k _ _ _. smt(). smt(). smt().
     rewrite /stack_from_leaf !(nth_map witness) /=; smt(pfl_size).
  rewrite ifT;1:smt(hwinc).
  have ->: k = hw (lpath (lidx + 1)) - 1 by smt(hwinc).
  rewrite /stack_from_leaf !(nth_map witness) /=;1: smt(pfl_size).
  have := hwinc_leaflast lidx _ _;1,2: smt(). 
  move => [H H1];split; last  by smt(hwinc pfl_size).  
  admit. 
admitted.

lemma si_size_in_loop  lidx ss ps ad offset :
0 <= lidx < 2^h =>
hw (lpath (lidx + 1)) <= hw (lpath lidx) =>
hw (lpath (lidx + 1)) <= offset <= hw (lpath lidx) + 1 =>
   size (stack_increment lidx ss ps ad offset) = offset.
move => *; rewrite /stack_increment /= ifF 1:/#.
rewrite size_cat /= size_take. admit. 
by smt(sfl_size).
qed.

(* 
lemma si_heights_in_loop lidx ss ps ad offset :
0 <= lidx < 2^h =>
hw (lpath (lidx + 1)) <= hw (lpath lidx) =>
hw (lpath (lidx + 1)) <= offset <= hw (lpath lidx) + 1 =>
(nth witness
   (stack_increment lidx ss ps ad offset) 
  (offset - 2)).`2 = .
admitted.


lemma si_heights_in_loop_bnd lidx ss ps ad offset k :
0 <= lidx < 2^h =>
hw (lpath (lidx + 1)) <= hw (lpath lidx) =>
hw (lpath (lidx + 1)) <= offset <= hw (lpath lidx) + 1 =>
0<= k < offset =>
 0<= (nth witness
   (stack_increment lidx ss ps ad offset) k).`2 < h - 1.
move => *.
admitted. 
*)

(* growth of leaves under the leftmost subtree *)
lemma growth ss ps ad leaves lidx :
0 <= lidx < 2^h =>
size leaves = lidx =>
 take (size (first_subtree_leaves (size leaves) ss ps ad)) leaves =
   first_subtree_leaves (size leaves) ss ps ad =>
 take (size (first_subtree_leaves (lidx + 1) ss ps ad))
   (rcons leaves (leafnode_from_idx ss ps ad lidx)) =
 first_subtree_leaves (lidx + 1) ss ps ad.
admitted.

(* FD + WR *)
equiv kg_eq : XMSS_TW(FakeRO).keygen ~ XMSS_PRF.kg : ={arg} ==> pkrel res{1}.`1 res{2}.`2 /\ skrel res{1}.`2 res{2}.`1.
proof.
have ? := h_g0; have ? := expr_gt0.
proc. inline {1} 2. inline {1} 5. inline {1} 8.
inline {2} 5. inline {2} 10.
swap {2} [5..7] -4; seq 3 3 : (NBytes.val ms{1} = sk_seed0{2} /\ NBytes.val ss{1} = sk_prf0{2} /\ NBytes.val ps{1} = pub_seed0{2}).
+ do 3!(rnd NBytes.val NBytes.insubd); auto => />.
   have H := supp_dlist W8.dword n.
   have Hn:= Params.ge0_n.
   split => *;1: smt(NBytes.insubdK NBytes.valK Params.ge0_n supp_dlist).
   split => *;1: (rewrite dmapE; apply mu_eq_support => x Hx;smt(NBytes.valK)).
   split => *;1:smt(NBytes.valP supp_dmap).
   split => *;1: smt(NBytes.insubdK NBytes.valK Params.ge0_n supp_dlist).
   smt(NBytes.valP supp_dmap).

sp 7 14;wp;conseq
    (: _ ==> (val_bt_trh (list2tree leafl0{1}) ps{1} (set_typeidx (XAddress.val witness) trhtype) h 0 =
              DigestBlock.insubd (BytesToBits (NBytes.val (nth witness stack{2} 0))))).
+ by auto => /> &1 *;smt(NBytes.valK). 
while (size leafl0{1} = i{2} /\ 0 <= i{2} <= 2^h /\ t{2} = h /\ s{2} = 0 
    /\ ps{1} = pub_seed1{2}
    /\ (forall k, 0<=k<3 => address0{2}.[k] = W32.zero)
    /\  size stack{2} = h + 1 /\ size heights{2} = h + 1
    /\ leafl0{1} = leaf_range  ss{1} ps{1} ad{1} i{2}
    /\ (let firstleaves = first_subtree_leaves i{2} ss{1} ps{1} ad{1} in
           take (size firstleaves) leafl0{1} = firstleaves)
    /\ (let stacklist = stack_from_leaf i{2} ss{1} ps{1} ad{1} in
      to_uint offset{2} = size stacklist /\
      forall k, 0 <= k < size stacklist =>
        bs2block (nth witness stack{2} k) =
          (nth witness stacklist k).`1 /\
        to_uint (nth witness heights{2} k) =
          (nth witness stacklist k).`2)); last first.
+ auto => /> &1; do split.
  + by smt(expr_ge0).
  + by smt(NBytes.valK).
  + by smt(Array8.initiE Array8.get_setE).
  + by smt(size_nseq).
  + by smt(size_nseq).
  + by rewrite leaf_range0.
  + by rewrite stack_from_leaf0.
  + by move=> 2?; rewrite stack_from_leaf0 /= /#.
  + move => leafs1 hs1 o1 st2 9? Hl 2? H.
    have @/bs2block -> := (H 0 _) => /=; first by smt().
    rewrite /stack_from_leaf nth0_head /paths_from_leaf /= ifT 1:/# /=.
    rewrite /node_from_path /= ifF 1:/# /= ifT 1:/# lfp_nil; congr; last first.
    - by rewrite -nth0_head nth_range //#.
    + by congr; rewrite Hl /leaf_range; congr => /#.

seq 3 6 : (#pre /\
   leaf{1} = leafnode_from_idx ss{1} ps{1} ad{1} i{2} /\ leaf{1} = bs2block node{2}).
  admit. (* this can be fixed by setting leafnode_from_idx to the correct semantics *)

wp. 
while {2} (
    (hw (lpath i{2}) < hw (lpath (i{2} + 1)) => to_uint offset{2} = hw (lpath (i{2} + 1))) 
 /\ (hw (lpath (i{2} + 1)) <= hw (lpath i{2}) => 
         hw (lpath (i{2} + 1)) <= to_uint offset{2} <= hw (lpath i{2}) + 1)
 /\ i{2} = size leafl0{1} /\ size stack{2} = h + 1 /\ size heights{2} = h + 1 
 /\ ps{1} = pub_seed1{2}
 /\ (forall k, (0<=k<5 \/ k=7) => address0{2}.[k] = (set_type zero_address 2).[k])
 /\   0 <= i{2} < 2 ^ h /\ t{2} = h /\ s{2} = 0 
 /\ leafl0{1} = leaf_range ss{1} ps{1} ad{1} i{2} /\
    (let firstleaves = first_subtree_leaves i{2} ss{1} ps{1} ad{1} in
         take (size firstleaves) leafl0{1} = firstleaves) 
 /\ leaf{1} = leafnode_from_idx ss{1} ps{1} ad{1} i{2} 
 /\ leaf{1} = bs2block node{2}
 /\ (let stacklist = 
      stack_increment i{2} ss{1} ps{1} ad{1} (to_uint offset{2}) in
        to_uint offset{2} = size stacklist
      /\ forall (k : int), 0 <= k < size stacklist =>
          bs2block (nth witness stack{2} k) = (nth witness stacklist k).`1 /\
          to_uint (nth witness heights{2} k) = (nth witness stacklist k).`2))
       (to_uint offset{2}); last first.
+ auto => /> &1 &2 ???????Ho Hs??Hn; pose _lidx := size leafl0{1}.
  have -> /= : offset{2} + W64.one - W64.one = offset{2} by ring.
  rewrite /= !W64.to_uintD_small /=;1: by
   rewrite Ho sfl_size 1:/# /hw; smt(size_lpath count_size BS2Int.size_int2bs h_max).
split. 
(* initialization of inner loop invariant *)
+ rewrite /stack_increment /=.
  pose _olds := (stack_from_leaf _lidx ss{1} pub_seed1{2} ad{1}).
  pose _hw1 := (hw (lpath (_lidx + 1))).
  pose _hw := (hw (lpath (_lidx))).
  have Hsos : size _olds = _hw
      by rewrite /olds /stack_from_leaf size_map; smt(pfl_size h_g0).
  do split.
+ smt(hwinc). 
+ by smt(sfl_size).
+ by smt(size_put).
+ by smt(size_put).
+ move => k kb; rewrite /set_type /zero_address. 
  by rewrite !get_setE 1..10:/#; smt(Array8.initiE).
+ case (_hw < _hw1).
  + by rewrite size_cat;smt(hwinc).
  by move => ?;rewrite -/_lidx size_cat /= size_take; smt(W64.to_uint_cmp). 
+ move => k kbl kbh.
  case (_hw < _hw1) => /= Hw.
  + (* hw increased by 1, so we have to show that the previous stack plus
         the new leaf is really the stack that we will end up with *)
      rewrite !nth_put;1,2: by rewrite Ho sfl_size 1:/# /hw /lpath; smt(size_ge0 size_rev count_size BS2Int.size_int2bs).
      rewrite nth_cat. 
      case(to_uint offset{2} = k) => Hk.
      + (* this is the leaf just added *)
        rewrite ifF 1:/# ifT 1:/# /= -Hn /node_from_path /= ifT;1:smt(size_lpath).
        rewrite revK BS2Int.int2bsK; smt(h_g0).
      + (* this is the previous stack *)
        rewrite ifT;1:smt(sfl_size size_cat). 
        move : (Hs k _);1:  smt(sfl_size size_cat).  
        move => [-> ->]. 
        by rewrite /stack_from_leaf !(nth_map witness) /=;smt(sfl_size pfl_size size_cat).
    + (* reductions will be needed, but we haven't started
         so we have the old stack in the first positions and a
         new leaf at the next position *)
      move : kbh; rewrite Hw /= !size_cat size_take;1:smt(W64.to_uint_cmp). 
      rewrite ifF /=;1: smt(sfl_size).
      move => kbh;rewrite !nth_cat /=. 
      rewrite take_oversize;1:smt().
      case (k < size _olds) => *; 1: by
       rewrite !nth_put;smt(size_ge0 size_rev count_size BS2Int.size_int2bs).
      rewrite !ifT;1: smt(size_cat).
      have -> /= : k = to_uint offset{2}  by smt(sfl_size).
      rewrite !nth_put /=;1,2: by rewrite Ho sfl_size 1:/# /hw /lpath; smt(size_ge0 size_rev count_size BS2Int.size_int2bs).
      have Hnoinc :=  hwnoinc_leaflast _lidx _ _;1,2: smt().
      have -> /= : (nth witness _olds (to_uint offset{2} - 1)).`2 = 0.
      + rewrite /_olds /stack_from_leaf.
        by rewrite (nth_map witness) /=;smt(nth_map pfl_size sfl_size). 
      rewrite take_oversize; 1: smt(size_lpath).
      rewrite /node_from_path ifT;1: smt(size_lpath).
      rewrite -Hn;congr.
      by rewrite /lpath revK /= BS2Int.int2bsK /#.

move => ad2 hs o2 s2;split. 
+ by move => *; rewrite /(\ule) /=;smt(W64.to_uint_cmp).
+ rewrite uleE /= => Hout. 
  have Hout' : to_uint o2 < 2 \/ (2 <= to_uint o2 /\ nth witness hs (to_uint o2 - 1) <> nth witness hs (to_uint o2 - 2)).
  + case (to_uint o2 < 2) => /= *; 1: by smt(). 
    move : Hout;rewrite !to_uintB /=;1,2: by rewrite uleE /= /#. 
    by smt().
  move => ???? Ha2 Ho2  H5.
  rewrite /stack_increment /=.
  pose _hw1 := (hw (lpath (_lidx + 1))).
  pose _hw := (hw (lpath (_lidx))).
do split.
  + by smt(size_rcons).
  + by smt().
  + by smt().
  + move => k kbl kbh; rewrite Ha2 1:/#.
    rewrite /set_type /zero_address. 
    by rewrite !get_setE 1..5:/#; smt(Array8.initiE).
  + by rewrite /leaf_range /range /= iotaSr 1:/# /= map_rcons /#. 
  + rewrite /first_subtree_leaves.
  + by smt(growth). 
  + case (_hw < _hw1) => *;1: by smt(sfl_size).
    have /= := hwdec_exit _lidx ss{1} pub_seed1{2} ad{1} (to_uint o2) _ _ _;1..3:smt().
    by smt(W32.to_uint_eq sfl_size W64.to_uint_cmp).
  + case (_hw < _hw1) => ? k *.
    + case (k < _hw) => *. 
      + have ? := hwinc_pathsprev _lidx k _ _ _;1..3: smt().
      have ? := hwinc_leaflast _lidx _ _;1..2: smt(). 
      
    have /= := hwdec_exit _lidx ss{1} pub_seed1{2} ad{1} (to_uint o2) _ _ _;1..3:smt().
    by smt(W32.to_uint_eq sfl_size W64.to_uint_cmp stack_final).
  + by smt(size_rcons). 
  + by smt(size_rcons).

move => &m z.
conseq (: _ ==> true) (: _ ==> _);1,2:smt(); last first. 
+ (* lossless *)
  by inline *; auto. 
seq 3  :
  (#pre 
  /\ address0 = set_tree_index 
      (set_tree_height (set_type zero_address 2) (to_uint (nth witness heights (to_uint offset - 1)))) 
        (BS2Int.bs2int (rev (take (h - (hw (lpath (size leafl0{m})) - (to_uint offset - 1)) - 1) ( (lpath (size leafl0{m}))))))).
+ auto => /> &hr ??????????Ho Hs; rewrite uleE /= => H H1; rewrite H1.
  move : (Hs (to_uint offset{hr} - 1) _);1: smt(sfl_size).
  move : (Hs (to_uint offset{hr} - 2) _);1: smt(sfl_size).
  move => [# Hs21 Hs22] [# Hs11 Hs12].
  rewrite !to_uintB /=;1: by rewrite uleE /=; smt(). 
  rewrite Hs12 Hs22.

(*   have? : 0 <= hw (lpath (size leafl0{m})) + 1 - to_uint offset{hr} <=
hw (lpath (size leafl0{m})) - hw (lpath (size leafl0{m} + 1)).
  + admit.  *)
  have -> : 
     (to_uint
         (W32.of_int (size leafl0{m}) `>>`
          truncateu8 ((nth witness heights{hr} (to_uint offset{hr} - 2) + W32.one) `&` W32.of_int 31))) = 
     (BS2Int.bs2int (rev (take (h - (hw (lpath (size leafl0{m})) - (to_uint offset{hr} - 1)) - 1) ( (lpath (size leafl0{m})))))); last first.  
  + split;1: by move => *;rewrite /set_tree_index /set_tree_height /=; smt(Array8.get_setE).
    rewrite tP => k kb;rewrite /set_tree_index /set_tree_height /=.
    pose x:= 
       (stack_increment (size leafl0{m}) ss{m} ps{m} ad{m} (hw (lpath (size leafl0{m})) + 1 - to_uint offset{hr})).
    pose y := W32.of_int
    (BS2Int.bs2int
       (rev (take (h - (hw (lpath (size leafl0{m})) - (to_uint offset{hr} - 1)) - 1) (lpath (size leafl0{m}))))).
     case (0<=k<5 \/ k= 7);1:by smt(Array8.get_setE).
     case (k=6);1:by smt(Array8.get_setE).
     move => *; have -> : k=5 by smt(). 
     rewrite !get_setE //=. 
     by move : H1; rewrite !to_uintB ?uleE /=;smt().

  + rewrite /(`>>`) /= to_uint_truncateu8.
    have -> : 31 = 2^5 - 1 by rewrite /=.
    rewrite and_mod //= to_uintD_small /=   Hs22 /=.
    (* + have := si_heights_in_loop_bnd (size leafl0{m}) ss{m} ps{m} ad{m} (hw (lpath (size leafl0{m})) + 1 - to_uint offset{hr}) (to_uint offset{hr} - 2) _ _ _;1:smt(hwinc h_max). admit. admit. smt(). *) admit. 
    rewrite to_uint_shr /=;1: smt(W32.to_uint_cmp).
    rewrite of_uintK  modz_small => /=;1: smt(l_max).
    rewrite of_uintK  modz_small /= 1:/#. 
    rewrite modz_small 1:/#.
    
    rewrite take_rev_int2bs.
    +  admit.
    rewrite revK BS2Int.int2bsK.  admit.
    + split => *;1:smt().
      + have -> /= :  b2i (size leafl0{m} = 2 ^ h) = 0 by smt().
        have -> : (h - (h - (hw (lpath (size leafl0{m})) - (to_uint offset{hr} - 1)) - 1))  = hw (lpath (size leafl0{m})) - to_uint offset{hr} + 2  by ring.
        have -> : h - (hw (lpath (size leafl0{m})) - (to_uint offset{hr} - 1)) - 1 = h - (hw (lpath (size leafl0{m})) - to_uint offset{hr} + 2) by ring.
        admit.
    congr;congr.
    rewrite modz_small.
    + admit. (* have := si_heights_in_loop_bnd (size leafl0{m}) ss{m} ps{m} ad{m} (hw (lpath (size leafl0{m})) + 1 - to_uint offset{hr}) (to_uint offset{hr} - 2) _ _ _;smt(h_max).  *)
    congr.
    have -> /= : b2i (size leafl0{m} = 2 ^ h) = 0 by smt().
    have -> : (h - (h - (hw (lpath (size leafl0{m})) - (to_uint offset{hr} - 1)) - 1))  = hw (lpath (size leafl0{m})) - to_uint offset{hr} + 2  by ring.
    (* have  := si_heights_in_loop (size leafl0{m}) ss{m} ps{m} ad{m} (hw (lpath (size leafl0{m})) + 1 - to_uint offset{hr}) (to_uint offset{hr} - 2) _ _ _;1..3:smt(h_max).
    pose si := (stack_increment (size leafl0{m}) ss{m} ps{m} ad{m} (hw (lpath (size leafl0{m})) + 1 - to_uint offset{hr})).
    have -> : hw (lpath (size leafl0{m})) - to_uint offset{hr} + 2 = 
     (hw (lpath (size leafl0{m})) + 1 - to_uint offset{hr}) + 1 by ring.
   by smt(). *) admit. 

seq 3 : (#pre /\ 
   node0 = nth XMSS_TreeHash.nbytes_witness stack (to_uint offset - 2)
/\  node1 = nth XMSS_TreeHash.nbytes_witness stack (to_uint offset - 1)   
/\   new_node = block2bs  (trh pub_seed1 address0 (BytesToBits (NBytes.val node0) ++ BytesToBits (NBytes.val node1)))).
+ inline *; auto => /> &hr ????????????; rewrite uleE /= => ?. 
   rewrite !to_uintB /=;1,2:by  rewrite ?uleE /=; smt().
   admit. (* semantics needs matching *)

auto => /> &hr ??????????Ho?.
rewrite uleE /= => ?.
rewrite !to_uintB /=;1..2: by rewrite uleE /= /#.
+ rewrite uleE /= to_uintB;by rewrite ?uleE /= /#.
+ by rewrite uleE /= /#.
move => ?;split.
+ do split.
  + move => H; smt(hwinc_noentry).
  + move => *;split;2:smt(). 
    rewrite Ho si_size_in_loop. smt(). admit. admit.
  + admit. 
  + by smt(size_put).
  + by smt(size_put).
  + rewrite si_size_in_loop. smt(). admit. admit. 
  + move => *;split.
    + admit.
    + by smt().
qed.

(* Signature type is abused with two index copies because I need this to simulate
   the actual operation of the implementation *)

op sigrel(asig : sigXMSSTW, sig : sig_t) =
   (*
     asig.`1 = ??? /\ why is the public seed in the signature ?
     MM: it is not, it is the "message key" (generated with "mkg"
     during signing based on the "message seed" and index), which is
     used as the key given to "mco" to compress the message an
     arbitrary-length message to a fixed-length one
     (and this is not the same as the public seed, which is sampled
     in key generation and is used to index the THFs).
   *)
   asig.`1.`1 = sig.`r /\
   asig.`1.`2 = to_uint sig.`sig_idx /\
   asig.`2.`1 = Index.insubd (to_uint sig.`sig_idx) /\
   asig.`2.`2 = DBLL.insubd
     (map (fun (b : nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (LenNBytes.val sig.`r_sig.`1)) /\
   asig.`2.`3 = DBHL.insubd
     (map (fun (b : nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (AuthPath.val sig.`r_sig.`2)).

(* FD + WR *)
equiv sig_eq : XMSS_TW(FakeRO).sign ~ XMSS_PRF.sign : skrel sk{1} sk{2} /\ ={m} ==>
   sigrel res{1}.`1 res{2}.`1 /\  skrel res{1}.`2 res{2}.`2.
proof.
proc. inline {1} 6. inline {1} 8. inline {1} 14. inline {1} 20. inline {2} 7. inline {2} 16. inline {2} 22.
admit.
qed.

(* PY *)
equiv ver_eq : XMSS_TW(FakeRO).verify ~ XMSS_PRF.verify :
       pkrel pk{1} pk{2} /\ ={m} /\ sigrel sig{1} s{2}
    /\ to_uint s{2}.`sig_idx < l
  ==>
    ={res}.
proof.
proc=> /=.
inline{1} 3.
seq 6 9 : (   pkrel pk{1} pk{2}
           /\ to_uint idx_sig{2} < l
           /\ Index.val sigfl{1}.`1 = to_uint idx_sig{2}
           /\ (map DigestBlock.val (DBLL.val sigfl{1}.`2)) = map (BytesToBits \o NBytes.val) (LenNBytes.val sig_ots{2})
           /\ (map DigestBlock.val (DBHL.val sigfl{1}.`3) = map (BytesToBits \o NBytes.val) (AuthPath.val auth{2}))
           /\ DigestBlock.val cm{1} = BytesToBits (NBytes.val _M'{2})
           /\ address{2} = zero_address
           /\ DigestBlock.val pk{1}.`1 = BytesToBits (NBytes.val root{2})
           /\ pk{1}.`2 = _seed{2}
           /\ root{2} = pk{2}.`pk_root).
+ auto => &1 &2 /> eqpk11 eqpk12 eqsig11 eqsig12 eqsig21 eqsig22 eqsig23 ltl_sig.
  do ! split.
  + rewrite eqsig21 Index.insubdK 2://.
    smt(W32.to_uint_cmp).
  + rewrite eqsig22 DBLL.insubdK.
    + admit.
    rewrite -map_comp /=.
    apply eq_map => x @/(\o).
    apply DigestBlock.insubdK.
    admit.
  + rewrite eqsig23 DBHL.insubdK. admit.
    rewrite -map_comp /=.
    apply eq_map => x @/(\o).
    apply DigestBlock.insubdK.
    admit.
  + rewrite /bs2block.
    rewrite DigestBlock.insubdK.
    admit.
    do 4! congr.
    rewrite eqsig11 eqsig12.
    congr; 1: congr.
    admit.
    rewrite to_uintK NBytes.insubdK.
    admit.
    admit (* n = 4? *).
  rewrite eqpk11.
  rewrite DigestBlock.insubdK //.
  admit.
inline{1} verify; inline{2} rootFromSig.
wp.
swap{1} ^pk1<- @^pk0<- & +1.
swap{1} ^root<- @^pk1<- & +1.
sp 3 0.
conseq (_: _ ==> DigestBlock.val root'{1} = BytesToBits (NBytes.val nodes0{2})).
+ move=> /> &1 &2 eqpk1 eqpk2 ltlsig eqsigfl1 eqsigfl2 eqsigfl3 eqcm eqvpk1.
  move=> r0 r1 eqrs.
  rewrite -DigestBlock.valKd eqrs eqpk1.
  admit.
inline{1} root_from_sigFLXMSSTW.
seq 14 11 : (   to_uint idx_sig0{2} < l
             /\ ps0{1} = _seed0{2}
             /\ map DigestBlock.val (DBLL.val pkWOTS0{1}) =  map (BytesToBits \o NBytes.val) (LenNBytes.val pk_ots{2})
             /\ (set_kpidx (set_typeidx ad0{1} pkcotype) (Index.val idx{1})) = address0{2}
             /\ Index.val idx{1} = to_uint idx_sig0{2}
             /\ (DBHL.val ap{1}) = map bs2block (AuthPath.val auth0{2})).
+ admit.
seq 1 3 : (   to_uint idx_sig0{2} < l
           /\ ps0{1} = _seed0{2}
           /\ (set_thtbidx (set_typeidx ad0{1} trhtype) 0 (Index.val idx{1})) = address0{2}
           /\ Index.val idx{1} = to_uint idx_sig0{2}
           /\ leaf{1} = bs2block nodes0{2}
           /\ (DBHL.val ap{1}) = map bs2block (AuthPath.val auth0{2})).
wp.
have ltree_ll : islossless LTree.ltree by admit.
exlim pk_ots{2}, address0{2}, _seed0{2} => pkots2 add02 sd02.
call{2} (_: arg = (pkots2, add02, sd02) ==> res = ltree pkots2 add02 sd02).
by conseq ltree_ll (Eqv_Ltree_ltree pkots2 add02 sd02).
skip => &1 &2 /> ltlidx eqpkots eqidx eqap.
split.
rewrite /trhtype. (* instantiate addresses so that setting entries can be matched...*)
admit.
rewrite /pkco /thfc /=.
rewrite (: 8 * n * XMSS_ABSTRACT.FLXMSSTW.len <> 8 * n). admit.
rewrite (: 8 * n * XMSS_ABSTRACT.FLXMSSTW.len <> 8 * n * 2) /=. admit. (* requires len <> 2... *)
rewrite /bs2block /pkcotype. do 4! congr.
rewrite eqpkots. admit.

exlim nodes0{2}, address0{2} => lf2 ad2.
while{2} (BytesToBits (NBytes.val nodes0{2})
          =
          (let app = drop (h - k{2}) (map bs2block (AuthPath.val auth0{2})) in
           let idp = (rev (BS2Int.int2bs k{2} (to_uint idx_sig0{2}))) in
           let lfp = bs2block lf2 in
           DigestBlock.val (val_ap_trh_gen app idp lfp _seed0{2} ad2 k{2} (to_uint idx_sig0{2} %/ 2 ^ k{2})))
          /\ 0 <= k{2} <= h)
         (h - k{2}).
+ move=> _ z.
  wp.
  proc change 2 : (! odd (to_uint idx_sig0 %/ 2 ^ k)).
  + admit.
  sp.
  have rand_hash_ll : islossless Hash.rand_hash by admit.
  if => //.
  + sp.
    exlim nodes0, auth_k, _seed0, address0 => nds0 apk sd0 ad0.
    call (_: arg = (nds0, apk, sd0, ad0) ==> res = rand_hash nds0 apk sd0 ad0).
    by conseq rand_hash_ll (rand_hash_eq nds0 apk sd0 ad0).
  skip => &1 /> ad01 ih ge0_k _ lth_k cut_even.
  rewrite -!andbA; split => [| /#].
  rewrite (: h - (k{1} + 1) = h - k{1} - 1) 1:/#.
  rewrite (drop_nth witness) 1:size_map 1:AuthPath.valP 1:/# /=.
  rewrite BS2Int.int2bsS 1:// rev_rcons /=.
  rewrite (: to_uint idx_sig0{1} %/ 2 ^ k{1} %% 2 = 0) /=. smt(oddP).
  rewrite (: 2 * (to_uint idx_sig0{1} %/ 2 ^ (k{1} + 1)) = (to_uint idx_sig0{1} %/ 2 ^ k{1})). admit.
  rewrite -ih /trh /thfc (: 8 * n * 2 <> 8 * n) /=; 1: smt(ge1_n).
  rewrite /rand_hash /=. admit.
  + sp.
    exlim auth_k, nodes0, _seed0, address0 => apk nds0 sd0 ad0.
    call (_: arg = (apk, nds0, sd0, ad0) ==> res = rand_hash apk nds0 sd0 ad0).
    by conseq rand_hash_ll (rand_hash_eq apk nds0 sd0 ad0).
  skip => &1 /> ad01 ih ge0_k _ lth_k cut_even.
  rewrite -!andbA; split => [| /#].
  rewrite (: h - (k{1} + 1) = h - k{1} - 1) 1:/#.
  rewrite (drop_nth witness) 1:size_map 1:AuthPath.valP 1:/# /=.
  rewrite BS2Int.int2bsS 1:// rev_rcons /=.
  rewrite (: to_uint idx_sig0{1} %/ 2 ^ k{1} %% 2 <> 0) /=. smt(oddP).
  rewrite (: 2 * (to_uint idx_sig0{1} %/ 2 ^ (k{1} + 1)) + 1 = (to_uint idx_sig0{1} %/ 2 ^ k{1})). admit.
  rewrite -ih /trh /thfc (: 8 * n * 2 <> 8 * n) /=; 1: smt(ge1_n).
  rewrite /rand_hash /=. admit.
wp; skip => &1 &2 /> ltlidx eqidx eqap.
split.
rewrite BS2Int.int2bs0s rev_nil /val_ap_trh_gen -eqap.
rewrite (: h = size (DBHL.val ap{1})) 1:DBHL.valP 1:// drop_size /=.
rewrite /bs2block DigestBlock.insubdK 2://. admit.
move => kr nds0.
split => [/# | /lezNgt geh_kr -> ge0_kr leh_kr].
rewrite (: kr = h) 1:/#.
rewrite /val_ap_trh /= drop0 eqap eqidx.
rewrite (: (to_uint idx_sig0{2} %/ 2 ^ h) = 0).
rewrite -divz_eq0 1:IntOrder.expr_gt0 1://; smt(W32.to_uint_cmp).
have: valid_tbidx 0 (to_uint idx_sig0{2}). admit.
move: (to_uint idx_sig0{2}) => i valtb.
congr.
admit. (* Annoying, but true: th and tb idx is always overwritten *)
qed.
