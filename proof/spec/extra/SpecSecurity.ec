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

lemma BitsToBytesK x : 8 %| size x => BytesToBits (BitsToBytes x) = x.
move => Hx.
rewrite /BitsToBytes /BytesToBits.
rewrite -map_comp /(\o) /=.  
have [H _]:= (eq_in_map (fun (x0 : bool list) => w2bits (W8.bits2w x0)) idfun (chunk 8 x)).
rewrite H;1: by move => x0 memX0 /=; rewrite W8.bits2wK; smt(in_chunk_size). 
rewrite map_id chunkK //. 
qed.

lemma BytesToBitsK x : (BitsToBytes (BytesToBits x)) = x.
rewrite /BitsToBytes /BytesToBits.
rewrite flattenK;1,2: smt(mapP W8.size_w2bits).
rewrite -map_comp /(\o).
have [H _]:= (eq_in_map (fun (x0 : W8.t) =>  W8.bits2w (W8.w2bits x0)) idfun x).
rewrite H;1: by move => x0 memX0 /=. 
by smt(map_id).
qed.

op W64toBytes_ext (x : W64.t) (l : int) : W8.t list =
  rev (mkseq (fun i => nth W8.zero (to_list (W8u8.unpack8 x)) i) l).


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
          (ltree ps ad wpk))))) 
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
op extract_path (p : path) (i : int) =
  if   nth false p i
  then Some (rcons (take i p) false)
  else None.

(* we compute paths in subtrees of height t *)
op paths_from_leaf (start lidxo : int, t : int) : path list =
  if (lidxo = 2^t) then [[]] (* we get the root *) else
  pmap (extract_path (drop (h-t) (lpath (start + lidxo)))) (range 0 t).

lemma size_lpath (lidx : int) :
  0 <= lidx <= 2^h => size (lpath lidx) = if lidx = 2^h then (h+1) else h.
proof.
by move : h_g0 => ? hle @/lpath; rewrite size_rev BS2Int.size_int2bs; smt().
qed.

lemma size_lpath_lt (lidx : int) :
  0 <= lidx < 2^h => size (lpath lidx) = h.
proof. by move : h_g0 => ??; rewrite size_lpath /#. qed.

(* Move to List *)
lemma count_eq_nth ['a] (p : 'a -> bool) (s1 s2 : 'a list) :
     size s1 = size s2
  => (forall k, 0 <= k < size s1 => p (nth witness s1 k) = p (nth witness s2 k))
  => count p s1 = count p s2.
proof. 
elim: s1 s2 => [|x1 s1 ih] [|x2 s2] //=; ~-1:smt(size_ge0).
by move/addzI => eq_sz heqp; rewrite (heqp 0) ?(ih s2); smt(size_ge0).
qed.

lemma paths_from_leaf_root s t : paths_from_leaf s (2^t) t = [[]].
proof. rewrite /paths_from_leaf /=.  by smt(dvdzE StdOrder.IntOrder.expr_gt0). qed.

hint simplify paths_from_leaf_root.

lemma lpath_root : lpath (2 ^ h) = true :: nseq h false.
proof.
move => *.
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
move : h_g0 => ? rg @/lpath; rewrite [lidx = _]ltr_eqF 1:/# b2i0 /=.
by rewrite /BS2Int.int2bs rev_mkseq.
qed.

lemma hw_lpathE (lidx : int) : 0 <= lidx < 2^h =>
  hw (lpath lidx) = count (fun i => lidx %/ 2^(h - (i + 1)) %% 2 <> 0) (range 0 h).
proof. by move : h_g0 => ?hrg; rewrite lpath_intdivE // /hw count_map /#. qed.

require import IntMin.

hint simplify b2i0, b2i1.

lemma b2i0_eq (b : bool) : !b => b2i b = 0.
proof. by case: b. qed.

lemma hw_rev (p : bool list) : hw (rev p) = hw p.
proof. by rewrite /hw count_rev. qed.

lemma hw_cat (p1 p2 : bool list) : hw (p1 ++ p2) = hw p1 + hw p2.
proof. by rewrite /hw count_cat. qed.

lemma hw_nil : hw [] = 0.
proof. by done. qed.

hint simplify hw_nil.

lemma ge0_hw (p : path) : 0 <= hw p.
proof. by apply: count_ge0. qed.

lemma hw_cons (b : bool) (p : bool list) : hw (b :: p) = b2i b + hw p.
proof. by rewrite /hw /pred1; case: b. qed.

hint simplify hw_cons.

lemma hw_rcons (p : bool list) (b : bool) : hw (rcons p b) = b2i b + hw p.
proof. by rewrite -cats1 hw_cat /= addrC. qed.

lemma hw_nseq (n : int) (b : bool) : 0 <= n => hw (nseq n b) = b2i b * n.
proof. by move=> ge0_n @/hw; rewrite count_nseq /pred1 /=; case: b => //#. qed.

lemma pfl_r_size (p : path) (n : int) : size p <= n =>
  size (pmap (extract_path p) (range 0 n)) = hw p.
proof.
move=> ltsz; rewrite (range_cat (size p)); ~-1: smt(size_ge0).
rewrite pmap_cat size_cat addrC [size _](_ : _ = 0) /=.
- apply/size_eq0; rewrite pmap_map eq_in_filter_pred0 //.
  move=> @/predC1 /= q /mapP[i]; rewrite mem_range.
  case=> rgi -> @/extract_path /=; rewrite iffalse //.
  by rewrite nth_default 1:/#.
elim/last_ind: {n ltsz} p => //=.
- by move=> @/extract_path /=; rewrite range_geq.
move=> p b ih; rewrite hw_rcons size_rcons.
rewrite rangeSr; first smt(size_ge0).
rewrite -[rcons _ (size _)]cats1 pmap_cat size_cat /=.
rewrite fun_if /= [if _ then _ else _](_ : _ = b2i b).
- by rewrite /extract_path nth_rcons /=; case: b.
rewrite addrC -ih !size_pmap; congr; apply eq_in_count.
move=> x /mem_range [ge0_x ltx] /= @/extract_path.
rewrite nth_rcons [if x < _ then _ else _]iftrue //=.
by case: (nth false p x).
qed.

lemma pfl_r_size_min (p : path) (n : int) : 0 <= n =>
  size (pmap (extract_path p) (range 0 n)) = hw (take n p).
proof.
move=> ge0_n; case: (size p <= n).
- by move=> ?; rewrite take_oversize // &(pfl_r_size).
move/ltzNge => ltn; rewrite -(pfl_r_size _ n).
- by rewrite size_take //#.
rewrite !size_pmap &(eq_in_count) /= => i /mem_range rgi.
rewrite /extract_path nth_take ~-1://#.
by rewrite ![is_some (if nth _ _ _ then _ else _)]fun_if.
qed.


lemma pfl_size (start lidxo : int, t : int) :
 0 <= start <= 2^h - 2^t =>  0 <= t <= h => 0 <= lidxo <= 2^t => 
  size (paths_from_leaf start lidxo t) = hw (drop (h - t) (lpath (start + lidxo))).
proof.
admitted.
(*
move =>  t_bdn. case=> ge0_lidx /lez_eqVlt [->|lt].
rewrite /paths_from_leaf /lpath /= BS2Int.int2bs_pow2;1:smt(mem_range).
- by rewrite /hw /= count_rev count_cat /= !count_nseq iffalse //=.
rewrite /paths_from_leaf [lidx = _]ltr_eqF //=.
rewrite &(pfl_r_size) /lpath [lidx = _]ltr_eqF //=.
by rewrite size_rev BS2Int.size_int2bs lez_maxr //#.
qed.
*)

lemma hw_le_size (p : path) : hw p <= size p.
proof. by rewrite /hw &(count_size). qed.

lemma take_cat' ['a] (n : int) (s1 s2 : 'a list) :
  take n (s1 ++ s2) = take n s1 ++ (take (n - size s1)) s2.
proof.
rewrite take_cat; case: (n < size s1) => ?.
- by rewrite [take (_ - _) _]take_le0 ?cats0 //#.
- by rewrite [take n s1]take_oversize //#.
qed.

lemma pfl_eq (p1 p2 : path) (n k : int) :
     0 <= n
  => 0 <= k
  => (forall n, 0 <= n => hw (take n p1) < k \/ hw (take n p2) < k => take (n+1) p1 = take (n+1) p2)
  => k <= hw p1
  => k <= hw p2
  =>   take k (pmap (extract_path p1) (range 0 n))
     = take k (pmap (extract_path p2) (range 0 n)).
proof.
move=> ge0_n ge0_k eq hw1 hw2; elim: n ge0_n => /= [|n ge0_n ih].
- by rewrite range_geq.
rewrite !rangeSr // -cats1 !pmap_cat /= !take_cat'.
rewrite !pfl_r_size_min // -ih; congr.
case: (hw (take n p1) < k \/ hw (take n p2) < k) => cmp; last first.
- by rewrite ![take (k - _) _]take_le0 //#.
have {eq}eq := eq n ge0_n cmp.
have <-: take n p1 = take n p2.
- by move/(congr1 (take n)): eq; rewrite !take_take iftrue //#.
suff <-: extract_path p1 n = extract_path p2 n by done.
rewrite /extract_path; congr.
- move/(congr1 (fun s => nth false s n)): eq => /=.
  by rewrite !nth_take ~-1://#.
- by move/(congr1 (take n)): eq; rewrite !take_take iftrue //#.
qed.

(* The list of leaves that are under a node given by a path *)
op leaves_from_path (p : path) =
 if 0 <= size p <= h then
    let hsub = h - size p in
    mkseq (fun i => BS2Int.bs2int (rev p) * 2^hsub + i) (2^hsub)
 else witness.

lemma lfp_leaf lidx : 0 <= lidx < 2^h => (leaves_from_path (lpath lidx)) = [lidx].
proof.
move : h_g0=>? rg_lidx @/leaves_from_path; rewrite size_lpath_lt 1:/# /=.
rewrite iftrue 1:/# mkseq1 /=.
by rewrite /lpath revK BS2Int.int2bsK /#.
qed.

lemma lfp_nil : leaves_from_path [] = range 0 (2^h).
proof.
move : h_g0 =>?;rewrite /leaves_from_path ifT 1:/# /=.
by rewrite rev_nil BS2Int.bs2int_nil /= /mkseq id_map //#.
qed.

(* The leaf node corresponding to a leaf path
   The semantics of this needs to be computed from wots using
   operators and then proved equivalent to the imperative code. *)
op wots_pk_val(ss ps : Params.nbytes, ad : SA.adrs, lidx : int) : dgstblocklenlist =
   pkWOTS_from_skWOTS (gen_skWOTS ss ps ad) ps ad.

op leafnode_from_idx(ss ps : Params.nbytes, ad : adrs, lidx : int) : dgstblock =
 let pk = wots_pk_val ss ps (set_kpidx (set_typeidx ad 0) lidx) lidx in
 bs2block (ltree  ps (set_kpidx (set_typeidx ad 1) lidx) (LenNBytes.insubd (map NBytes.insubd (chunk n (BitsToBytes (flatten (map DigestBlock.val (DBLL.val pk)))))))).

lemma Eqv_Ltree_ltree (pkWOTS : wots_pk) (ad : adrs) (ps : seed) :
  phoare[LTree.ltree : arg = (pkWOTS, ad, ps) ==> ltree ps ad pkWOTS = res] = 1%r.
conseq (: _ ==> true) (: _ ==> _);1,2:smt(); last first. 
+ proc. 
  wp; while (true) (_len).
  + move => *.
    wp;while (true) (_len %/ 2 - i).
    move => *.
    inline *;auto => /> /#.
  by auto => /> /#.
 by auto => /> /#.
proc *. ecall (ltree_eq _seed address pk).
by auto => />.
qed.

lemma Eqv_WOTS_pkgen  (ad : adrs) (ss ps : seed) :
  phoare[WOTS.pkGen : arg = (ss, ps, ad) ==>  
     LenNBytes.insubd (map NBytes.insubd (chunk n (BitsToBytes (flatten (map DigestBlock.val (DBLL.val 
       (pkWOTS_from_skWOTS (gen_skWOTS ss ps ad) ps ad)))))))= res] = 1%r.
admitted.

(* list of all the leaves up to an index, exclusive *)
op leaf_range(ss ps : Params.nbytes, ad : SA.adrs, lidx : int) =
   map (leafnode_from_idx ss ps ad) (range 0 lidx).

lemma leaf_range0 ss ps ad : leaf_range ss ps ad 0 = [].
proof. by rewrite /leaf_range range_geq. qed.

(* The node corresponding to an arbitrary path in the full tree  *)
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

(* The full stack state when one starts to process leaf lidx in a subtree of height t *)
op stack_from_leaf (start lidxo : int, ss ps : Params.nbytes, ad : SA.adrs, t : int) : (dgstblock * int) list =
  let prefix = take (h-t) (lpath (start + lidxo)) in
  map (fun p => (node_from_path (prefix ++ p) ss ps ad, (h - size p))) (paths_from_leaf start lidxo t).

lemma sfl_size start lidxo ss ps ad t :
  0 <= start <= 2^h - 2^t => 0<=t <= h => 0 <= lidxo <= 2^t => 
size (stack_from_leaf start lidxo ss ps ad t) = hw (drop (h-t) (lpath (start + lidxo))).
proof. by move=> ?? hrg; rewrite /stack_from_leaf /= size_map pfl_size //#. qed.

(* The list of leaves that fall under the first node in the stack when one starts to process leaf lidx
   The case o lidx=0 is a corner case, as the stack is empty *)
op first_subtree_leaves(start lidxo : int,ss ps : Params.nbytes, ad : SA.adrs, t : int) =
 if lidxo = 0 then
   []
 else
   let prefix = take (h-t) (lpath (start + lidxo)) in
   let lps = (paths_from_leaf start lidxo t) in
   let p1 = head witness lps in
   let lp1 = leaves_from_path (prefix ++ p1) in
   map (leafnode_from_idx ss ps ad) lp1.

(* The hamming weight of 0 is 0, so stack is empty *)
lemma pfl0 s t : 0 <= s <= 2 ^ h - 2 ^ t => 0 <=t<=h => 2^t %| s => paths_from_leaf s 0 t = [].
proof.
move : h_g0 => ????.
have expr_gt0 := expr_gt0; apply/size_eq0.
rewrite pfl_size //=; 1:smt(StdOrder.IntOrder.expr_ge0). 
rewrite /lpath /= /b2i ifF /=;1:smt(StdOrder.IntOrder.expr_gt0).
admit. 
qed.

lemma stack_from_leaf0 s ss ps ad t : 0 <= s <= 2 ^ h - 2 ^ t => 2 ^ t %| s => 0 <= t <= h =>  stack_from_leaf s 0 ss ps ad  t= [].
proof. move => ???; rewrite /stack_from_leaf pfl0 //. qed.


(* This op describes the state of the stack in the inner loop, while
   reducing, where o is the current offset = size of stack = sfl ++ [rednode].
   There are two cases: either the hw increased by one, then there
   is nothing to do. Or it has decreased and we enter the loop.
   The loop performs as many iterations as needed to reduce the
   hamming weight of lidx to hamming weight of lidx+1, if any. *)
op stack_increment (start lidxo : int, t : int, ss ps : Params.nbytes, ad : SA.adrs, offset : int) =
  (* the stack configuration is the state encountered for lidx
     with the extra node computed for lidx at the end *)
  let hwi = hw (drop (h-t) (lpath (start + lidxo))) in
  let hwi1 = hw (drop (h-t) (lpath (start + lidxo + 1))) in
  if hwi < hwi1
  (* Then then case only happens when lidx is even, in which
     case we are already in the state we need on exit *)
  then stack_from_leaf start lidxo ss ps ad t ++
          [(node_from_path (lpath (start + lidxo)) ss ps ad, 0)]
  else
      (* we reach this point with hw1 <= offset <= hw + 1
         we still did not touch the first (offset - 1) positions in the old stack
         the node stored at offset - 1 corresponds to the node reduced along the 
         path to lidx that we can also compute *)
      let oldstack = stack_from_leaf start lidxo ss ps ad t in
      let level = if offset = size oldstack + 1 
                  then 0 (* we always start reducing with a leaf *)
                  else (nth witness oldstack (offset - 1)).`2 + 1 in
      let carrypath = (take (h - level) (lpath (start + lidxo)))
      in (take (offset - 1) oldstack) ++
                        [(node_from_path carrypath ss ps ad, level)].

(* Overflows may happen unless h is upper bounded *)
axiom h_max : h < 32. 
(* We are using multiples of n and len to distinguish which hash to use *)
axiom gt0_n : 0 < n. 
lemma gt2_len : 2 < XMSS_ABSTRACT.FLXMSSTW.len.
rewrite /len /len1 /len2 /= /len1 /len2 /w /w.
admitted. 

lemma l_max : l < 4294967296 
  by rewrite -pow2_32 /l;apply WOTS_TW.gt_exprsbde;  smt(h_g0 h_max). 

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
     0 <= N
  => 0 <= k
  => 0 <= n1
  => 0 <= n2 < 2^k
  => (n1 * 2^k + n2) < 2^N
  =>   hw (BS2Int.int2bs N (n1 * 2^k + n2))
     = hw (BS2Int.int2bs N n1) + hw (BS2Int.int2bs N n2).
proof.
have ? := expr_gt0; move=> *.
case: (n1 = 0) => [->/=|nz_n1]; first by rewrite BS2Int.int2bs0 hw_nseq.
have ?: k < N.
- apply/ltrNge/negP => le_Nk.
  have ?: 2^N <= 2^k by apply: ler_weexpn2l.
  smt().
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

lemma int2bs_incSE (N lidx : int) :
     0 <= N
  => 0 <= lidx
  => lidx + 1 < 2^N
  => let k = argmax (fun i => take i (BS2Int.int2bs N lidx)) (all idfun) in
        (   k < N
         /\ (forall i, 0 <= i < k => nth false (BS2Int.int2bs N lidx) i)
         /\ nth false (BS2Int.int2bs N lidx) k = false
         /\ BS2Int.int2bs N lidx
            = nseq k true ++ false :: drop (k + 1) (BS2Int.int2bs N lidx)
         /\ BS2Int.int2bs N (lidx + 1)
            = nseq k false ++ true :: drop (k + 1) (BS2Int.int2bs N lidx)).
proof.
have ? := expr_gt0; move=> ge0_N ge0_ldx lt_lidxS k.
have lt_lidx: lidx < 2 ^ N by smt().
have lt_lidx' : lidx < 2 ^ (N+1) by rewrite exprSr //#.
move: @k; (pose f i := take i (BS2Int.int2bs N lidx)) => k.
have: exists i, 0 <= i < N /\ nth false (BS2Int.int2bs N lidx) i = false.
- suff: !all idfun (BS2Int.int2bs N lidx).
  - rewrite -has_predC => /hasP[b] @/predC @/idfun /= [+ hNb].
    move/nthP => /(_ false) []; rewrite BS2Int.size_int2bs.
    by rewrite lez_maxr // => i0 [rg_i0 hi0]; exists i0 => /#.
  apply/negP => hones; have: BS2Int.int2bs N lidx = nseq N true.
  - apply/(eq_from_nth false); 1: by rewrite ?size_nseq BS2Int.size_int2bs.
    rewrite BS2Int.size_int2bs lez_maxr // => i rgi.
    rewrite nth_nseq //; move/List.allP: hones.
    move/(_ (nth false (BS2Int.int2bs N lidx) i)).
    move=> @/idfun /= -> //; apply/mem_nth.
    by rewrite BS2Int.size_int2bs lez_maxr.
  move/(congr1 BS2Int.bs2int); rewrite BS2Int.int2bsK ~-1://.
  by rewrite BS2Int.bs2int_nseq_true //#.
case=> i0 [rg_i0 hbit0].
have := argmaxP_r f (List.all idfun) 0 N // _ _ _; 1,2: smt(take0).
- move=> k0 rg_k0; rewrite -has_predC &(hasP).
  exists (nth false (BS2Int.int2bs N lidx) i0).
  rewrite -{1}(nth_take _ k0) ~-1:/# mem_nth /=.
  - by rewrite size_take_condle ~-1:/# BS2Int.size_int2bs /#.
  - by rewrite /predC /idfun /= hbit0.
rewrite -/k => [# ge0_k allones hz]; have: k < N.
- rewrite ltzNge; apply/negP => le_Nk.
  move/all_nthP: allones => /(_ false i0 _).
  - by rewrite size_take // BS2Int.size_int2bs /#.
  by rewrite /idfun nth_take ~-1://# hbit0.
move=> ^lt_kN -> /=; rewrite -!andaE.
split=> [//|allones_k]; last split=> [|?].
- move=> i [ge0_i lt_ik]; move/all_nthP: allones => /(_ false i _).
  - by rewrite size_take_condle // BS2Int.size_int2bs /#.
  by rewrite /idfun /= /f nth_take.
- have := hz (k + 1) _; ~-1: smt().
  rewrite -has_predC => /hasP[b] @/predC @/idfun.
  case=> + hNb - @/f; rewrite (take_nth false).
  - by rewrite ?BS2Int.size_int2bs //#.
  rewrite mem_rcons /=; case=> [<-//#|hmemb].
  by move/List.allP: allones => /(_ _ hmemb) /#.
have: BS2Int.int2bs N lidx =
  nseq k true ++ false :: BS2Int.int2bs (N - (k+1)) (lidx %/ 2^(k+1)).
- apply/(eq_from_nth false).
  - rewrite size_cat /= !BS2Int.size_int2bs /= size_nseq /#.
  rewrite BS2Int.size_int2bs lez_maxr // => i rgi.
  rewrite nth_cat size_nseq lez_maxr //; case: (i < k).
  - by move=> lt_ik; rewrite nth_nseq ~-1:/# allones_k //#.
  move=> /lerNgt le_ki; case: (i = k) => /= [->>//|].
  move=> ne_ik; rewrite subr_eq0 ne_ik /=.
  rewrite (BS2Int.int2bs_cat (k+1) N) ~-1:/#.
  rewrite nth_cat BS2Int.size_int2bs lez_maxr ~-1://#.
  by rewrite iffalse 1:/# opprD !addrA.
move=> ^eq {1}->; split.
- do 2! congr; rewrite !drop_mkseq 1:/# &(eq_in_mkseq) /(\o) /=.
  by move=> i rgi; rewrite -divz_mul 1:/# -exprD_nneg ~-1://#.
move=> _; move/(congr1 BS2Int.bs2int): eq; rewrite BS2Int.int2bsK ~-1://#.
rewrite -cat1s catA BS2Int.bs2int_cat -nseq1.
rewrite {1}(_ : 1 = (k + 1) - k) 1:#ring.
rewrite BS2Int.bs2int_cat_nseq_true_false ~-1:/#.
rewrite size_cat !size_nseq /= !lez_maxr ~-1:/#.
rewrite BS2Int.int2bsK 1:/#; first split=> [|_].
- by rewrite divz_ge0 // expr_gt0.
- rewrite ltz_divLR; first smt(expr_gt0).
  by rewrite -exprD_nneg //#.
move/(congr1 (fun i => i + 1))=> /= ->.
rewrite (BS2Int.int2bs_cat (k+1) N) ~-1:/#.
rewrite addrAC /= -BS2Int.int2bs_mod.
rewrite {1}[2^(k+1)*_]mulrC modzMDr.
rewrite pmod_small 1:exprSr ~-1://#.
rewrite BS2Int.int2bs_pow2 ?mem_range ~-1://# /=.
rewrite nseq0 -catA cat1s /=; do 2? congr.
rewrite [2^(k+1)*_]mulrC divzMDr ~-1:/#.
rewrite [2^_ %/ _]pdiv_small 1:exprSr ~-1://# /=.
apply/(eq_from_nth false).
- by rewrite size_drop ~-1://# !BS2Int.size_int2bs /#.
rewrite ?BS2Int.size_int2bs lez_maxr 1:/# => i rgi.
rewrite nth_drop ~-1:/# /int2bs !nth_mkseq ~-1://# /=.
rewrite -divzMr; ~-1:smt(expr_gt0).
by rewrite -exprD_nneg //#.
qed.

lemma hwincSE (N lidx : int) :
     0 <= N
  => 0 <= lidx
  => lidx + 1 < 2^N
  => let k = argmax (fun i => take i (BS2Int.int2bs N lidx)) (all idfun) in
     hw (BS2Int.int2bs N (lidx + 1)) = hw (BS2Int.int2bs N lidx) + 1 - k.
proof.
have ? := h_g0; move=> 3? k; have := int2bs_incSE N lidx _ _ _ => //.
have ge0_k: 0 <= k by apply: ge0_argmax.
rewrite -/k /= => -[# lekN hones hzero _ ->]; rewrite hw_cat /= hw_nseq //=.
rewrite -{2}[BS2Int.int2bs N _](cat_take_drop (k+1)).
rewrite hw_cat /= [hw (take _ _)](_ : _ = k) -1:#ring.
rewrite [take _ _](_ : _ = rcons (nseq k true) false); last first.
- by rewrite -cats1 hw_cat hw_nseq //=; smt(ge0_argmax).
rewrite (take_nth false) ?BS2Int.size_int2bs ~-1://#; congr.
have sztk: size (take k (BS2Int.int2bs N lidx)) = k.
- by rewrite size_take_condle // BS2Int.size_int2bs /#.
rewrite &(eq_from_nth false) ?size_nseq 1:/# sztk.
move=> i [ge0_i ltik]; rewrite nth_nseq //.
by rewrite nth_take // hones.
qed.

lemma hwincSE_lpath (lidx : int) : 0 <= lidx < 2^h =>
     (   lidx = 2^h - 1
      /\ lpath lidx = nseq h true
      /\ lpath (lidx + 1) = true :: nseq h false)
  \/ (   lidx < 2^h - 1
      /\ let k = argmax (fun i => take i (BS2Int.int2bs h lidx)) (all idfun) in
         hw (lpath (lidx + 1)) = hw (lpath lidx) + 1 - k).
proof.
case=> rg0_lidx /ltzE /lez_eqVlt [SlidxE | lt_Slidx]; [left | right].
- have ->/=: lidx = 2^h - 1 by apply/Ring.IntID.subr_eq.
  rewrite /lpath int2bs_pow2B1; ~-1:smt(h_g0).
  by rewrite b2i0_eq 1:/# /= nseq0 cats0 rev_nseq.
- split=> [/# | k @/lpath]; rewrite !hw_rev.
  rewrite [lidx + 1 = _]ltr_eqF // [lidx = _]ltr_eqF 1:/#.
  by have /= := hwincSE h lidx _ _ _; ~-1: smt(h_g0).
qed.

(* hw increases by exactly 1 *)
lemma hwinc lidx :
      0 <= lidx < 2^h
   => hw (lpath lidx) < hw (lpath (lidx+1))
   => hw (lpath (lidx+1)) = hw (lpath lidx) + 1.
proof.
have ? := h_g0; case/hwincSE_lpath.
- by move=> [# lidxE -> ->] /=; rewrite !hw_nseq //#.
- move=> [# lt -> /=]; smt(ge0_argmax).
qed.

(* we don't enter the loop if hw increased *)
lemma hwinc_noentry start lidxo t ss ps ad offset: 
   0 <= start <= 2^h - 2^t =>
   2^t %| start =>
   0 <= t <= h =>
   0 <= lidxo < 2^t =>
    hw (lpath (start + lidxo)) < hw (lpath (start + lidxo + 1)) =>
   let si = stack_increment start lidxo t ss ps ad offset in
    ((size si < 2) \/
     (2 <= size si /\
       (nth witness si (size si - 1)).`2 <>
         (nth witness si (size si - 2)).`2)).
admitted. (* 
proof.
move=> lt hinc si; have siE: si =
  stack_from_leaf lidx ss ps ad ++ [(node_from_path (lpath lidx) ss ps ad, 0)].
- by rewrite /si /stack_increment /=; rewrite hinc.
have ? := h_g0; move: lt hinc => ^[ge0_lidx _]; case/hwincSE_lpath.
- by move=> [# + -> ->] /= -; rewrite !hw_nseq /= /#.
(pose k':= argmax _ _) => [# /= *].
have := int2bs_incSE h lidx _ _ _; ~-1: by move=> //#.
rewrite -/k' /= => [#] _ _ /=.
have ->: k' = 0 by smt(ge0_argmax).
rewrite nseq0 /= nth0_head => hhd eqE.
case: (size si < 2) => /= [//|/lezNgt ^ge2_sz -> /=].
rewrite nth_last {1}siE last_cat /= eq_sym.
have ?: 0 < size (stack_from_leaf lidx ss ps ad).
- by move: ge2_sz; rewrite siE size_cat /= /#.
pose d := (nth witness si (size si - 2)).`2.
have: d \in map snd (stack_from_leaf lidx ss ps ad).
- apply/(@map_f snd); rewrite siE nth_cat size_cat /= iftrue 1:/#.
  apply/mem_nth; smt().
rewrite /stack_from_leaf -map_comp /(\o) /= => /mapP /=.
case=> p [+ ->] - @/paths_from_leaf; case: (lidx = _) => /= [->/=/#|].
case/pmapP=> i [/mem_range rgi] @/extract_path.
case: (nth false (lpath lidx) i) => // nthi /someI ->.
rewrite size_rcons size_take ~-1:/# size_lpath ~-1:/#.
rewrite [lidx = _]ltr_eqF 1:/# /= iftrue 1:/#.
suff: i <> h - 1 by smt().
apply: contraL nthi => ->; rewrite (_ : h = size (lpath lidx)).
- by rewrite size_lpath /#.
by rewrite nth_last /lpath last_rev b2i0_eq 1:/# /= hhd.
qed.
*)
(* hw increase implies odd, so last node in paths is the previous leaf *)
lemma hwinc_leaflast start lidxo t :
   0 <= start <= 2^h - 2^t =>
   2^t %| start =>
   0 <= t <= h =>
   0 <= lidxo < 2^t 
   => hw (lpath (start + lidxo)) < hw (lpath (start + lidxo + 1))
   =>    size (nth witness (paths_from_leaf start (lidxo + 1) t) (hw (drop (h-t) (lpath (start + lidxo))))) = t
      /\ lidxo = BS2Int.bs2int (rev ((take (h-t) (lpath (start + lidxo + 1))) ++ (nth witness  (paths_from_leaf start (lidxo + 1) t)) (hw (drop (h-t) (lpath (start + lidxo + 1))) - 1))).
admitted.
(* 
proof.
have ? := h_g0; move=> ^[ge0_lidx _]; case/hwincSE_lpath.
- by move=> [# + -> ->] /= - -> /=; rewrite !hw_nseq /= //#.
(pose k':= argmax _ _) => [# /= *].
have := int2bs_incSE h lidx _ _ _; ~-1: by move=> //#.
rewrite -/k' /= => [#] _ _ /=.
have ->: k' = 0 by smt(ge0_argmax).
move=> + _ +; rewrite nseq0 /= nth0_head => hhd eqE.
rewrite /paths_from_leaf !iffalse ~-1:/#.
pose p1 := lpath (lidx + 1); pose p2 := lpath lidx.
have: exists s, size s = h - 1 /\ ((p1 = rcons s true) /\ (p2 = rcons s false)). (* FACTOR OUT *)
- exists (rev (drop 1 (BS2Int.int2bs h lidx))); split.
  - by rewrite size_rev size_drop // BS2Int.size_int2bs /#.
  split.
  - by rewrite /p1 /lpath ltr_eqF 1:/# /= eqE rev_cons.
  - rewrite /p2 /lpath ltr_eqF 1:/# /= -rev_cons; congr.
    rewrite -{1}[BS2Int.int2bs _ _](cat_take_drop 1) -cat1s; congr.
    rewrite -[BS2Int.int2bs _ _]drop0 (drop_take1_nth false) /=.
    - by rewrite BS2Int.size_int2bs /#.
    - by rewrite nth0_head.
case=> s [szs [^p1E-> ^p2E->]]; rewrite !hw_rcons /=.
have ->: nth witness (pmap (extract_path (rcons s true)) (range 0 h)) (hw s) = rcons s false.
- rewrite (range_cat (h - 1)) ~-1:/# pmap_cat nth_cat.
  rewrite pfl_r_size_min ~-1:/# (_ : take (h - 1) (rcons s true) = s).
  - by rewrite -cats1 take_cat szs /= cats0.
  rewrite ltrr /= (rangeS (h - 1)) /= /extract_path.
  rewrite nth_rcons szs /= -[rcons s true]cats1 take_cat.
  by rewrite szs /= cats0.
rewrite size_rcons szs /= rev_rcons.
move/(congr1 rev)/(congr1 BS2Int.bs2int): p2E.
rewrite /p2 rev_rcons => <- @/lpath; rewrite revK.
by rewrite [lidx = 2^h]ltr_eqF 1:/# /= BS2Int.int2bsK //#.
qed.
*)

(* hw increase implies all previous paths same as before *)
lemma hwinc_pathsprev start lidxo k t : 
   0 <= start <= 2^h - 2^t =>
   2^t %| start =>
   0 <= t <= h =>
   0 <= lidxo < 2^t =>
    hw (lpath (start + lidxo)) < hw (lpath (start + lidxo + 1)) =>
     0 <= k < hw (lpath (start + lidxo)) =>
      (nth witness (paths_from_leaf start (lidxo + 1) t) k)
      = (nth witness (paths_from_leaf start lidxo t) k).
admitted.
(* 
proof.
have ? := h_g0; move=> ^[ge0_lidx _]; case/hwincSE_lpath.
- by move=> [# + -> ->] /= - ->; rewrite !hw_nseq //#.
(pose k':= argmax _ _) => [# /= *].
have := int2bs_incSE h lidx _ _ _; ~-1: by move=> //#.
rewrite -/k' /= => [#] _ _ /=.
have ->: k' = 0 by smt(ge0_argmax).
move=> + _ +; rewrite nseq0 /= nth0_head => hhd eqE.
rewrite /paths_from_leaf !iffalse ~-1://#.
pose p1 := lpath (lidx + 1); pose p2 := lpath lidx.
have: exists s, size s = h - 1 /\ ((p1 = rcons s true) /\ (p2 = rcons s false)).
- exists (rev (drop 1 (BS2Int.int2bs h lidx))); split.
  - by rewrite size_rev size_drop // BS2Int.size_int2bs /#.
  split.
  - by rewrite /p1 /lpath ltr_eqF 1:/# /= eqE rev_cons.
  - rewrite /p2 /lpath ltr_eqF 1:/# /= -rev_cons; congr.
    rewrite -{1}[BS2Int.int2bs _ _](cat_take_drop 1) -cat1s; congr.
    rewrite -[BS2Int.int2bs _ _]drop0 (drop_take1_nth false) /=.
    - by rewrite BS2Int.size_int2bs /#.
    - by rewrite nth0_head.
case=> s [szs [^p1E-> ^p2E->]].
pose s1 := pmap (extract_path _) _.
pose s2 := pmap (extract_path _) _.
suff: take (k+1) s1 = take (k+1) s2.
- move/(congr1 (fun s => nth witness s k)) => /=.
  by rewrite !nth_take ~-1://#.
have lek: k < hw s.
- have: k < hw (lpath lidx) by smt().
  by rewrite -/p2 p2E hw_rcons /=.
apply: pfl_eq; first 2 smt().
- move=> n ge0_n; rewrite -!cats1 !take_cat.
  by case: (n < size s) => /=; rewrite ?hw_cat; smt().
- by rewrite hw_rcons /= /#.
- by rewrite hw_rcons /= /#.
qed.
*)

(* hw decrease implies odd, so last node in old stack is leaf *)
lemma hwnoinc_leaflast start lidxo t :
   0 <= start <= 2^h - 2^t =>
   2^t %| start =>
   0 <= t <= h =>
   0 <= lidxo < 2^t =>
    hw (lpath (start + lidxo + 1)) <= hw (lpath (start + lidxo))  =>
     (0 < hw (lpath (start + lidxo)) /\ 
     size (nth witness (paths_from_leaf start lidxo t) ((size (paths_from_leaf start lidxo t)) - 1)) = h).
admitted.
(* 
proof.
have ? := h_g0; move=> ^[ge0_lidx _]; case/hwincSE_lpath.
- move=> [# + -> ->] /= - ->; rewrite !hw_nseq ~-1://# /=.
  move=> ge1_h; split; first smt().
  admit.
(pose k':= argmax _ _) => [# /= ? -> ?]; have ?: 0 < k' by smt().
have := int2bs_incSE h lidx _ _ _; ~-1: by move=> //#.
rewrite -/k' /= => [#] _ _ /= => hhd eqE1 eqE2; split.
- rewrite /lpath hw_rev b2i0_eq 1:/# /=.
  by rewrite eqE1 hw_cat /= hw_nseq ~-1:/# /=; smt(ge0_hw).
rewrite pfl_size 1:/# /paths_from_leaf iffalse 1:/#.
rewrite /lpath hw_rev b2i0_eq 1:/# /=.
rewrite -hw_rev; have <- := pfl_r_size (rev (BS2Int.int2bs h lidx)) h.
- by rewrite size_rev BS2Int.size_int2bs //#.
rewrite nth_last (range_cat (h - 1)) ~-1:/# pmap_cat rangeS /=.
pose q := extract_path _ (h - 1).
suff ->/=: q = Some (rcons (take (h - 1) (rev (BS2Int.int2bs h lidx))) false).
- rewrite last_cat /= size_rcons size_take_condle ~-1:/#.
  by rewrite size_rev BS2Int.size_int2bs /#.
rewrite /q /extract_path /= nth_rev ?BS2Int.size_int2bs 1:/# /=.
rewrite lez_maxr 1:/# /= iftrue // eqE1 nth_cat.
by rewrite size_nseq iftrue ~-1:/# nth_nseq /#.
qed.
*)

lemma take_nseq ['a] (i j : int) (x : 'a) : 0 <= i <= j =>
  take i (nseq j x) = nseq i x.
proof. by move=> rg; rewrite -!mkseq_nseq take_mkseq. qed.

(* if inner loop exited, then we have reached the final stack size *)
lemma hwdec_exit start lidxo ss ps ad offset t : 
   0 <= start <= 2^h - 2^t =>
   2^t %| start =>
   0 <= t <= h =>
   0 <= lidxo < 2^t 
   => hw (lpath (start + lidxo + 1)) <= hw (lpath (start + lidxo))
   => hw (lpath (start + lidxo + 1)) <= offset <= hw (lpath (start + lidxo)) + 1
   => let si = stack_increment start lidxo t ss ps ad offset  in
      (   size si < 2
       \/ (2 <= size si /\ (nth witness si (size si - 1)).`2 <> (nth witness si (size si - 2)).`2))
   => offset = hw (drop (h-t) (lpath (start + lidxo + 1))) /\ size si = hw (drop (h-t) (lpath (start + lidxo + 1))).
admitted.
(* 
proof.
have ? := h_g0; move=> ^[ge0_lidx _]; case/hwincSE_lpath.
- admit.
(pose k':= argmax _ _) => [# /=] ? + ^hdec - -> ?.
have ?: 0 < k' by smt().
have := int2bs_incSE h lidx _ _ _; ~-1: by move=> //#.
rewrite -/k' /= => [#] ?? /= => hhd eqE1 eqE2 hoff.
pose si := stack_increment _ _ _ _ _.
pose oldstack := stack_from_leaf lidx ss ps ad.
pose level :=
  if   offset = size oldstack + 1
  then 0
  else (nth witness oldstack (offset - 1)).`2 + 1.
pose carrypath := take (h - level) (lpath lidx).
have siE : si =
  take (offset - 1) oldstack ++ [(node_from_path carrypath ss ps ad, level)].
- by rewrite /si /stack_increment /= iffalse //#.
move=> hsz; rewrite -andaE; split; last first.
- rewrite siE => -> /=; rewrite size_cat /= size_take_condle.
  - rewrite /lpath hw_rev b2i0_eq 1:/# /=.
    by rewrite eqE1 hw_cat /= hw_nseq 1:/# /=; smt(ge0_hw).
  by rewrite sfl_size 1:/# iftrue /#.
have szod: size oldstack = hw (lpath lidx).
- by rewrite /oldstack sfl_size 1:/#.
have ltk': k' <= hw (lpath lidx).
- rewrite /lpath hw_rev b2i0_eq 1:/# /= eqE1.
  by rewrite hw_cat hw_nseq 1:/# /=; smt(ge0_hw).
have nthod: forall i, 0 <= i < k' => (nth witness (rev oldstack) i).`2 = i.
- move=> i rgi; rewrite nth_rev /oldstack sfl_size ~-1:/#.
  rewrite /stack_from_leaf (nth_map witness) 1:pfl_size ~-1:/# /=.
  rewrite /paths_from_leaf iffalse 1:/# (range_cat (h - (i+1))) ~-1:/#.
  have eqsz: hw (lpath lidx) - (i + 1) =
    size (pmap (extract_path (lpath lidx)) (range 0 (h - (i + 1)))).
  - rewrite &(eq_sym) /= pfl_r_size_min 1:/# {2}/lpath b2i0_eq 1:/# /=.
    rewrite -[BS2Int.int2bs _ _](cat_take_drop (i + 1)).
    rewrite rev_cat 2?(rev_take, rev_drop) ?BS2Int.size_int2bs ~-1:/#.
    rewrite lez_maxr 1:/# hw_cat /lpath b2i0_eq 1:/# /=.
    rewrite -addrA -{1}[hw _]addr0; congr; apply/eq_sym.
    rewrite {1}[h](_ : _ = size (BS2Int.int2bs h lidx)).
    - by rewrite BS2Int.size_int2bs /#.
    rewrite -rev_take ?BS2Int.size_int2bs 1:/# hw_rev eqE1.
    rewrite take_cat' take_nseq ~-1:/# hw_cat hw_nseq /= 1:/#.
    by rewrite size_nseq iftrue 1:/# /=.
  rewrite pmap_cat nth_cat iffalse; first by rewrite eqsz.
  rewrite eqsz /= range_ltn 1:/# /=.
  have ->/=: extract_path (lpath lidx) (h - (i + 1)) =
    Some (rcons (take (h - (i + 1)) (lpath lidx)) false).
  - rewrite /extract_path iftrue //= /lpath nth_rev.
    - by rewrite BS2Int.size_int2bs /= b2i0_eq /#.
    rewrite b2i0_eq 1:/# BS2Int.size_int2bs lez_maxr 1:/# /=.
    rewrite [h - _](_ : _ = i) 1:#ring eqE1 nth_cat.
    by rewrite size_nseq iftrue 1:/# nth_nseq //#.
  by rewrite size_rcons /= size_take 1:/# size_lpath /#.
case: hoff; rewrite ler_eqVlt; case=> // gtoff leoff; suff //: false.
have ge2_offset: 2 <= offset by smt().
have size_tk_od: size (take (offset - 1) oldstack) = offset - 1.
- by rewrite /oldstack size_take_condle -1:sfl_size -1:iftrue //#.
have ge2_szsi: 2 <= size si by rewrite siE size_cat /= size_tk_od.
move: hsz; rewrite ltrNge ge2_szsi /= nth_last {1}siE last_cat /=.
rewrite {1}siE cats1 nth_rcons iftrue; first by rewrite siE size_cat /#.
rewrite siE size_cat /= nth_take ~-1:/# size_tk_od /=.
have := nthod (size oldstack - (offset - 1)) _; first smt().
rewrite nth_rev /= 1:/# !(opprB, opprD, addrA) /= => ->.
rewrite /level; case: (offset = size oldstack + 1) => [->//|neoff].
have := nthod (size oldstack - offset) _; first smt().
by rewrite nth_rev /= 1:/# !opprD !addrA /= => ->; ring.
qed.
*)

(* final state of stack after reduction *)
lemma stack_final start lidxo ss ps ad t :
   0 <= start <= 2^h - 2^t =>
   2^t %| start =>
   0 <= t <= h =>
   0 <= lidxo < 2^t 
  => forall k, 0 <= k < hw (lpath (start + lidxo + 1)) =>
         nth witness (stack_increment start lidxo t ss ps ad (hw (lpath (start + lidxo + 1))))  k
       = nth witness (stack_from_leaf start (lidxo + 1) ss ps ad t) k.
proof.
admitted.
(* 
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
*)

lemma si_size_in_loop start lidxo ss ps ad offset t:
   0 <= start <= 2^h - 2^t =>
   2^t %| start =>
   0 <= t <= h =>
   0 <= lidxo < 2^t =>
hw (drop (h-t) (lpath (start + lidxo + 1))) <= hw (drop (h-t) (lpath (start + lidxo))) =>
hw (drop (h-t) (lpath (start + lidxo + 1))) <= offset <= hw (drop (h-t) (lpath (start + lidxo))) + 1 =>
2 <= offset =>
(nth witness (stack_increment start lidxo t ss ps ad offset) (offset - 1)).`2 = 
(nth witness (stack_increment start lidxo t ss ps ad offset) (offset - 2)).`2 =>
   size ((stack_increment start lidxo  t ss ps ad offset)) = offset /\
   size (stack_from_leaf start (lidxo+1) ss ps ad t) < offset.
admitted.
(* 
move => *;split.
+ move => *; rewrite /stack_increment /= ifF 1:/#.
  rewrite size_cat /= size_take 1:/#. 
  smt(sfl_size).
admit. (* not finished yet *)
qed. 
*)

(* entering the inner loop for a leaf tree means that
   we are still hashing values at height < h-1: when
   we exit the loop for leaf 2^h - 1 we have produced a 
   hash at level h *)
lemma si_heights_in_loop_bnd start lidxo ss ps ad offset k t :
   0 <= start <= 2^h - 2^t =>
   2^t %| start =>
   0 <= t <= h =>
   0 <= lidxo < 2^t =>
hw (drop (h-t) (lpath (start + lidxo + 1))) <= hw (drop (h-t) (lpath (start + lidxo))) =>
2 <= offset =>
(nth witness (stack_increment start lidxo t ss ps ad offset) (offset - 1)).`2 = 
(nth witness (stack_increment start lidxo t ss ps ad offset) (offset - 2)).`2 =>
0<= k < offset =>
 0<= (nth witness
   (stack_increment start lidxo t ss ps ad offset) k).`2 < t.
move => *.
admitted. 

(* In the inner loop, the final node in the stack
   is the hash of the last two nodes in the previous
   stack *)
lemma si_reduced_node start lidxo ss ps ad offset t :
   0 <= start <= 2^h - 2^t =>
   2^t %| start =>
   0 <= t <= h =>
   0 <= lidxo < 2^t =>
hw (drop (h-t) (lpath (start + lidxo + 1))) <= hw (drop (h-t) (lpath (start + lidxo))) =>
2 <= offset =>
(nth witness (stack_increment start lidxo t ss ps ad offset) (offset - 1)).`2 = 
(nth witness (stack_increment start lidxo t ss ps ad offset) (offset - 2)).`2 =>
let si = (stack_increment start lidxo t ss ps ad offset) in
let si1 = (stack_increment start lidxo t ss ps ad (offset - 1)) in
(nth witness si1 (offset - 2)).`1 =
trh ps (set_tree_index (set_tree_height (set_type zero_address 2) ((nth witness si (offset - 1)).`2))
     ((start + lidxo) %/ 2 ^ ((nth witness si (offset - 1)).`2 + 1))) 
  ( (DigestBlock.val (nth witness si (offset - 2)).`1) ++
    (DigestBlock.val (nth witness si (offset - 1)).`1)).
move => ? Hw ?? /=.
admitted.
(* growth of leaves under the leftmost subtree *)
lemma growth ss ps ad leaves start lidxo t :
   0 <= start <= 2^h - 2^t =>
   2^t %| start =>
   0 <= t <= h =>
   0 <= lidxo < 2^t =>
size leaves = start + lidxo =>
 take (size (first_subtree_leaves start (size leaves) ss ps ad t)) leaves =
   first_subtree_leaves start  (size leaves) ss ps ad t =>
 take (size (first_subtree_leaves start (lidxo + 1) ss ps ad t))
   (rcons leaves (leafnode_from_idx ss ps ad (start + lidxo))) =
 first_subtree_leaves start (lidxo + 1) ss ps ad t.
admitted.

phoare leaves_correct _ps _ss  _ad :
 [ FL_XMSS_TW_ES.leaves_from_sspsad : 
  arg = (_ss, _ps, _ad)  ==>
   res =
  map
    (leafnode_from_idx (NBytes.insubd (NBytes.val _ss)) (NBytes.insubd (NBytes.val _ps))
       (set_layer_addr zero_address 0)) (range 0 (2 ^ h))] = 1%r.
admitted.

phoare tree_hash_correct _ps _ss _lstart _sth _ad : 
[ XMSS_TreeHash.TreeHash.treehash : 
    arg = (_ps,_ss,_lstart,_sth,_ad) 
/\  _ad = zero_address /\ 0 <= _sth <= h /\ 0 <= _lstart < 2^h  /\ 2^_sth %| _lstart /\ 0 <= _lstart <= 2 ^ h - 2 ^ _sth
 ==> 
  DigestBlock.insubd (BytesToBits (NBytes.val res)) =  
    val_bt_trh (list2tree (map (leafnode_from_idx _ss _ps _ad) (range  _lstart (_lstart + 2^_sth)))) _ps (set_typeidx (XAddress.val witness) trhtype) _sth _lstart  ] = 1%r.
proof.
conseq (: _ ==> true) (: _ ==> _);1,2:smt(); last first. 
+ proc. 
  wp;while (true) (2^t - i).
  + move => *; wp; while (true) (to_uint offset).
    + move => *;inline *; auto => &hr;rewrite uleE /= => *. 
      rewrite W64.to_uintB => /=;1: by rewrite uleE /= /#.
      by smt().
    wp;call(:true).
    wp; while (true) (_len).
    + move => *.
      wp;while (true) (_len %/ 2 - i).
      move => *.
      inline *;auto => /> /#.
    by auto => /> /#.
   by auto => /> /#. 
  sp;wp;exlim sk_seed, pub_seed, address => ss ps ad. 
  call (Eqv_WOTS_pkgen ad ss ps).
  + auto => /> &hr ? h o; rewrite uleE /=;split; smt(W64.to_uint_cmp).
  by auto => /> /#.

proc.    
wp;while ( #{/~_ad = zero_address}pre
    /\ 0 <= i <= 2^t 
    /\ (forall k, 0<=k<3 => address.[k] = W32.zero)
    /\  size stack = h + 1 /\ size heights = h + 1
    /\ (let stacklist = stack_from_leaf _lstart i _ss _ps _ad _sth in
      to_uint offset = size stacklist /\
      forall k, 0 <= k < size stacklist =>
        bs2block (nth witness stack k) =
          (nth witness stacklist k).`1 /\
        to_uint (nth witness heights k) =
          (nth witness stacklist k).`2)); last first.
+ auto => /> &1 *; do split.
  + by smt(expr_ge0).
  + by smt(Array8.initiE Array8.get_setE).
  + by smt(size_nseq).
  + by smt(size_nseq).
  + by rewrite stack_from_leaf0 /#. 
  + by move=> 2?; rewrite stack_from_leaf0 /= /#.
  + move => hs1 i o1 st2 7? H.
    have @/bs2block -> := (H 0 _) => /=. rewrite sfl_size.  smt(). smt(). smt().  admit.  
    rewrite /stack_from_leaf nth0_head /paths_from_leaf /= ifT 1:/# /= cats0 /=.
    rewrite /node_from_path /=.
    case (_sth = h) => Ht.
    + rewrite Ht /= take0 /=  ifF;1:smt(h_g0).
      rewrite ifT 1:/# lfp_nil; congr; last first.
      - by rewrite -nth0_head nth_range //#.
      + congr; smt(). 
      admit. (* semantic match *)
   + rewrite ifF. admit. rewrite ifT. admit.
     congr; last first.
      - admit. 
      + admit. admit.  admit. 

seq 6 : (#pre /\
   bs2block node = leafnode_from_idx _ss _ps _ad (_lstart + i)).  
+ seq 3 : (#pre /\   pk = LenNBytes.insubd
  (map NBytes.insubd
     (chunk n
        (BitsToBytes
           (flatten (map DigestBlock.val (DBLL.val (wots_pk_val _ss _ps (set_kpidx (set_typeidx _ad 0) (_lstart + i)) (_lstart + i))))))))).
  + conseq />. smt(). 
    ecall {1} (pkWOTS_from_skWOTS_eq skWOTS0{1} ps1{1} (set_kpidx (set_typeidx ad0{1} 0) (size leafl0{1}))).
    ecall {1} (skWOTS_eq ss1{1} ps1{1} (set_kpidx (set_typeidx ad0{1} 0) (size leafl0{1}))).
    ecall {2} (Eqv_WOTS_pkgen address0{2} sk_seed1{2}  pub_seed1{2} ).
    auto => /> &1 &2 ???????????;split;1:smt(Array8.get_setE).
    congr;congr;congr;congr;congr;congr;congr;congr. 
    + congr. rewrite /set_ots_addr /set_kpidx /set_idx. admit. (* address semantics *)
    rewrite /set_ots_addr /set_kpidx /set_idx. admit. (* address semantics *)
  ecall {2} (Eqv_Ltree_ltree pk0{2} address0{2} pub_seed1{2}).
  auto => /> &1 &2 ???????????;split;1:smt(Array8.get_setE).
  rewrite /pkco /thfc ifF; 1: smt(@StdOrder.IntOrder gt0_n gt2_len).
  rewrite ifF /=. pose xx := 8*n. have ? : 0 < xx by smt(gt0_n). have ? := gt2_len. 
   have := Domain.mulfI xx _. smt(). rewrite /injective. smt().
 
  rewrite /leafnode_from_idx /= /bs2block;split;congr;congr;congr;congr. 
  +  rewrite /set_ots_addr /set_kpidx /set_idx. admit.  (* address semantics *)

wp. 
while {2} (
    (hw (lpath i{2}) < hw (lpath (i{2} + 1)) => to_uint offset{2} = hw (lpath (i{2} + 1))) 
 /\ (hw (lpath (i{2} + 1)) <= hw (lpath i{2}) => 
         hw (lpath (i{2} + 1)) <= to_uint offset{2} <= hw (lpath i{2}) + 1)
 /\ i{2} = size leafl0{1} /\ size stack{2} = h + 1 /\ size heights{2} = h + 1 
 /\ ps{1} = pub_seed1{2} /\ ad{1} = ad0{1} 
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
+ smt(hwinc sfl_size). 
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
       rewrite !nth_put;smt(size_ge0 size_rev count_size BS2Int.size_int2bs sfl_size).
      rewrite ifF;1: smt(sfl_size size_cat).
      rewrite ifT;1: smt(sfl_size size_cat).
      rewrite ifT;1: smt(sfl_size size_cat).
      have -> /= : k = to_uint offset{2}  by smt(sfl_size).
      rewrite !nth_put /=;1,2: by rewrite Ho sfl_size 1:/# /hw /lpath; smt(size_ge0 size_rev count_size BS2Int.size_int2bs).
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
    have /= := hwdec_exit _lidx ss{1} pub_seed1{2} ad0{1} (to_uint o2) _ _ _ _;1..3:smt().
    + have ->  :size (stack_increment _lidx ss{1} pub_seed1{2} ad0{1} (to_uint o2)) = to_uint o2 by smt().
      move : Hout'. 
      case (to_uint o2 < 2) => /=*;1: smt().
      split;1:smt().
      rewrite -!H5. smt(). smt().
   by smt(W32.to_uint_eq sfl_size W64.to_uint_cmp sfl_size hwinc).
   by smt(W32.to_uint_eq sfl_size W64.to_uint_cmp sfl_size hwinc).
   
  + case (_hw < _hw1) => ? k *.
    + case (k < _hw) => *. 
      + have ? := hwinc_pathsprev _lidx k _ _ _;1..3: smt().
        have ? := hwinc_leaflast _lidx _ _;1..2: smt(). 
        by rewrite -!stack_final;smt().
      by rewrite !H5;smt(W32.to_uint_eq sfl_size W64.to_uint_cmp stack_final).
  + have /= := hwdec_exit _lidx ss{1} pub_seed1{2} ad0{1} (to_uint o2) _ _ _ _;1..3:smt(). 
    + have ->  :size (stack_increment _lidx ss{1} pub_seed1{2} ad0{1} (to_uint o2)) = to_uint o2 by smt().
      move : Hout'.
      case (to_uint o2 < 2)  => /=*;1:smt().
      by rewrite -!H5; smt(W32.to_uint_eq sfl_size W64.to_uint_cmp stack_final).
     move => *.
     rewrite !H5;1,2: smt(W32.to_uint_eq sfl_size W64.to_uint_cmp stack_final).
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
        ((size leafl0{m}) %/ 2^(to_uint (nth witness heights (to_uint offset - 2)) + 1))).
+ auto => /> &hr ??????????Ho Hs; rewrite uleE /= => H.
  rewrite !to_uintB /=;1,2: by rewrite uleE /=; smt(). 
  move => H1;rewrite H1.
  move : (Hs (to_uint offset{hr} - 1) _);1: smt(sfl_size).
  move : (Hs (to_uint offset{hr} - 2) _);1: smt(sfl_size).
  move => [# Hs21 Hs22] [# Hs11 Hs12].

pose _lidx := size leafl0{m}.
have ? :  hw (lpath (_lidx + 1)) <= hw (lpath _lidx) by
 have /=:= hwinc_noentry _lidx ss{m} ps{m} ad0{m} (to_uint offset{hr}) _;smt(sfl_size). 


have -> : 
     (to_uint
         (W32.of_int (size leafl0{m}) `>>`
          truncateu8 ((nth witness heights{hr} (to_uint offset{hr} - 2) + W32.one) `&` W32.of_int 31))) = 
     (_lidx %/ 2^(to_uint (nth witness heights{hr} (to_uint offset{hr} - 2)) + 1)); last first.  
  + split;1: by move => *;rewrite /set_tree_index /set_tree_height /=; smt(Array8.get_setE).
    rewrite tP => k kb;rewrite /set_tree_index /set_tree_height /=.
    pose x:= 
       (stack_increment (size leafl0{m}) ss{m} ps{m} ad0{m} (hw (lpath (size leafl0{m})) + 1 - to_uint offset{hr})).
    pose y := W32.of_int ( _lidx %/ 2^(to_uint (nth witness heights{hr} (to_uint offset{hr} - 2)) + 1)).
     case (0<=k<5 \/ k= 7);1:by smt(Array8.get_setE).
     case (k=6);1:by smt(Array8.get_setE).
     move => *; have -> : k=5 by smt(). 
     rewrite !get_setE //= /#. 

  + rewrite /(`>>`) /= to_uint_truncateu8.
    have -> : 31 = 2^5 - 1 by rewrite /=.
    rewrite and_mod //= to_uintD_small /=   Hs22 /=.
    + by have := si_heights_in_loop_bnd _lidx ss{m} ps{m} ad0{m} (to_uint offset{hr})  (to_uint offset{hr} - 2) _ _ _;smt(h_max). 
    rewrite to_uint_shr /=;1: smt(W32.to_uint_cmp).
    rewrite of_uintK  modz_small => /=;1: smt(l_max).
    rewrite of_uintK  modz_small /= 1:/#. 
    rewrite modz_small 1:/#.
    rewrite modz_small.
    + by have := si_heights_in_loop_bnd _lidx ss{m} ps{m} ad0{m} (to_uint offset{hr})  (to_uint offset{hr} - 2) _ _ _;smt(h_max).
    rewrite /stack_increment /= ifF 1:/# nth_cat ifT;1: smt(size_take sfl_size).
    rewrite nth_take 1,2:/# /stack_from_leaf /= (nth_map witness) /=;1: smt(size_take pfl_size). 
    by smt().
 
seq 3 : (#pre /\ 
   node0 = nth XMSS_TreeHash.nbytes_witness stack (to_uint offset - 2)
/\  node1 = nth XMSS_TreeHash.nbytes_witness stack (to_uint offset - 1)   
/\   new_node = block2bs  (trh pub_seed1 address0 (BytesToBits (NBytes.val node0) ++ BytesToBits (NBytes.val node1)))).
+ inline *; auto => /> &hr ????????????; rewrite uleE /= => ?. 
   rewrite !to_uintB /=;1,2:by  rewrite ?uleE /=; smt().
   move => ?.
   rewrite /trh /thfc /= ifF. smt(@StdOrder gt0_n gt2_len).
   rewrite /block2bs DigestBlock.insubdK. 
   + rewrite /BytesToBits (size_flatten_ctt 8);1:smt(mapP W8.size_w2bits).
     rewrite size_map. smt(NBytes.valP).
   rewrite BytesToBitsK NBytes.valKd /rand_hash /=.
   congr;rewrite -!catA; congr;congr.
   + by rewrite /prf /=;congr;congr;rewrite -!catA; congr.
   congr.

     have Hs8 :  (size (BytesToBits (NBytes.val (nth XMSS_TreeHash.nbytes_witness stack{hr} (to_uint offset{hr} - 2)))) %/ 8) = size (chunk 8 (BytesToBits (NBytes.val (nth XMSS_TreeHash.nbytes_witness stack{hr} (to_uint offset{hr} - 2)))))     by rewrite size_chunk //.

  have Hsd : (size (BytesToBits (NBytes.val (nth XMSS_TreeHash.nbytes_witness stack{hr} (to_uint offset{hr} - 2)))) +
       size (BytesToBits (NBytes.val (nth XMSS_TreeHash.nbytes_witness stack{hr} (to_uint offset{hr} - 1))))) %/
      8 %/ 2 = size (BytesToBits (NBytes.val (nth XMSS_TreeHash.nbytes_witness stack{hr} (to_uint offset{hr} - 2)))) %/ 8.
        + have -> : size (BytesToBits (NBytes.val (nth XMSS_TreeHash.nbytes_witness stack{hr} (to_uint offset{hr} - 1)))) =
            size (BytesToBits (NBytes.val (nth XMSS_TreeHash.nbytes_witness stack{hr} (to_uint offset{hr} - 2)))); last by smt().
          rewrite /BytesToBits !(size_flatten_ctt 8);1,2: smt(mapP W8.size_w2bits). 
          by rewrite !size_map !NBytes.valP.

     have ? : size
  (map W8.bits2w
     (take
        (size
           (BytesToBits (NBytes.val (nth XMSS_TreeHash.nbytes_witness stack{hr} (to_uint offset{hr} - 2))) ++
            BytesToBits (NBytes.val (nth XMSS_TreeHash.nbytes_witness stack{hr} (to_uint offset{hr} - 1)))) %/
         8 %/ 2)
        (chunk 8
           (BytesToBits (NBytes.val (nth XMSS_TreeHash.nbytes_witness stack{hr} (to_uint offset{hr} - 2))) ++
            BytesToBits (NBytes.val (nth XMSS_TreeHash.nbytes_witness stack{hr} (to_uint offset{hr} - 1))))))) =
n.
     + rewrite size_map size_cat 1:Hsd chunk_cat;1: by rewrite /BytesToBits !(size_flatten_ctt 8); smt(mapP W8.size_w2bits). 
       rewrite Hs8  take_cat' /= take0 /= cats0 /= take_size size_chunk //. 
       rewrite /BytesToBits !(size_flatten_ctt 8);1: smt(mapP W8.size_w2bits). 
       by rewrite !size_map !NBytes.valP /= /#.

     have ? : size
  (map W8.bits2w
     (drop
        (size
           (BytesToBits (NBytes.val (nth XMSS_TreeHash.nbytes_witness stack{hr} (to_uint offset{hr} - 2))) ++
            BytesToBits (NBytes.val (nth XMSS_TreeHash.nbytes_witness stack{hr} (to_uint offset{hr} - 1)))) %/
         8 %/ 2)
        (chunk 8
           (BytesToBits (NBytes.val (nth XMSS_TreeHash.nbytes_witness stack{hr} (to_uint offset{hr} - 2))) ++
            BytesToBits (NBytes.val (nth XMSS_TreeHash.nbytes_witness stack{hr} (to_uint offset{hr} - 1))))))) =
n.
     + rewrite size_map size_cat 1:Hsd chunk_cat;1: by rewrite /BytesToBits !(size_flatten_ctt 8); smt(mapP W8.size_w2bits). 
       rewrite Hs8  drop_cat /= drop0 /= /BytesToBits flattenK //;1:smt(mapP W8.size_w2bits). 
       by rewrite !size_map !NBytes.valP /= /#.

   congr.
   + rewrite /BitsToBytes size_map size_chunk // -map_take.
     rewrite NBytes.insubdK 1:/# map_take size_cat Hsd.
     rewrite chunk_cat;1:by rewrite /BytesToBits !(size_flatten_ctt 8); smt(mapP W8.size_w2bits). 
     rewrite map_cat Hs8 -(size_map W8.bits2w) take_cat' /= take0 cats0 take_size.
     have ->: map W8.bits2w
  (chunk 8 (BytesToBits (NBytes.val (nth XMSS_TreeHash.nbytes_witness stack{hr} (to_uint offset{hr} - 2))))) =
     BitsToBytes (BytesToBits (NBytes.val (nth XMSS_TreeHash.nbytes_witness stack{hr} (to_uint offset{hr} - 2)))) by smt().
     by rewrite BytesToBitsK.

   + rewrite /BitsToBytes size_map size_chunk // -map_drop.
     rewrite NBytes.insubdK 1:/# map_drop size_cat Hsd.
     rewrite chunk_cat;1:by rewrite /BytesToBits !(size_flatten_ctt 8); smt(mapP W8.size_w2bits). 
     rewrite map_cat Hs8 -(size_map W8.bits2w) drop_cat /= drop0 /=. 
     have ->: map W8.bits2w
  (chunk 8 (BytesToBits (NBytes.val (nth XMSS_TreeHash.nbytes_witness stack{hr} (to_uint offset{hr} - 1))))) =
     BitsToBytes (BytesToBits (NBytes.val (nth XMSS_TreeHash.nbytes_witness stack{hr} (to_uint offset{hr} - 1)))) by smt().
     by rewrite BytesToBitsK.


   congr.
   + by rewrite /prf /=;congr;congr;rewrite -!catA; congr.
   by rewrite /prf /=;congr;congr;rewrite -!catA; congr.

+ auto => /> &hr ??????????Ho Hs; rewrite uleE /= => H.
  rewrite !to_uintB /=;1..2,4: by rewrite uleE /=; smt(). 
  + by rewrite uleE /= to_uintB /=; rewrite ?uleE /=; smt().
  
  move => H1;rewrite H1.
  move : (Hs (to_uint offset{hr} - 1) _);1: smt(sfl_size).
  move : (Hs (to_uint offset{hr} - 2) _);1: smt(sfl_size).
  move => [# Hs21 Hs22] [# Hs11 Hs12].

pose _lidx := size leafl0{m}.
have ? :  hw (lpath (_lidx + 1)) <= hw (lpath _lidx) by
 have /=:= hwinc_noentry _lidx ss{m} ps{m} ad0{m} (to_uint offset{hr}) _;smt(). 

split;last by smt().
have Hsil := si_size_in_loop (size leafl0{m}) ss{m} ps{m} ad0{m} (to_uint offset{hr}) _ _ _ _ _; 1..5: smt(). 
  do split.
  + smt(hwinc_noentry).
  + move => *;split;2:smt().
    rewrite Ho.
    rewrite Ho /stack_increment /= ifF 1:/# ifF 1:/# /= !size_cat /=.
    rewrite size_take;1:smt(size_ge0).
    by  smt(sfl_size size_take).
  + by smt(size_put).
  + by smt(size_put).
  + rewrite Ho /stack_increment /= ifF 1:/# /= !size_cat /=.
    rewrite size_take;1:smt(size_ge0).
    have -> /= : !(hw (lpath _lidx) < hw (lpath (_lidx + 1))) by smt().
    by case (to_uint offset{hr} - 1 < size (stack_from_leaf (size leafl0{m}) ss{m} ps{m} ad{m}));rewrite size_cat /=; by  smt(sfl_size size_take).

  + move => k kbl kbh. 
    rewrite !nth_put;1,2: smt(count_size BS2Int.size_int2bs size_rev).
    have kbh1 : k < to_uint offset{hr} -1.
    + move : kbh;rewrite /stack_increment /= ifF 1:/# size_cat /=.
      smt(size_take sfl_size).
    case (to_uint offset{hr} - 2 = k) => Hk; last first. 
    + rewrite !Hs;1,2:smt().
      rewrite /stack_increment /= ifF 1:/#.
      have -> /= : !(hw (lpath _lidx) < hw (lpath (_lidx + 1))) by smt().
      rewrite !nth_cat /= ifT;1:smt(size_take sfl_size size_ge0).
      have -> /=: !(k - size (take (to_uint offset{hr} - 2) (stack_from_leaf _lidx ss{m} ps{m} ad0{m})) = 0) by smt(sfl_size size_take).
      rewrite !ifT;1:smt(size_take sfl_size size_ge0).
      by rewrite !nth_take;smt(size_take sfl_size size_ge0). 
   split. 
  + rewrite /bs2block /block2bs NBytes.insubdK;1: 
      by rewrite /BitsToBytes size_map size_chunk 1:/# DigestBlock.valP /#.   
    rewrite BitsToBytesK;1: by rewrite DigestBlock.valP /=; smt().
    rewrite DigestBlock.valKd /=.
    have /= := si_reduced_node _lidx ss{m} ps{m} ad0{m} (to_uint offset{hr}) _ _ _ _;1..4:smt().
    rewrite Hk => ->; congr;1: smt(). 
    congr.
    + rewrite -Hk -Hs21 /bs2block DigestBlock.insubdK.
      + rewrite /BytesToBits (size_flatten_ctt 8);  smt(mapP W8.size_w2bits size_map NBytes.valP).
      congr; congr; rewrite (nth_change_dfl XMSS_TreeHash.nbytes_witness witness);  smt(count_size BS2Int.size_int2bs size_rev).
     rewrite  -Hs11 /bs2block DigestBlock.insubdK.
      + rewrite /BytesToBits (size_flatten_ctt 8);  smt(mapP W8.size_w2bits size_map NBytes.valP).
      congr; congr; rewrite (nth_change_dfl XMSS_TreeHash.nbytes_witness witness);  smt(count_size BS2Int.size_int2bs size_rev).
  rewrite to_uintD_small /=.
  + rewrite Hs22. 
    + have := si_heights_in_loop_bnd  (size leafl0{m})  ss{m} ps{m} ad0{m} (to_uint offset{hr}) (to_uint offset{hr} - 2) _ _ _ _ _;smt(h_max).
  rewrite Hs22.  
    rewrite /stack_increment /= ifF 1:/# nth_cat /=.
      have -> /= : !(hw (lpath _lidx) < hw (lpath (_lidx + 1))) by smt().
      rewrite !nth_cat /= ifT;1:smt(size_take sfl_size size_ge0).
    rewrite ifF;1:smt(size_take sfl_size size_ge0).
    rewrite ifT;1:smt(size_take sfl_size size_ge0).
    rewrite ifF;1:smt(size_take sfl_size size_ge0).
   rewrite /node_from_path /=.    
   smt(nth_take).
qed.

op skrel(ask : skXMSSTW, sk : xmss_sk) =
   ask.`1 = sk.`sk_prf /\
   ask.`2.`1 = Index.insubd (to_uint sk.`idx) /\
   ask.`2.`2 = sk.`sk_seed  /\
   ask.`2.`3 = sk.`pub_seed_sk
   (* ask.`2.`4 = ??? Why is the address in/not in the sk/pk? *)
   (* ??? = sk.`pk_root Why is the root not in/in the sk? *).

op pkrel(apk : pkXMSSTW, pk : xmss_pk) =
   apk.`1 = DigestBlock.insubd (BytesToBits (NBytes.val pk.`pk_root)) /\
   apk.`2 = pk.`pk_pub_seed
   (* apk.`3 = ??? Why is the address in the sk/pk? *)
   (* ??? = pk.`pk_oid I guess abstract proofs fon't care about oid *).

(* FD + WR *)
equiv kg_eq : XMSS_TW(FakeRO).keygen ~ XMSS_PRF.kg : ={arg} ==> pkrel res{1}.`1 res{2}.`2 /\ skrel res{1}.`2 res{2}.`1.
proof.
have ? := h_g0; have ? := expr_gt0.
proc. inline {1} 2. inline {1} 5. inline {2} 5.
swap {2} [5..7] -4. swap {2} 2 -1; seq 3 3 : (NBytes.val ss{1} = sk_seed0{2} /\ NBytes.val ms{1} = sk_prf0{2} /\ NBytes.val ps{1} = pub_seed0{2}).
+ do 3!(rnd NBytes.val NBytes.insubd); auto => />.
   have H := supp_dlist W8.dword n.
   have Hn:= Params.ge0_n.
   split => *;1: smt(NBytes.insubdK NBytes.valK Params.ge0_n supp_dlist).
   split => *;1: (rewrite dmapE; apply mu_eq_support => x Hx;smt(NBytes.valK)).
   split => *;1:smt(NBytes.valP supp_dmap).
   split => *;1: smt(NBytes.insubdK NBytes.valK Params.ge0_n supp_dlist).
   smt(NBytes.valP supp_dmap).

sp;wp => /=. conseq
    (: _ ==> (val_bt_trh (list2tree leafl{1}) ps{1} (set_typeidx (XAddress.val witness) trhtype) h 0 =
              DigestBlock.insubd (BytesToBits (NBytes.val root{2})))).
+ by auto => /> &1 *; smt(NBytes.valK). 

ecall {1} (leaves_correct  ps0{1} ss0{1} ad{1}).
ecall {2} (tree_hash_correct pub_seed{2} sk_seed{2} 0 h address{2}).
auto => /> &1; split;1: by rewrite /set_layer_addr /zero_address tP => *;  smt(Array8.get_setE Array8.initiE).
move => *;smt(NBytes.valK).
qed.

(* Signature type is abused with two index copies because I need this to simulate
   the actual operation of the implementation *)

op sigrel(asig : sigXMSSTW, sig : sig_t) =
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
proc. inline {1} 6. inline {1} 8. inline {1} 5.
swap {1} 21 -4. swap {1} [13..17] -1. swap {1} [11..16] -1. swap {1} [9..15] -6. inline {2} 7. inline {2} 16.
wp 20 25;sp; conseq />.

seq 1 0 : #pre. admit.  (* we need to meta-swap this *)

seq 2 1 : (#pre /\ ap{1} =
   DBHL.insubd
     (map (fun (b : Params.nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (AuthPath.val auth0{2}))); last first.  

+ seq 0 3 : (#pre /\ sigWOTS{1} =
   DBLL.insubd
     (map (fun (b : Params.nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (LenNBytes.val sig_ots{2}))). admit.  (* we need to meta-swap this *)
   auto => /> &1; rewrite /mkg => />  *;do split.
   + congr. congr.  congr. admit. smt().
   + rewrite NBytes.insubdK /toByte.
     + rewrite size_rev size_mkseq. smt(gt0_n). 
   + congr. admit. admit. admit. (* FIXME SOMETHING MISSING IN REL *)

inline {2} 1. wp; conseq />.
admitted.
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
