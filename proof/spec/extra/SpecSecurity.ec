require import AllCore List Distr DList.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

require (****) XMSS_TW.
require import XMSS_PRF.
import Params Types XMSS_Types Hash WOTS Address LTree BaseW.

op BitsToBytes (bits : bool list) : W8.t list = map W8.bits2w (chunk W8.size bits).
op BytesToBits (bytes : W8.t list) : bool list = flatten (map W8.w2bits bytes).
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
   type FLXMSSTW.SA.WTW.adrs <- adrs,
   op FLXMSSTW.n <- n,
   op FLXMSSTW.h <- h,
   op mkg = (fun (ms : nbytes) (i : FLXMSSTW.SA.index) =>
          let padding =  W64toBytes_ext prf_padding_val padding_len in
          let in_0 = toByte (W32.of_int (FLXMSSTW.SA.Index.val i)) 4 in
          (Hash (padding ++ NBytes.val ms ++ in_0),FLXMSSTW.SA.Index.val i)).


import FLXMSSTW SA WTW HtS Repro MCORO.

op bs2block(a : nbytes) = DigestBlock.insubd (BytesToBits (NBytes.val a)).

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
- We have a full binary tree with height h+1, so 2^h nodes.
  MM: Shouldn't it be:
    height h -> 2^h leaves, 2^h - 1 non-leaf nodes -> 2^(h + 1) - 1 nodes
- Levels are indexed from bottom to top, leaves at level 0, root at level h
- The length of a full path to a leaf is h
- The length of the path to a node at level l \in [0..h] is h - l (root path is [])
- The path to a leaf can be extracted from the bit representation of its index:
    the i-th leaf can be found at path rev (bits h i)
- throughout we will need the corner case of the leaf with index 2^h when
  we exit the loop, where everything works in a tree of height h+2
*)

(* The hamming weight of a path determines the size of the stack *)
op hw(p : bool list) = count (pred1 true) p.

(* The path of a leaf; we need the corner case of leaf 2^h for exiting the loop *)
op lpath(lidx : int) = rev (BS2Int.int2bs (if lidx = 2^h then (h+1) else h) lidx).

(* The paths of all the sibling nodes of 1-bit choices in a leaf path *)
op paths_from_leaf(lidx : int) : bool list list =
   if (lidx = 2^h) then [[]] (* we get the root *)
   else pmap (fun (bi : _*_) =>
     if bi.`1
     then Some ((take bi.`2 (lpath lidx)) ++ [false])
     else None) (zip (lpath lidx) (iota_ 0 h)).

lemma size_lpath (lidx) :
   lidx <= 2^h =>
     size (lpath lidx) = if lidx = 2^h then (h+1) else h.
move => H.
rewrite /lpathl size_rev BS2Int.size_int2bs; smt(h_g0).
qed.

lemma pfl_size (lidx : int) :
   lidx <= 2^h =>
   size (paths_from_leaf lidx) = hw (lpath lidx).
rewrite /paths_from_leaf => Hs.
case (lidx = 2 ^ h) => /= Hh.
+ rewrite /lpath /= Hh /= /hw BS2Int.int2bs_pow2;1:smt(mem_range h_g0).
  have -> : (h + 1 - 1 - h) = 0 by ring.
  rewrite nseq0 /= rev_cat rev1 count_cat /pred1 /= /b2i /=.
  rewrite (eq_in_count _ pred0);1: by move => x;rewrite rev_nseq mem_nseq /#.
  by rewrite count_pred0 /=.
rewrite /hw.
have -> : h = size (lpath lidx) by smt(size_lpath).
rewrite pmap_map size_map size_filter.
admit.
qed.

(* The list of leaves that are under a node given by a path *)
op leaves_from_path(p : bool list) =
   if size p = h+1 then witness (* we should never need this *)
   else
     let hsub = h - size p in
     let start = foldl (fun acc (bi : _ * _) => acc + if bi.`1 then 2^(h - bi.`2) else 0) 0 (zip p (iota_ 0 (size p))) in
         iota_ start (2^hsub).

lemma lfp_leaf lidx :
  lidx < 2^h =>
  (leaves_from_path (lpath lidx)) = [lidx].
move => Hh.
rewrite /leaves_from_path ifF /=. admit.
rewrite size_lpath 1:/# /= ifF 1:/# /= iota1;congr.
admit.
qed.

(* The leaf node corresponding to a leaf path
   The semantics of this needs to be computed from wots using
   operators and then proved equivalent to the imperative code. *)
op leafnode_from_idx(ss ps : Params.nbytes, ad : SA.adrs, lidx : int) : dgstblock.

(* list of all the leaves up to an index, exclusive *)
op leaf_range(ss ps : Params.nbytes, ad : SA.adrs, lidx : int) =
   map (leafnode_from_idx ss ps ad) (iota_ 0 lidx).

(* The node corresponding to an arbitrary path  *)
op node_from_path(p : bool list,ss ps : Params.nbytes, ad : SA.adrs) : dgstblock =
   if size p = h+1 then witness (* we should never need this *)
   else
      let ls = leaves_from_path p in
      let nls = map (leafnode_from_idx ss ps ad) ls in
      let subtree = list2tree nls in
         (val_bt_trh subtree ps (set_typeidx ad trhtype) (h - size p) (head witness ls)).

(* The full stack state when one starts to process leaf lidx *)
op stack_from_leaf(lidx : int,ss ps : Params.nbytes, ad : SA.adrs) : (dgstblock * int) list =
   map (fun p =>
     (node_from_path p ss ps ad, (h - size p))) (paths_from_leaf lidx).


lemma sfl_size lidx ss ps ad :
  lidx <= 2^h =>
  size (stack_from_leaf lidx ss ps ad) = hw (lpath lidx).
proof.
move => Hi.
rewrite  /stack_from_leaf size_map /paths_from_leaf.
case (lidx = 2 ^ h) => H /=.
+ rewrite /lpath /= H /= /hw BS2Int.int2bs_pow2;1:smt(mem_range h_g0).
  have -> : (h + 1 - 1 - h) = 0 by ring.
  rewrite nseq0 /= rev_cat rev1 count_cat /pred1 /= /b2i /=.
  rewrite (eq_in_count _ pred0);1: by move => x;rewrite rev_nseq mem_nseq /#.
  by rewrite count_pred0 /=.
rewrite pmap_map size_map size_filter /hw /predC1 /= count_map /preim /=.
admit.
qed.

(* The list of leaves that fall under the first node in the stack when one starts to process leaf lidx
   The case o lidx=0 is a corner case, as the stack is empty *)
op first_subtree_leaves(lidx : int,ss ps : Params.nbytes, ad : SA.adrs) =
   if lidx = 0 then [] else
   let lps = (paths_from_leaf lidx) in
   let p1 = head witness lps in
   let lp1 = leaves_from_path p1 in
     map (leafnode_from_idx ss ps ad) lp1.

(* The hamming weight of 0 is 0, so stack is empty *)
lemma pfl0 : paths_from_leaf 0 = [].
rewrite /paths_from_leaf ifF;1:smt(StdOrder.IntOrder.expr_gt0 h_g0).
rewrite (eq_in_pmap _ (fun _ => None)).
+ move => bi H; have := mem_zip  (lpath 0) (iota_ 0 h) bi.`1 bi.`2 _; 1:smt().
  rewrite /lpath mem_rev BS2Int.int2bs0 mem_nseq /#.
by apply pmap_none.
qed.

(* This op describes the state of the stack in the inner loop, while
   reducing, where i is the number of the iteration we are in.
   At iteration zero we just added the leaf we are processing (lidx) to
   the stack.
   The loop performs as many iterations as needed to reduce the
   hamming weight of lidx to hamming weight of lidx+1, if any. *)
op stack_increment(lidx : int,ss ps : Params.nbytes, ad : SA.adrs, i : int) =
  let hwi = hw (lpath lidx) in
  let hwi1 = hw (lpath (lidx + 1)) in
  if hwi < hwi1
  (* Then then case only happens when lidx is even, in which
     case we are already in the state we need on exit *)
  then stack_from_leaf (lidx+1) ss ps ad
  else
      (* reducing red positions requires red+1 hashes
         i must be in the range 0<=i<=red if loop is entered.
         when i = 0 the stack has size hwi + 1
         when i = red+1,i.e., we exit the loop, the stack has size hwi1
         at any i when we enter the loop we have still
         not touched positions 0..hwi1+red-1-i in the stack *)
      let red = hwi - hwi1 in
      (* we still did not touch positions [0 ... (hwi1 + red - 1 - i)] *)
      (* and the stack contains only one more element in position      *)
      (* (hwi1 + red - i) that corresponds to the node along the path to
         lidx that we can also compute *)
      let carrypath = (take (h - i) (lpath lidx))
      in (take (hwi1 + red - i) (stack_from_leaf lidx ss ps ad)) ++
                        [(node_from_path carrypath ss ps ad, h - size carrypath)].

(* FD + WR *)
equiv kg_eq : XMSS_TW(FakeRO).keygen ~ XMSS_PRF.kg : ={arg} ==> pkrel res{1}.`1 res{2}.`2 /\ skrel res{1}.`2 res{2}.`1.
proof.
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
+ by auto => /> &1 *;smt(NBytes.valK). print dgstblock.
while (size leafl0{1} = i{2} /\ 0 <= i{2} <= 2^h /\ t{2} = h
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
+ auto => /> &1;do split.
  + by apply StdOrder.IntOrder.expr_ge0 => //.
  + by rewrite /leaf_range iota0 /=.
  + by rewrite /stack_from_leaf pfl0 /= /#.
  + by move => h ?; rewrite /stack_from_leaf pfl0 /= /#.
  + move => leafs1 hs1 o1 st2 ????Hl??H.
    move : (H 0 _) => /=;1: by smt().
    rewrite /bs2block => ->.
    rewrite /stack_from_leaf nth0_head /paths_from_leaf /=.
    rewrite ifT 1:/# /=.
    rewrite /node_from_path /= /leaves_from_path !ifF /=;1,2:smt(h_g0).
    congr;last first.
    + rewrite iotaS_minus /=;1:smt(StdOrder.IntOrder.expr_gt0).
      by rewrite /hw /= /idfun /= iota0 //.
    + congr;rewrite Hl.
      rewrite /leaf_range;congr.
      rewrite /hw /= /idfun /= (iota0 0 0) //= /#.

seq 3 6 : (#pre /\
  leaf{1} = leafnode_from_idx ss{1} ps{1} ad{1} i{2} /\ leaf{1} = bs2block node{2}).
  admit. (* this can be fixed by setting leafnode_from_idx to the correct semantics *)

wp.
while {2} ((hw (lpath i{2}) < hw (lpath (i{2} + 1)) => to_uint offset{2} = hw (lpath (i{2} + 1))) /\
           (hw (lpath (i{2} + 1)) <= hw (lpath i{2}) => hw (lpath (i{2} + 1)) <= to_uint offset{2} <= hw (lpath i{2})) /\
    i{2} = size leafl0{1} /\
    0 <= i{2} < 2 ^ h /\
    t{2} = h /\
    leafl0{1} = leaf_range ss{1} ps{1} ad{1} i{2} /\
    (let firstleaves = first_subtree_leaves i{2} ss{1} ps{1} ad{1} in
         take (size firstleaves) leafl0{1} = firstleaves) /\
    let stacklist = stack_increment i{2} ss{1} ps{1} ad{1} (to_uint offset{2} - (hw (lpath i{2})) - 1) in
        to_uint offset{2} = size stacklist /\
      forall (k : int)
        0 <= k < size stacklist =>
          bs2block (nth witness stack{2} k) = (nth witness stacklist k).`1 /\
          to_uint (nth witness heights{2} k) = (nth witness stacklist k).`2 /\
  leaf{1} = leafnode_from_idx ss{1} ps{1} ad{1} i{2} /\ leaf{1} = bs2block node{2})
    (to_uint offset{2}); last first.
+ auto => /> &1 &2 ????Ho Hs??Hn; pose _lidx := size leafl0{1};do split.
+ admit. (* hw property *)
+ admit. (* hw property *)
+ rewrite !to_uintD_small /=. admit. (* we need an upper bound on h *)
  rewrite Ho /stack_increment /=.
  case (hw (lpath _lidx) < hw (lpath (_lidx + 1))).
  + admit. (* hw increases by exactly 1*)
  move => ?;rewrite -/_lidx.
  pose _olds := (stack_from_leaf _lidx ss{1} ps{1} ad{1}).
  pose _hw1 := (hw (lpath (_lidx + 1))).
  pose _hw := (hw (lpath (_lidx))).
  have Hsos : size _olds = _hw
   by rewrite /olds /stack_from_leaf size_map; smt(pfl_size h_g0).
  rewrite Hsos /=.
  have -> : (_hw1 + (_hw - _hw1) - (_hw + 1 - _hw - 1)) = _hw by ring.
  have -> /= : (h - (_hw + 1 - _hw - 1)) = h by ring.
  rewrite size_cat /= size_take /=;1:by smt(count_ge0).
  by smt().
+ move => k kbl.
  have -> : (offset{2} + W64.one - W64.one) = offset{2} by ring.
  rewrite /= !to_uintD_small;1: admit. (* we need an upper bound on h *)
  move => kbh; move :  (Hs k _). admit. (* lemma that stack decreases in reduction *)
  move => [H1 H2].
  have -> : (to_uint offset{2} + to_uint W64.one - hw (lpath _lidx) - 1)    = 0.
  + rewrite Ho /=.
    have -> : size (stack_from_leaf (size leafl0{1}) ss{1} ps{1} ad{1}) = hw (lpath _lidx);last by ring.
    by smt(sfl_size h_g0).
  rewrite /stack_increment /=.
  pose _olds := (stack_from_leaf _lidx ss{1} ps{1} ad{1}).
  pose _hw1 := (hw (lpath (_lidx + 1))).
  pose _hw := (hw (lpath (_lidx))).
  have Hsos : size _olds = _hw
      by rewrite /olds /stack_from_leaf size_map; smt(pfl_size h_g0).
  have -> : take (_hw1 + (_hw - _hw1)) _olds = _olds.
  + have -> : (_hw1 + (_hw - _hw1)) = size _olds by smt().
    by rewrite take_size.
  have -> : node_from_path (take h (lpath _lidx)) ss{1} ps{1} ad{1} = bs2block node{2}.
  + rewrite -Hn /node_from_path /= ifF ;1: smt(size_take h_g0).
    have -> : (take h (lpath _lidx) = (lpath _lidx));1: smt(take_size BS2Int.size_int2bs h_g0 size_rev).
    rewrite lfp_leaf /=;1:smt().
    rewrite -/_lidx size_lpath /=;1:smt().
    rewrite ifF 1:/# /list2tree /= ifT;1: by exists 0 =>/=.
    admit. (* we need to know that evaluation at level 0 is the leaf *)
  + (* this is the initialization of the inner loop *)
    case (_hw < _hw1) => /= *.
    + (* hw increased by 1, so we have to show that the previous stack plus
         the new leaf is really the stack that we will end up with *)
      admit.
    + (* reductions will be needed, but we haven't started
         so we have the old stack in the first positions and a
         new leaf at the next position *)
      rewrite !nth_cat.
      case (k < size _olds) => *;1: smt(sfl_size nth_put).
      rewrite !ifT. admit.
      rewrite !size_take /=; 1:smt(h_g0).
      rewrite !size_lpath /=;1:smt().
      rewrite !ifF /=;1..3:smt().
      have -> : k = to_uint offset{2}.
      + have ? : to_uint offset{2} = _hw by smt(sfl_size).
        move : kbh.
        have -> : (to_uint offset{2} + to_uint W64.one - hw (lpath _lidx) - 1) = to_uint offset{2} - _hw by rewrite /=;smt().
        rewrite /stack_increment /= ifF 1:/#.
        rewrite -/_hw -/_hw1 -/_lidx size_cat /=.
        have -> : (_hw1 + (_hw - _hw1) - (to_uint offset{2} - _hw))= _hw by smt().
        rewrite size_take;1: smt(count_ge0).
        smt(sfl_size).
      rewrite !nth_put /=. admit. admit.
      done.

move => hs o2 s2;do split => H H0 H1 H2 H3.
+ rewrite /(\ule) /= H1.  admit.  (* something about termination condition? *)
+ do split.
  + smt(size_rcons).
  + smt().
  + smt().
  + admit. (* to do *)
  + admit. (* to do  *)
  + admit. (* to do *)
  + admit. (* to do *)
  + admit. (* to do *)

move => *.
admit. (* preservation of inner loop invariant *)
qed.

(* Signature type is abused with two index copies because I need this to simulate
   the actual operation of the implementation *)

op sigrel(asig : sigXMSSTW, sig : sig_t) =
   (* asig.`1 = ??? /\ why is the public seed in the signature ? *)
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
admitted.

(* PY *)
equiv ver_eq : XMSS_TW(FakeRO).verify ~ XMSS_PRF.verify : pkrel pk{1} pk{2} /\ ={m} /\ sigrel sig{1} s{2} ==>
   ={res}.
proof.
proc.
inline {1} 4. inline {1} 7. inline {1} 13.
inline {2} 10.
admitted.
