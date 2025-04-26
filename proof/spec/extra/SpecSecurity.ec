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

(* Get checksum from XMXX_Checksum and then plug those results
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

(* The hamming weight of a path determines the size of the stack *)
op hw(p : bool list) = size (filter idfun p).

(* The path of a leaf; we need the corner case of leaf 2^h for exiting the loop *)
op lpath(lidx : int) = rev (BS2Int.int2bs (if lidx = 2^h then (h+1) else h) lidx).

(* The paths of all the nodes corresponding to one bits in a leaf path *)
op paths_from_leaf(lidx : int) : bool list list = 
   foldl (fun (paths : bool list list) (bi : _*_) => 
     if bi.`1 
     then paths ++ [(take bi.`2 (lpath lidx)) ++ [false]] 
     else paths) [] (zip (lpath lidx) (iota_ 0 h)).

(* The list of leaves that are under a node given by a path *)
op leaves_from_path(p : bool list) =
   let hsub = h - size p in
   let start = foldl (fun i acc => acc + 2^i) 0 (iota_ 0 (hw p)) in 
   iota_ start (2^hsub).

(* The leaf node corresponding to a leaf path *)
op leafnode_from_idx(ss ps : Params.nbytes, ad : SA.adrs, lidx : int) : dgstblock.

(* all the leaves up to an index *)
op leaf_range(ss ps : Params.nbytes, ad : SA.adrs, lidx : int) =
   map (leafnode_from_idx ss ps ad) (iota_ 0 (lidx+1)).

(* The node corresponding to a path *)
op node_from_path(p : bool list,ss ps : Params.nbytes, ad : SA.adrs) : dgstblock =
   let ls = leaves_from_path p in
     let nls = map (leafnode_from_idx ss ps ad) ls in
     let subtree = list2tree nls in
        (val_bt_trh subtree ps (set_typeidx ad trhtype) (h - size p) (head witness ls)).

(* The full stack state when one starts to process leaf lidx *)
op stack_from_leaf(lidx : int,ss ps : Params.nbytes, ad : SA.adrs) : (dgstblock * int) list = 
   map (fun p =>
     (node_from_path p ss ps ad, (h - size p))) (paths_from_leaf lidx).

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
rewrite /paths_from_leaf.
rewrite (foldl_in_eq (fun (paths : bool list list) (bi : bool * int) =>
     if bi.`1 then paths ++ [take bi.`2 (lpath 0) ++ [false]] else paths) (fun (paths : bool list list) (bi : bool * int) => paths)).
+ move => path;rewrite /lpath =>  bi H /=.
  have := mem_zip  (lpath 0) (iota_ 0 h) bi.`1 bi.`2 _;1:smt().
  rewrite /lpath mem_rev BS2Int.int2bs0 mem_nseq /#.
  by elim (zip (lpath 0) (iota_ 0 h)) => //=.
qed.

(* This op describes the state of the stack in the inner loop, while
   reducing, where i is the number of the iteration we are in.
   The loop performs as many iterations as needed to reduce the 
   hamming weight of lidx to hamming weight of lidx+1, which may
   be no iterations at all if the hamming weight increases *)
search belast.
op stack_increment(lidx : int,ss ps : Params.nbytes, ad : SA.adrs, i : int) =
  let hwi = hw (lpath lidx) in
  let hwi1 = hw (lpath (lidx + 1)) in
  if hwi < hwi1 then stack_from_leaf (lidx+1) ss ps ad
  else 
      let red = hwi - hwi1 in
      let lps = (paths_from_leaf lidx) in
      let lps1 = (paths_from_leaf (lidx+1)) in
      (* we still did not touch positions [0 ... (hwi1 - 1 + red - i)] *)
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
while (size leafl0{1} = i{2} /\ 0 <= i{2} <= 2^h 
    /\ leafl0{1} = leaf_range  ss{1} ps{1} ad{1} (i{2}-1) 
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
  + move => leafs1 hs1 o1 st2 ???????H.
   have Hlp : (lpath (size leafs1)) = true :: nseq h false.
   + rewrite /lpath.
     have -> /= : (size leafs1) = 2^h by smt().
     rewrite BS2Int.int2bs_pow2 /=;1:smt(mem_range h_g0).
     by rewrite nseq0 /= rev_cat rev_nseq rev1 cat_cons /=.
    move : (H 0 _) => /=. 
    + rewrite /= /stack_from_leaf size_map /paths_from_leaf /=. 
      rewrite Hlp.
      rewrite iotaS_minus /=;1:smt(h_g0). admit.
  rewrite /bs2block => ->.
  rewrite /stack_from_leaf nth0_head /paths_from_leaf /=.
  rewrite Hlp /=.
  admit. 

admitted.

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
