require import AllCore IntDiv List Distr DList StdOrder RealExp.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.
require import Array8.

require (****) XMSS_TW Checksum.
require import XMSS_RFC_Abs.
import XMSS_RFC_Params WOTS_RFC_Abs Address BaseW.
(*
require (****) XMSS_TW.
require import XMSS_PRF.
import Params Types XMSS_Types Hash WOTS Address LTree BaseW.
*)
import IntOrder.

(* Overflows may happen unless h is upper bounded *)
axiom h_max : h < 32.

(* We are using multiples of n and len to distinguish which hash to use
axiom gt0_n : 0 < n.
*)

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
have [H _]:= (eq_in_map (fun (x0 : W8.t) => W8.bits2w (W8.w2bits x0)) idfun x).
rewrite H;1: by move => x0 memX0 /=.
by smt(map_id).
qed.

op W64toBytes_ext (x : W64.t) (l : int) : W8.t list =
  rev (mkseq (fun i => nth W8.zero (to_list (W8u8.unpack8 x)) i) l).

(*
  Conversion operators
  --------------------
  Security spec indices (corresponding to an address):
    [hash    | padding(= 0) | tree breadth;
     chain   | padding(= 0) | tree height;
     keypair | keypair      | padding(= 0);
     chtype  | pkcotype     | trhtype]
  RFC address:
    [layer(= 0);
     hypertree1(= 0);
     hypertree2(= 0);
     chtype(= 0) | ltrtype(= 1)  | trhtype(= 2);
     keypair     | keypair       | padding(= 0);
     chain       | tree height   | tree height;
     hash        | tree breadth  | tree breadth;
     keyAndMask]

  If we have set the abstraction (of the hash functions) up properly, we only need
  to consider parts of the addresses that (conceptually) overlap between the two.
  Particularly:
  - The layer, hypertree1, hypertree2 are always 0 on the RFC side, as we are dealing with single-tree XMSS,
    making them irrelevant.
  - The tree height and tree breadth indices used for ltree/public key compression on the RFC side
    are abstracted away under the relevant hash function (security: pkco, RFC: ltree).
    Specifically, these indices are also always 0 as far as we can tell here (and their usage/manipulation
    is done "inside the hash functions").
  - The keyAndMask index on the RFC side is also abstracted away under the relevant hash functions.
    (Indeed,  this index is also always 0 as far as we can tell here, and its usage/manipulation
    is done "inside the hash functions").
*)
(* Indices of security spec -> address in implementation/RFC *)
op idxs2adr (il : int list) : adrs =
  init (fun (i : int) =>
        if 3 <= i <= 6
        then W32.of_int (nth witness il (6 - i))
        else W32.zero).

(* Address in implementation/RFC -> Indices of security spec *)
op adr2idxs (ad : Address.adrs) : int list =
  rev (map W32.to_uint (sub ad 3 4)).

lemma idxs2adrK (il : int list) :
  size il = 4 =>
  all (mem (range 0 W32.modulus)) il =>
  adr2idxs (idxs2adr il) = il.
proof.
move=> eq4szil mem_il.
have eq4szm : size (adr2idxs (idxs2adr il)) = 4.
+ by rewrite size_rev size_map size_mkseq.
rewrite &(eq_from_nth witness) eq4szm 1:eq4szil // => i rngi.
rewrite /adr2idxs nth_rev size_map size_sub 1..3://.
rewrite (nth_map witness witness) 1:size_sub 1:// 1:/#.
rewrite nth_mkseq 1:/# /= /idxs2adr initiE 1:/# /= (: 3 <= 7 - (i + 1) <= 6) 1:/# /=.
rewrite of_uintK pmod_small 2:/#.
by move/(all_nthP _ _ witness): mem_il => /(_ i _); smt(mem_range).
qed.

lemma adr2idxsK (ad : Address.adrs) :
  (forall i, 0 <= i < 3 \/ i = 7 => ad.[i] = W32.zero) =>
  idxs2adr (adr2idxs ad) = ad.
proof.
move=> zr.
rewrite /adr2idxs /idxs2adr tP => i rngi.
rewrite initE rngi /=; case (0 <= i < 3 \/ i = 7) => outi.
+ by move: (zr i outi) => -> /#.
rewrite ifT 1:/# nth_rev 2:(nth_map witness); 1,2:smt(size_map size_sub).
by rewrite to_uintK nth_sub; smt(size_sub size_map).
qed.


(*
lemma adr2idxsK (ad : Address.adrs) :

  idxs2adr (adr2idxs ad) = ad.
proof.
*)
(* Get checksum from XMSS_Checksum and then plug those results
   here
- Make space in detailed chapters for discussion in introduction
  > what do difficulties reveal about actual crypto
  > clear explanation of things that want to make a point about that are relevant
    to crypto:
      Delaying of delaying key gen, requireing that it is stateless
      SSP: explain enough of

-


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
*)

(* -- Checksum instantiation -- *)
clone import Checksum as CS with
  op w <- 2 ^ (ilog 2 w)

proof *.
realize gt0_w by rewrite expr_gt0.

clone import XMSS_TW as XMSS_Security with
  type mseed <- nbytes,
  type mkey <- nbytes,
  type msgXMSSTW <- W8.t list,
  op mkg <-
    (fun (ms : nbytes) (i : FLXMSSTW.SA.index) =>
     prf ms (NBytes.insubd (toByte (W32.of_int (FLXMSSTW.SA.Index.val i)) n))),
  op dmseed <- dmap (dlist W8.dword Params.n) NBytes.insubd,
  op MKey.enum <= map NBytes.insubd (mkseq (fun (i : int) =>
                                            BitsToBytes (BS2Int.int2bs (8 * n) i)) (2 ^ (8 * n))),
  op dmkey <- duniform MKey.enum,
  op FLXMSSTW.n <- n,
  op FLXMSSTW.log2_w <- ilog 2 w,
  op FLXMSSTW.h <- h,
  op FLXMSSTW.chtype <= 0,
  op FLXMSSTW.pkcotype <= 1,
  op FLXMSSTW.trhtype <= 2,
  op FLXMSSTW.SA.adc <= FLXMSSTW.SA.XAddress.insubd (FLXMSSTW.SA.HAX.Adrs.insubd
                                                     (adr2idxs (zero_address))),
  op FLXMSSTW.SA.dmsgFLXMSSTW <- duniform FLXMSSTW.SA.WTW.DigestBlockFT.enum,
  type FLXMSSTW.SA.WTW.pseed <- nbytes,
  type FLXMSSTW.SA.WTW.sseed <- nbytes,
  op FLXMSSTW.SA.WTW.dsseed <- dmap (dlist W8.dword Params.n) NBytes.insubd,
  op FLXMSSTW.SA.WTW.dpseed <- dmap (dlist W8.dword Params.n) NBytes.insubd,
  op FLXMSSTW.SA.WTW.ddgstblock <- duniform FLXMSSTW.SA.WTW.DigestBlockFT.enum,
  theory FLXMSSTW.SA.WTW.BaseW <- CS.BaseW,
  op FLXMSSTW.SA.WTW.encode_msgWOTS <= (fun (m : msgWOTS) =>
                                        EmsgWOTS.mkemsgWOTS (encode_int len1
                                                             (BS2Int.bs2int (rev (DigestBlock.val m))) len2)),
  op FLXMSSTW.SA.WTW.ch <= (fun (g : nbytes -> FLXMSSTW.SA.adrs -> bool list -> dgstblock) (ps : nbytes)
                                (ad : FLXMSSTW.SA.adrs) (s i : int) (x : bool list) =>
                            (DigestBlock.insubd
                             (iteri i
                              (fun chain_count x => (DigestBlock.val (g ps (set_hidx ad (s + chain_count)) x)))
                              x))),
  op FLXMSSTW.SA.WTW.prf_sk <=
    (fun (ss : nbytes) (psad : nbytes * FLXMSSTW.SA.adrs) =>
     DigestBlock.insubd (BytesToBits
                         (NBytes.val
                          (prf_keygen ss (psad.`1, (idxs2adr (FLXMSSTW.SA.HAX.Adrs.val psad.`2))))))),
  op FLXMSSTW.SA.WTW.thfc <=
    (fun (i : int) (ps : nbytes) (ad : FLXMSSTW.SA.adrs) (x : bool list) =>
     let nb2db = (fun (x : nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val x))) in
     let mad = (idxs2adr (FLXMSSTW.SA.HAX.Adrs.val ad)) in
     if i = 8 * n then
      nb2db (f ps mad (NBytes.insubd (BitsToBytes x)))
     else if i = 8 * n * 2 then
      let mad = set_tree_height mad ((get_tree_height mad) - 1) in (* Compensate for off-by-one in security spec... *)
      let xl = take (8 * n) x in
      let xr = drop (8 * n) x in
      nb2db (rand_hash ps mad (NBytes.insubd (BitsToBytes xl)) (NBytes.insubd (BitsToBytes xr)))
     else if i = 8 * n * len then
      let wpk = LenNBytes.insubd (map NBytes.insubd (chunk n (BitsToBytes x))) in
      nb2db (ltree ps mad wpk)
     else witness)
proof *.
realize FLXMSSTW.ge1_n by exact: ge1_n.
realize FLXMSSTW.val_log2w by case: w_vals => ->; smt(ilog_powK).
realize FLXMSSTW.ge1_h by smt(h_g0).
realize FLXMSSTW.dist_adrstypes by trivial.
realize FLXMSSTW.SA.WTW.ch0.
move=> g ps ad s i x valad sz8n le0_i.
by congr; rewrite iteri0.
qed.
realize FLXMSSTW.SA.WTW.chS.
move=> g ps ad s i x valad sz8n ge0_s gt0_i lew1_si.
rewrite (iteriS (i - 1)) 1:/# DigestBlock.valKd DigestBlock.insubdK 2:/#.
elim/natind: i gt0_i lew1_si; 1: smt().
move=> j ge0_j ih gt0_j1 ltw1.
case (j = 0) => [-> /= | neq0_j]; 1: by rewrite iteri0.
rewrite (: j + 1 - 1 = j - 1 + 1) 1://.
by rewrite iteriS 1:/# /= DigestBlock.valP.
qed.
realize FLXMSSTW.SA.WTW.two_encodings.
move=> m m' neqm_mp.
have eq28n_wl1 : 2 ^ (8 * n) = w ^ len1.
+ rewrite /w -exprM; congr.
  rewrite /len1 log2_wP -fromint_div 2:from_int_ceil; first by smt(val_log2w).
  by rewrite -divMr 2:mulKz 3://; first 2 smt(val_log2w).
move: (checksum_prop_var len1 len2 (BS2Int.bs2int (rev (DigestBlock.val m'))) (BS2Int.bs2int (rev (DigestBlock.val m)))).
move=> /(_ _ _ _); first 2 by smt(ge1_len1 ge1_len2).
+ rewrite -lt_fromint -RField.fromintXn 1:#smt:(ge1_len2) -rpow_int 1:#smt:(val_w).
  have <- := rpowK w%r ((w - 1) * len1)%r _ _ _; first 3 by smt(val_w ge1_len1).
  apply: rexpr_hmono_ltr; first by smt(val_w).
  split=> [|_]; first by rewrite log_ge0 #smt:(val_w ge1_len1).
  rewrite /len2; pose l1w1 := len1 * (w - 1).
  have ->: log2 l1w1%r / log2 w%r = log w%r l1w1%r; last by smt(floor_bound).
  by rewrite /log2 /log; field; first 2 by smt(ln_eq0 val_w).
move=> /(_ _ _); first 2 by smt(BS2Int.bs2int_ge0 DigestBlock.valP size_rev BS2Int.bs2int_le2Xs).
move=> /contra; rewrite negb_forall=> //= /(_ _).
+ rewrite -negP=> /(congr1 (BS2Int.int2bs (8 * n))).
  rewrite -{1}(DigestBlock.valP m') -(size_rev (DigestBlock.val m')) -{1}(DigestBlock.valP m) -(size_rev (DigestBlock.val m)).
  rewrite !BS2Int.bs2intK => /(congr1 rev); rewrite !revK => /(congr1 DigestBlock.insubd).
  by rewrite !DigestBlock.valKd => ->>.
move=> [] i; rewrite negb_imply (lezNgt (BaseW.val _)) /= => -[Hi Hlt].
exists i; split; first by exact: Hi.
rewrite /encode_msgWOTS !EmsgWOTS.getE Hi /= !EmsgWOTS.ofemsgWOTSK //.
+ by rewrite /encode_int size_cat 1:size_int2lbw 3:size_checksum; smt(ge1_len1 ge1_len2 BS2Int.bs2int_ge0).
by rewrite /encode_int size_cat 1:size_int2lbw 3:size_checksum; smt(ge1_len1 ge1_len2 BS2Int.bs2int_ge0).
qed.
realize FLXMSSTW.SA.dmsgFLXMSSTW_ll.
rewrite duniform_ll -size_eq0 2!size_map size_range.
suff /#: 0 < 2 ^ (8 * n).
by rewrite expr_gt0.
qed.
realize FLXMSSTW.SA.dmsgFLXMSSTW_uni by exact: duniform_uni.
realize FLXMSSTW.SA.dmsgFLXMSSTW_fu by apply /duniform_fu /WTW.DigestBlockFT.enumP.
realize FLXMSSTW.SA.WTW.dsseed_ll by apply /dmap_ll /dlist_ll /W8.dword_ll.
realize FLXMSSTW.SA.WTW.dpseed_ll by apply /dmap_ll /dlist_ll /W8.dword_ll.
realize FLXMSSTW.SA.WTW.ddgstblock_ll.
rewrite duniform_ll -size_eq0 2!size_map size_range.
suff /#: 0 < 2 ^ (8 * n).
by rewrite expr_gt0.
qed.
realize MKey.enum_spec.
move => x; rewrite count_uniq_mem.
+ rewrite ?map_inj_in_uniq /= 3:iota_uniq.
  + move=> xl yl /mapP [x' /= [xpin ->]] /mapP [y' /= [ypin ->]] eqins.
    rewrite -NBytes.insubdK 2:eq_sym 2:-NBytes.insubdK 3:eqins //.
    + rewrite /BitsToBytes size_map size_chunk 1:// BS2Int.size_int2bs.
      by rewrite lez_maxr 2:mulKz 2://; 1:smt(ge1_n).
    rewrite /BitsToBytes size_map size_chunk 1:// BS2Int.size_int2bs.
    by rewrite lez_maxr 2:mulKz 2://; 1:smt(ge1_n).
  move=> x' y' /mem_iota /= rng_x /mem_iota /= rng_y eqb2b.
  suff eqbs: (BS2Int.int2bs (8 * n) x') = (BS2Int.int2bs (8 * n) y').
  +  by rewrite -(BS2Int.int2bsK (8 * n)) 3:eq_sym 3:-(BS2Int.int2bsK (8 * n)); smt(ge1_n).
  rewrite -BitsToBytesK; 1: by rewrite BS2Int.size_int2bs lez_maxr 2:dvdz_mulr; 1: smt(ge1_n).
  by rewrite eq_sym -BitsToBytesK; 1: rewrite BS2Int.size_int2bs lez_maxr 2:dvdz_mulr; smt(ge1_n).
rewrite /b2i mapP ifT 2://; 1: exists (NBytes.val x).
rewrite NBytes.valKd /= mapP; exists (BS2Int.bs2int (BytesToBits (NBytes.val x))).
rewrite /= (: 8 * n = size (BytesToBits (NBytes.val x))).
+ rewrite /BytesToBits (size_flatten_ctt 8).
  + by move=> bs /mapP [x' ->]; rewrite size_w2bits.
  by congr; rewrite size_map NBytes.valP.
by rewrite BS2Int.bs2intK BytesToBitsK mem_iota BS2Int.bs2int_ge0 BS2Int.bs2int_le2Xs.
qed.
realize MsgXMSSTW.enum_spec.
admitted. (*
            TODO:
            this shouldn't be necessary, but current HtS requires it.
            Need to introduce finite type for arbitrary-length messages
            in RFC spec.
          *)
realize dmseed_ll by apply /dmap_ll /dlist_ll /W8.dword_ll.
realize dmkey_ll.
rewrite duniform_ll -size_eq0 2!size_map size_iota.
suff /#: 0 < 2 ^ (8 * n).
by rewrite expr_gt0.
qed.
realize dmkey_uni by exact: duniform_uni.
realize dmkey_fu by apply /duniform_fu /MKey.enumP.

import RFC HtSRFC Repro MCORO.
import FLXMSSTW SA WTW.

lemma gt2_len : 2 < XMSS_Security.FLXMSSTW.len.
proof.
rewrite /len /len1 /len2 /= /len1 /len2 /w /w.
admitted.


lemma l_max : l <= 2147483648.
have -> : 2147483648 = 2^31 by simplify => //=.
rewrite /l;apply ler_weexpn2l; 1,2:smt(h_max h_g0).
qed.


op bs2block(a : nbytes) = DigestBlock.insubd (BytesToBits (NBytes.val a)).
op block2bs(a : dgstblock): nbytes = NBytes.insubd (BitsToBytes (DigestBlock.val a)).
op ads2adr (ad : SA.adrs) : Address.adrs = idxs2adr (HAX.Adrs.val ad).
op adr2ads (ad : Address.adrs) : SA.adrs = HAX.Adrs.insubd (adr2idxs ad).

lemma ads2adrK (ad : SA.adrs) :
  all (mem (range 0 W32.modulus)) (HAX.Adrs.val ad) =>
  adr2ads (ads2adr ad) = ad.
proof. move=> *; smt(HAX.Adrs.valP HAX.Adrs.valKd idxs2adrK). qed.

lemma adr2adsK (ad : Address.adrs) :
  (forall i, 0 <= i < 3 \/ i = 7 => ad.[i] = W32.zero) =>
  valid_adrsidxs (adr2idxs ad) =>
  ads2adr (adr2ads ad) = ad.
proof. smt(HAX.Adrs.insubdK adr2idxsK). qed.

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

lemma size_lpath (lidx : int) :
  0 <= lidx <= 2^h => size (lpath lidx) = if lidx = 2^h then (h+1) else h.
proof.
by move=> hle @/lpath; rewrite size_rev BS2Int.size_int2bs; smt(h_g0).
qed.

lemma size_lpath_lt (lidx : int) :
  0 <= lidx < 2^h => size (lpath lidx) = h.
proof. by move=> ?; rewrite size_lpath /#. qed.

(* When working in subtrees of height t we need the suffix of length t
   of the path to the leaf, except in the corner case where we are at
   the end.  *)
op prefix(s : 'a list, t : int) = take (size s - t) s.
op suffix(s : 'a list, t : int) = drop (size s - t) s.

(* The path of the exit leaf is not a prefix of the path
   in the full tree, but it makes the theorems nicely commute *)
op lpathst (lidxo t : int) =
  rev (BS2Int.int2bs (t + (b2i (lidxo = 2^t))) lidxo).

(* Exiting a subtree breaks this identity *)
lemma lpathst_suffix (start lidxo t : int) :
   0 <= start <= 2^h - 2^t
=> 0 <= t <= h
=> 0 <= lidxo < 2^t
 => 2^t %| start
=> lpathst lidxo t =  suffix (lpath (start + lidxo)) t.
proof.
move => *.
rewrite /lpathst /lpath /suffix size_rev BS2Int.size_int2bs /=.
have -> /= : b2i (lidxo = 2 ^ t) = 0 by smt().
have -> /= : b2i (start + lidxo = 2 ^ h) = 0 by smt().
have -> /= : (max 0 h - t) = h-t by smt().
have -> := BS2Int.int2bs_cat t h (start + lidxo) _;1:smt().
rewrite rev_cat drop_cat_le ifT; 1: smt(size_take size_rev BS2Int.size_int2bs h_g0).
rewrite drop_oversize /=;1: smt(size_take size_rev BS2Int.size_int2bs h_g0).
congr;apply BS2Int.bs2int_eq;1,2:smt().
smt().
qed.

lemma size_lpathst (lidxo t : int) :
   0 <= t <= h
=> 0 <= lidxo <= 2^t
=> size (lpathst lidxo t) = if lidxo = 2^t then (t+1) else t.
proof.
move=> ?? @/lpathst;rewrite size_rev BS2Int.size_int2bs; smt().
qed.

lemma size_lpathst_lt (lidxo t : int) :
   0 <= t <= h
=> 0 <= lidxo < 2^t
=> size (lpathst lidxo t) = t.
proof. by move=> *; rewrite size_lpathst /#. qed.

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

op paths_from_leaf ( lidxo t : int) : path list =
  if (lidxo = 2^t) then [[]] (* we get the root *) else
  pmap (extract_path (lpathst lidxo t)) (range 0 t).

(* Move to List *)
lemma count_eq_nth ['a] (p : 'a -> bool) (s1 s2 : 'a list) :
     size s1 = size s2
  => (forall k, 0 <= k < size s1 => p (nth witness s1 k) = p (nth witness s2 k))
  => count p s1 = count p s2.
proof.
elim: s1 s2 => [|x1 s1 ih] [|x2 s2] //=; ~-1:smt(size_ge0).
(* Only solved by Z3 4.12.4 *)
move/addzI => eq_sz heqp; rewrite (heqp 0) ?(ih s2) => *; smt(size_ge0).
qed.

lemma paths_from_leaf_root t : paths_from_leaf (2^t) t = [[]].
proof. by rewrite /paths_from_leaf //=. qed.

hint simplify paths_from_leaf_root.

lemma lpath_root : lpath (2 ^ h) = true :: nseq h false.
proof.
have h_g0 := h_g0; move=> @/lpath @/b2i /=.
rewrite BS2Int.int2bs_pow2 ?mem_range 1:/# /=.
by rewrite nseq0 rev_cat /= rev_nseq.
qed.

lemma lpathst_root t :
   0 <= t <= h
=> lpathst  (2 ^ t) t = true :: nseq t false.
proof.
move => ht;move=> @/lpathst @/b2i /=.
rewrite BS2Int.int2bs_pow2 ?mem_range 1:/# /=.
by rewrite nseq0 rev_cat /= rev_nseq.
qed.

hint simplify lpath_root (* , lpathst_root *).

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


lemma pfl_size (lidxo t : int) :
    0 <= t <= h
 => 0 <= lidxo <= 2^t
 => size (paths_from_leaf lidxo t) = hw (lpathst lidxo t).
proof.
move => ?.
have ? := h_g0; case=> ge0_lidx /lez_eqVlt [->|lt].
- by rewrite /hw /= lpathst_root 1:/# /= count_nseq iffalse //=.
rewrite /paths_from_leaf [lidxo = _]ltr_eqF //=.
rewrite &(pfl_r_size) /lpathst /suffix.
by rewrite size_rev BS2Int.size_int2bs lez_maxr //#.
qed.

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
move=> rg_lidx @/leaves_from_path; rewrite size_lpath_lt 1:/# /=.
have h_gt0 := h_g0; rewrite iftrue 1:/# mkseq1 /=.
by rewrite /lpath revK BS2Int.int2bsK /#.
qed.

lemma lfp_nil : leaves_from_path [] = range 0 (2^h).
proof.
have h_gt0 := h_g0; rewrite /leaves_from_path ifT 1:/# /=.
by rewrite rev_nil BS2Int.bs2int_nil /= /mkseq id_map //#.
qed.

lemma lfp_st _lstart _sth:
   leaves_from_path (prefix (lpath _lstart) _sth) = range _lstart (_lstart + 2 ^ _sth).
admitted.

(* The leaf node corresponding to a leaf path
   The semantics of this needs to be computed from wots using
   operators and then proved equivalent to the imperative code. *)
op wots_pk_val(ss ps : Params.nbytes, ad : SA.adrs, lidx : int) : dgstblocklenlist =
   pkWOTS_from_skWOTS (gen_skWOTS ss ps ad) ps ad.

op leafnode_from_idx(ss ps : Params.nbytes, ad : adrs, lidx : int) : dgstblock =
 let pk = wots_pk_val ss ps (set_kpidx (set_typeidx ad 0) lidx) lidx in
 bs2block (ltree ps (ads2adr (set_kpidx (set_typeidx ad 1) lidx))
           (LenNBytes.insubd (map NBytes.insubd (chunk n (BitsToBytes (flatten (map DigestBlock.val (DBLL.val pk)))))))).
(*
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
*)

lemma Eqv_WOTS_pkgen  (ad : adrs) (ss ps : seed) :
  hoare[WOTS.pkGen : arg = (ss, ps, ads2adr ad) ==>
     LenNBytes.insubd (map NBytes.insubd (chunk n (BitsToBytes (flatten (map DigestBlock.val (DBLL.val
       (pkWOTS_from_skWOTS (gen_skWOTS ss ps ad) ps ad))))))) = res].
admitted.

lemma Eqv_WOTS_pkgen_ll  :
 islossless WOTS.pkGen.
admitted.

(* list of all the leaves up to an index, exclusive *)
op leaf_range(ss ps : Params.nbytes, ad : SA.adrs, start lidxo  : int) =
   map (leafnode_from_idx ss ps ad) (range start lidxo).

lemma leaf_range0 ss ps ad s : 0 <= s => leaf_range ss ps ad s 0 = [].
proof. move => *; by rewrite /leaf_range range_geq. qed.

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
op stack_from_leaf (start lidxo t : int, ss ps : Params.nbytes, ad : SA.adrs) : (dgstblock * int) list =
  map (fun p => (node_from_path (prefix (lpath start) t ++ p) ss ps ad,  t - size p)) (paths_from_leaf lidxo t).

lemma sfl_size start lidxo t ss ps ad :
    0 <= t <= h
 => 0 <= start <= 2^h - 2^t
 => 2^t %| start
 => 0 <= lidxo <= 2^t
 => size (stack_from_leaf start lidxo t ss ps ad) = hw (lpathst lidxo t).
proof. move=> *; rewrite /stack_from_leaf size_map pfl_size //. qed.

(* The list of leaves that fall under the first node in the stack when one starts to process leaf lidx
   The case o lidx=0 is a corner case, as the stack is empty *)
op first_subtree_leaves(start lidxo t : int,ss ps : Params.nbytes, ad : SA.adrs) =
 if lidxo = 0 then
   []
 else
   let lps = (paths_from_leaf lidxo t) in
   let p1 = prefix (lpath start) t ++ head witness lps in
   let lp1 = leaves_from_path p1 in
   map (leafnode_from_idx ss ps ad) lp1.

(* The hamming weight of 0 is 0, so stack is empty *)
lemma pfl0 t :
    0 <= t <= h
 =>   paths_from_leaf 0 t = [].
proof.
move => *;have expr_gt0 := expr_gt0; apply/size_eq0.
rewrite pfl_size //= 1:/#.
by rewrite /lpathst /= BS2Int.int2bs0 /= /hw count_rev count_nseq /pred1 //=.
qed.

lemma stack_from_leaf0 start t ss ps ad :
    0 <= t <= h
 => 0 <= start <= 2^h - 2^t
 => 2^t %| start
 => stack_from_leaf start 0 t ss ps ad = [].
proof. move => *;rewrite /stack_from_leaf pfl0 //. qed.

(* This op describes the state of the stack in the inner loop, while
   reducing, where o is the current offset = size of stack = sfl ++ [rednode].
   There are two cases: either the hw increased by one, then there
   is nothing to do. Or it has decreased and we enter the loop.
   The loop performs as many iterations as needed to reduce the
   hamming weight of lidx to hamming weight of lidx+1, if any. *)
op stack_increment (start lidxo t : int, ss ps : Params.nbytes, ad : SA.adrs, offset : int) =
  (* the stack configuration is the state encountered for lidx
     with the extra node computed for lidx at the end *)
  let hwi = hw (lpathst lidxo t) in
  let hwi1 = hw (lpathst (lidxo + 1) t) in
  if hwi < hwi1
  (* Then then case only happens when lidx is even, in which
     case we are already in the state we need on exit *)
  then stack_from_leaf start lidxo t ss ps ad ++
          [(node_from_path (lpath (start +lidxo)) ss ps ad, 0)]
  else
      (* we reach this point with hw1 <= offset <= hw + 1
         we still did not touch the first (offset - 1) positions in the old stack
         the node stored at offset - 1 corresponds to the node reduced along the
         path to lidx that we can also compute *)
      let oldstack = stack_from_leaf start lidxo t ss ps ad in
      let level = if offset = size oldstack + 1
                  then 0 (* we always start reducing with a leaf *)
                  else (nth witness oldstack (offset - 1)).`2 + 1 in
      let carrypath = (take (h - level) (lpath (start + lidxo)))
      in (take (offset - 1) oldstack) ++
                        [(node_from_path carrypath ss ps ad, level)].

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

lemma hwincSE_lpathst (lidxo t : int) :
    0 <= t <= h
 => 0 <= lidxo < 2^t =>
     (   lidxo = 2^t - 1
      /\ lpathst lidxo t = nseq t true
      /\ lpathst (lidxo + 1) t = true :: nseq t false)
  \/ (   lidxo < 2^t - 1
      /\ let k = argmax (fun i => take i (BS2Int.int2bs t lidxo)) (all idfun) in
         hw (lpathst (lidxo + 1) t) = hw (lpathst lidxo t) + 1 - k).
proof.
move => ?;case=> rg0_lidx /ltzE /lez_eqVlt [SlidxE | lt_Slidx]; [left | right].
- have ->/=: lidxo = 2^t - 1 by apply/Ring.IntID.subr_eq.
  rewrite /lpathst !int2bs_pow2B1 /=; ~-1:smt(h_g0).
  rewrite b2i0_eq 1:/# /= nseq0 cats0 rev_nseq /=.
  rewrite BS2Int.int2bs_pow2 /=;1:smt(mem_range).
  by rewrite nseq0 /= rev_cat rev_nseq rev1 //.
- split=> [/# | k @/lpath]; rewrite !hw_rev.
  rewrite [lidxo + 1 = _]ltr_eqF // [lidxo = _]ltr_eqF 1:/#.
  by have /= := hwincSE t lidxo _ _ _;smt().
qed.

(* hw increases by exactly 1 *)
lemma hwinc lidxo t :
    0 <= t <= h
 => 0 <= lidxo < 2^t
   => hw (lpathst lidxo t) < hw (lpathst (lidxo+1) t)
   => hw (lpathst (lidxo+1) t) = hw (lpathst lidxo t) + 1.
proof.
move=> ?;case => *. 
have := hwincSE_lpathst lidxo t _ _;1,2:smt().
smt(ge0_argmax hw_nseq).
qed.

(* we don't enter the loop if hw increased *)
lemma hwinc_noentry start lidxo t ss ps ad offset:
    0 <= t <= h
 => 0 <= start <= 2^h - 2^t
 => 2^t %| start
 => 0 <= lidxo < 2^t =>
    hw (lpathst lidxo t) < hw (lpathst (lidxo + 1) t) =>
   let si = stack_increment start lidxo t ss ps ad offset in
    ((size si < 2) \/
     (2 <= size si /\
       (nth witness si (size si - 1)).`2 <>
         (nth witness si (size si - 2)).`2)).
move=> tr sr tdiv lt hinc si; have siE: si =
  stack_from_leaf start lidxo t ss ps ad ++ [(node_from_path (lpath (start+lidxo)) ss ps ad, 0)].
- by rewrite /si /stack_increment /=; rewrite hinc.
have ? := h_g0; move: lt hinc => ^[ge0_lidx _]; case/(hwincSE_lpathst lidxo t tr).
- move=> [# + -> ->] /= -; rewrite !hw_nseq /= 1,2: /#.
  move => ??;rewrite /si; have -> : lidxo = 0 by smt(Ring.IntID.expr0).
  left; rewrite /stack_increment /= /lpathst /= /stack_from_leaf /=/paths_from_leaf /= /extract_path /=.
  have -> /= : b2i (0 = 2 ^ t) = 0 by smt(Ring.IntID.expr0).
  have -> /= : b2i (1 = 2 ^ t) = 1 by smt(Ring.IntID.expr0).
  rewrite !BS2Int.int2bs0 /= !BS2Int.int2bs1 /= 1:/#.
  have ->  /=: hw (rev (nseq t false)) < hw (rev (true :: nseq t false)). 
  + by rewrite /hw rev_cons !rev_nseq -cats1 count_cat /= !count_nseq /#.
  have -> /= : (0 = 2 ^ t) = false by smt(Ring.IntID.expr0).
  rewrite size_cat size_map pmap_map size_map /= /lpathst /= size_filter count_map /preim /=.
  have -> /= : b2i (0 = 2 ^ t) = 0 by smt(Ring.IntID.expr0).
  rewrite count_pred0_eq_in; last by smt().
  move => *; rewrite !BS2Int.int2bs0 /= /extract_path rev_nseq /predC1 /= ifF; last by smt(). 
  smt(nth_nseq_if).
(pose k':= argmax _ _) => [# /= *].
have := int2bs_incSE t lidxo _ _ _; ~-1: by move=> //#.
rewrite -/k' /= => [#] _ _ /=.
have ->: k' = 0 by smt(ge0_argmax).
rewrite nseq0 /= nth0_head => hhd eqE.
case: (size si < 2) => /= [//|/lezNgt ^ge2_sz -> /=].
rewrite nth_last {1}siE last_cat /= eq_sym.
have ?: 0 < size (stack_from_leaf start lidxo t ss ps ad).
- by move: ge2_sz; rewrite siE size_cat /= /#.
pose d := (nth witness si (size si - 2)).`2.
have: d \in map snd (stack_from_leaf start lidxo t ss ps ad).
- apply/(@map_f snd); rewrite siE nth_cat size_cat /= iftrue 1:/#.
  apply/mem_nth; smt().
rewrite /stack_from_leaf -map_comp /(\o) /= => /mapP /=.
case=> p [+ ->] - @/paths_from_leaf; case: (lidxo = _) => /= [->/=|].
+ smt(Ring.IntID.expr0).
case/pmapP=> i [/mem_range rgi] @/extract_path.
case: (nth false (lpathst lidxo t) i) => // nthi /someI ->.
rewrite size_rcons size_take ~-1:/# size_lpathst ~-1:/#.
rewrite [lidxo = _]ltr_eqF 1:/# /= iftrue 1:/#.
suff: i <> t - 1 by smt().
apply: contraL nthi => ->; rewrite {2}(_ : t = size (lpathst lidxo t)).
- by rewrite size_lpathst /#.
by rewrite nth_last /lpath last_rev b2i0_eq 1:/# /= hhd.
qed.

(* hw increase implies odd, so last node in paths is the previous leaf *)
lemma hwinc_leaflast lidxo t :
    0 <= t <= h
 => 0 <= lidxo < 2^t
   => hw (lpathst lidxo t) < hw (lpathst (lidxo + 1) t)
   =>    size (nth witness (paths_from_leaf (lidxo + 1) t) (hw (lpathst lidxo t))) = t
      /\ lidxo = BS2Int.bs2int (rev (nth witness (paths_from_leaf (lidxo + 1) t) (hw (lpathst (lidxo + 1) t) - 1))).
proof.
move=> tr lt hinc.
case (t = 0).
+ move => Ht;rewrite Ht /=;have Hlidxo : lidxo = 0 by smt(Ring.IntID.expr0).
  by rewrite /paths_from_leaf !Hlidxo /= /lpathst /= BS2Int.int2bs0 BS2Int.int2bs1 1:/# /= nseq0 /=  rev1  /= rev_nil BS2Int.bs2int_nil /=.
move => tg0.
 move: lt hinc => ^[ge0_lidx _]; case/(hwincSE_lpathst lidxo t tr).
- move=> [# + -> ->] /= - -> /=; rewrite !hw_nseq /= // 1,2:/# => tl1.
  rewrite ifT 1:/# /= rev_nil BS2Int.bs2int_nil;smt(Ring.IntID.expr0).
(pose k':= argmax _ _) => [# /= *].
have := int2bs_incSE t lidxo _ _ _; ~-1: by move=> //#.
rewrite -/k' /= => [#] _ _ /=.
have ->: k' = 0 by smt(ge0_argmax).
move=> + _ +; rewrite nseq0 /= nth0_head => hhd eqE.
rewrite /paths_from_leaf !iffalse ~-1:/#.
pose p1 := lpathst (lidxo + 1) t; pose p2 := lpathst lidxo t.
have: exists s, size s = t - 1 /\ ((p1 = rcons s true) /\ (p2 = rcons s false)). (* FACTOR OUT *)
- exists (rev (drop 1 (BS2Int.int2bs t lidxo))); split.
  - by rewrite size_rev size_drop // BS2Int.size_int2bs;smt(Ring.IntID.expr0).
  split.
  - by rewrite /p1 /lpathst ltr_eqF 1:/# /= eqE rev_cons.
  - rewrite /p2 /lpathst ltr_eqF 1:/# /= -rev_cons; congr.
    rewrite -{1}[BS2Int.int2bs _ _](cat_take_drop 1) -cat1s; congr.
    rewrite -[BS2Int.int2bs _ _]drop0 (drop_take1_nth false) /=.
    - by rewrite BS2Int.size_int2bs /#.
    - by rewrite nth0_head.
case=> s [szs [^p1E-> ^p2E->]]; rewrite !hw_rcons /=.
have ->: nth witness (pmap (extract_path (rcons s true)) (range 0 t)) (hw s) = rcons s false.
- rewrite (range_cat (t - 1)) ~-1:/# pmap_cat nth_cat.
  rewrite pfl_r_size_min ~-1:/# (_ : take (t - 1) (rcons s true) = s).
  - by rewrite -cats1 take_cat szs /= cats0.
  rewrite ltrr /= (rangeS (t - 1)) /= /extract_path.
  rewrite nth_rcons szs /= -[rcons s true]cats1 take_cat.
  by rewrite szs /= cats0.
rewrite size_rcons szs /= rev_rcons.
move/(congr1 rev)/(congr1 BS2Int.bs2int): p2E.
rewrite /p2 rev_rcons => <- @/lpath; rewrite revK.
by rewrite [lidxo = 2^t]ltr_eqF 1:/# /= BS2Int.int2bsK //#.
qed.


(* hw increase implies all previous paths same as before *)
lemma hwinc_pathsprev lidxo t k :
    0 <= t <= h
 => 0 <= lidxo < 2^t =>
    hw (lpathst lidxo t) < hw (lpathst (lidxo  + 1) t) =>
     0 <= k < hw (lpathst lidxo t) =>
      (nth witness (paths_from_leaf (lidxo  + 1) t) k)
      = (nth witness (paths_from_leaf lidxo t) k).
proof.
move=> tr lt hinc.
case (t = 0).
+ move => Ht;rewrite Ht /=;have Hlidxo : lidxo = 0 by smt(Ring.IntID.expr0).
  rewrite /paths_from_leaf !Hlidxo /= /lpathst /= BS2Int.int2bs0 nseq0 /=.
  rewrite rev_nil /hw /= /#.
move => tg0.
 move: lt hinc => ^[ge0_lidx _]; case/(hwincSE_lpathst lidxo t tr).
- move=> [# + -> ->] /= - -> /=; rewrite !hw_nseq /= // /#.
(pose k':= argmax _ _) => [# /= *].
have := int2bs_incSE t lidxo _ _ _; ~-1: by move=> //#.
rewrite -/k' /= => [#] _ _ /=.
have ->: k' = 0 by smt(ge0_argmax).
move=> + _ +; rewrite nseq0 /= nth0_head => hhd eqE.
rewrite /paths_from_leaf !iffalse ~-1://#.
pose p1 := lpathst (lidxo + 1) t; pose p2 := lpathst lidxo t.
have: exists s, size s = t - 1 /\ ((p1 = rcons s true) /\ (p2 = rcons s false)).
- exists (rev (drop 1 (BS2Int.int2bs t lidxo))); split.
  - by rewrite size_rev size_drop // BS2Int.size_int2bs /#.
  split.
  - by rewrite /p1 /lpathst ltr_eqF 1:/# /= eqE rev_cons.
  - rewrite /p2 /lpathst ltr_eqF 1:/# /= -rev_cons; congr.
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
- have: k < hw (lpathst lidxo t) by smt().
  by rewrite -/p2 p2E hw_rcons /=.
apply: pfl_eq; first 2 smt().
- move=> n ge0_n; rewrite -!cats1 !take_cat.
  by case: (n < size s) => /=; rewrite ?hw_cat; smt().
- by rewrite hw_rcons /= /#.
- by rewrite hw_rcons /= /#.
qed.

(* hw decrease implies odd, so last node in old stack is leaf *)
lemma hwnoinc_leaflast lidxo t :
    0 <= t <= h
 => 0 <= lidxo < 2^t =>
    hw (lpathst (lidxo  + 1) t) <= hw (lpathst lidxo t)  =>
     (0 < hw (lpathst lidxo t) /\
     size (nth witness (paths_from_leaf lidxo t) ((size (paths_from_leaf lidxo t)) - 1)) = t).
proof.
move=> tr lt hinc.
have Ht : 0 < t.
+  case (t  = 0) => /= H; 2: smt().
   move : hinc; have -> /= : lidxo = 0 by smt(Ring.IntID.expr0).
   rewrite H /lpathst /hw /= BS2Int.int2bs0 /= !nseq0 rev_nil /=.
   by rewrite BS2Int.int2bs1 //= nseq0 /= rev1 /= /#.
 move: lt hinc => ^[ge0_lidx _]; case/(hwincSE_lpathst lidxo t tr).
- move=> [# + -> ->] /= - -> /=; rewrite !hw_nseq /= //= 1,2:/# => lt1.
  split;1:smt().
  rewrite /paths_from_leaf /= ifF 1:/# /= nth_last /extract_path pmap_map /=. 
  rewrite -last_map -map_comp.
  have [#[H1 _]]:= all_filterP (predC1 None) (map
           (fun (i : int) =>
              if nth false (lpathst (2 ^ t - 1) t) i then Some (rcons (take i (lpathst (2 ^ t - 1) t)) false) else None)
           (range 0 t)).
  rewrite H1.
  + rewrite /predC1 all_map /preim /= allP => x ? /=; rewrite ifT;last by smt().
    rewrite /lpathst /=.
    have-> /=: b2i (2 ^ t - 1 = 2 ^ t) = 0 by smt().
    rewrite BS2Int.int2bs_cat_nseq_true_false 1:/# /= nseq0 cats0 /= rev_nseq.
    by rewrite nth_nseq_if;smt(mem_range). 
  rewrite -map_comp /(\o) /=.
  rewrite (range_cat (t-1) 0 t) 1,2:/# map_cat.
  have -> : (range (t-1) t)  = (range (t-1) ((t-1) + 1)) by smt().
  rewrite rangeS /= -cat_rcons cats0 last_rcons.
  rewrite ifT.
  + rewrite /lpathst.
    have-> /=: b2i (2 ^ t - 1 = 2 ^ t) = 0 by smt().
    rewrite BS2Int.int2bs_cat_nseq_true_false 1:/# /= nseq0 cats0 /= rev_nseq.
    by rewrite nth_nseq_if;smt(mem_range). 
  rewrite oget_some /= size_rcons /= size_take 1:/#.
  rewrite /lpathst.
  have-> /=: b2i (2 ^ t - 1 = 2 ^ t) = 0 by smt().
  rewrite BS2Int.int2bs_cat_nseq_true_false 1:/# /= nseq0 cats0 /= rev_nseq.
  by rewrite size_nseq /#.
(pose k':= argmax _ _) => [# /= ? -> ?]; have ?: 0 < k' by smt().
have := int2bs_incSE t lidxo _ _ _; ~-1: by move=> //#.
rewrite -/k' /= => [#] _ _ /= => hhd eqE1 eqE2; split.
- rewrite /lpath hw_rev b2i0_eq 1:/# /=.
  by rewrite eqE1 hw_cat /= hw_nseq ~-1:/# /=; smt(ge0_hw).
rewrite pfl_size 1:/# /paths_from_leaf 1:/# iffalse 1:/#.
rewrite /lpathst hw_rev b2i0_eq 1:/# /=.
rewrite -hw_rev; have <- := pfl_r_size (rev (BS2Int.int2bs t lidxo)) t.
- by rewrite size_rev BS2Int.size_int2bs //#.
rewrite nth_last (range_cat (t - 1)) ~-1:/# pmap_cat rangeS /=.
pose q := extract_path _ (t - 1).
suff ->/=: q = Some (rcons (take (t - 1) (rev (BS2Int.int2bs t lidxo))) false).
- rewrite last_cat /= size_rcons size_take_condle ~-1:/#.
  by rewrite size_rev BS2Int.size_int2bs /#.
rewrite /q /extract_path /= nth_rev ?BS2Int.size_int2bs 1:/# /=.
rewrite lez_maxr 1:/# /= iftrue // eqE1 nth_cat.
by rewrite size_nseq iftrue ~-1:/# nth_nseq /#.
qed.

lemma take_nseq ['a] (i j : int) (x : 'a) : 0 <= i <= j =>
  take i (nseq j x) = nseq i x.
proof. by move=> rg; rewrite -!mkseq_nseq take_mkseq. qed.

(* if inner loop exited, then we have reached the final stack size *)
lemma hwdec_exit start lidxo t ss ps ad offset :
    0 <= t <= h
 => 0 <= start <= 2^h - 2^t
 => 2^t %| start
 => 0 <= lidxo < 2^t
   => hw (lpathst (lidxo + 1) t) <= hw (lpathst lidxo t)
   => hw (lpathst (lidxo + 1) t) <= offset <= hw (lpathst lidxo t) + 1
   => let si = stack_increment start lidxo t ss ps ad offset in
      (   size si < 2
       \/ (2 <= size si /\ (nth witness si (size si - 1)).`2 <> (nth witness si (size si - 2)).`2))
   => offset = hw (lpathst (lidxo + 1) t) /\ size si = hw (lpathst (lidxo + 1) t).
proof.
move=> tr sr ds lt hinc.
case (t = 0). admit.
move => gt0t.
 move: lt hinc => ^[ge0_lidx _]; case/(hwincSE_lpathst lidxo t tr).
- admit.
(pose k':= argmax _ _) => [# /=] ? + ^hdec - -> ?.
have ?: 0 < k' by smt().
have := int2bs_incSE t lidxo _ _ _; ~-1: by move=> //#.
rewrite -/k' /= => [#] ?? /= => hhd eqE1 eqE2 hoff.
pose si := stack_increment _ _ _ _ _ _ _.
print stack_increment.
pose oldstack := stack_from_leaf start lidxo t ss ps ad.
pose level :=
  if   offset = size oldstack + 1
  then 0
  else (nth witness oldstack (offset - 1)).`2 + 1.
pose carrypath := take (h - level) (lpath (start + lidxo)).
have siE : si =
  take (offset - 1) oldstack ++ [(node_from_path carrypath ss ps ad, level)].
- by rewrite /si /stack_increment /= iffalse //= /#.
move=> hsz; rewrite -andaE; split; last first.
- rewrite siE => -> /=; rewrite size_cat /= size_take_condle.
  - rewrite /lpathst hw_rev b2i0_eq 1:/# /=.
    by rewrite eqE1 hw_cat /= hw_nseq 1:/# /=; smt(ge0_hw).
  by rewrite sfl_size 1..4:/# iftrue /#.
have szod: size oldstack = hw (lpathst lidxo t). 
- by rewrite /oldstack sfl_size /#.
have ltk': k' <= hw (lpathst lidxo t).
- rewrite /lpathst hw_rev b2i0_eq 1:/# /= eqE1.
  by rewrite hw_cat hw_nseq 1:/# /=; smt(ge0_hw).
have nthod: forall i, 0 <= i < k' => (nth witness (rev oldstack) i).`2 = i.
- move=> i rgi; rewrite nth_rev /oldstack sfl_size ~-1:/#.
  rewrite /stack_from_leaf (nth_map witness) 1:pfl_size ~-1:/# /=.
  rewrite /paths_from_leaf iffalse 1:/# (range_cat (t - (i+1))) ~-1:/#.
  have eqsz: hw (lpathst lidxo t) - (i + 1) =
    size (pmap (extract_path (lpathst lidxo t)) (range 0 (t - (i + 1)))).
  - rewrite &(eq_sym) /= pfl_r_size_min 1:/# {2}/lpathst b2i0_eq 1:/# /=.
    rewrite -[BS2Int.int2bs _ _](cat_take_drop (i + 1)).
    rewrite rev_cat 2?(rev_take, rev_drop) ?BS2Int.size_int2bs ~-1:/#.
    rewrite lez_maxr 1:/# hw_cat /lpathst b2i0_eq 1:/# /=.
    rewrite -addrA -{1}[hw _]addr0; congr; apply/eq_sym.
    rewrite {1}[t](_ : _ = size (BS2Int.int2bs t lidxo)).
    - by rewrite BS2Int.size_int2bs /#.
    rewrite -rev_take ?BS2Int.size_int2bs 1:/# hw_rev eqE1.
    rewrite take_cat' take_nseq ~-1:/# hw_cat hw_nseq /= 1:/#.
    by rewrite size_nseq iftrue 1:/# /=.
  rewrite pmap_cat nth_cat iffalse; first by rewrite eqsz.
  rewrite eqsz /= range_ltn 1:/# /=.
  have ->/=: extract_path (lpathst lidxo t) (t - (i + 1)) =
    Some (rcons (take (t - (i + 1)) (lpathst lidxo t)) false).
  - rewrite /extract_path iftrue //= /lpathst nth_rev.
    - by rewrite BS2Int.size_int2bs /= b2i0_eq /#.
    rewrite b2i0_eq 1:/# BS2Int.size_int2bs lez_maxr 1:/# /=.
    rewrite [t - _](_ : _ = i) 1:#ring eqE1 nth_cat.
    by rewrite size_nseq iftrue 1:/# nth_nseq //#.
  by rewrite size_rcons /= size_take 1:/# size_lpathst /#.
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

(* final state of stack after reduction *)
lemma stack_final start lidxo t ss ps ad :
    0 <= t <= h
 => 0 <= start <= 2^h - 2^t
 => 2^t %| start
 => 0 <= lidxo < 2^t =>
   forall k, 0 <= k < hw (lpathst (lidxo  + 1) t) =>
         nth witness (stack_increment start lidxo t ss ps ad (hw (lpathst (lidxo + 1) t)))  k
       = nth witness (stack_from_leaf start (lidxo + 1) t ss ps ad) k.
proof.
move => ???? k *.
case (hw (lpathst (lidxo + 1) t) <= hw (lpathst lidxo t)) => *;last first.
+ rewrite /stack_increment /= ifT 1:/#.
  rewrite nth_cat sfl_size 1..4:/#.
  case (k < hw (lpathst lidxo t)) => *.
  +  have := hwinc_pathsprev  lidxo t k _ _ _. smt(). smt(). smt().
     rewrite /stack_from_leaf !(nth_map witness) /=; smt(pfl_size).
  rewrite ifT;1:smt(hwinc).
  have ->: k = hw (lpathst (lidxo + 1) t) - 1 by smt(hwinc).
  rewrite /stack_from_leaf !(nth_map witness) /=;1: smt(pfl_size).
  have := hwinc_leaflast lidxo t _ _ _;1..3: smt().
  move => [H H1];split; last  by smt(hwinc pfl_size).
  admit.
admitted.

lemma si_size_in_loop start lidxo t ss ps ad offset :
    0 <= t <= h
 => 0 <= start <= 2^h - 2^t
 => 2^t %| start
 => 0 <= lidxo < 2^t =>
hw (lpathst (lidxo + 1) t) <= hw (lpathst lidxo t) =>
hw (lpathst (lidxo + 1) t) <= offset <= hw (lpathst lidxo t) + 1 =>
2 <= offset =>
(nth witness (stack_increment start lidxo t ss ps ad offset) (offset - 1)).`2 = 
(nth witness (stack_increment start lidxo t ss ps ad offset) (offset - 2)).`2 =>
   size ((stack_increment start lidxo t ss ps ad offset)) = offset /\
   size (stack_from_leaf start (lidxo + 1) t ss ps ad) < offset.
admitted.
(*
move => *;split.
+ move => *; rewrite /stack_increment /= ifF 1:/#.
  rewrite size_cat /= size_take 1:/#.
  smt(sfl_size).
admit. (* not finished yet *)
qed. *)


(* entering the inner loop for a leaf tree means that
   we are still hashing values at height < h-1: when
   we exit the loop for leaf 2^h - 1 we have produced a
   hash at level h *)
lemma si_heights_in_loop_bnd start lidxo t ss ps ad offset k :
    0 <= t <= h
 => 0 <= start <= 2^h - 2^t
 => 2^t %| start
 => 0 <= lidxo < 2^t =>
hw (lpathst (lidxo + 1) t) <= hw (lpathst lidxo t) =>
2 <= offset =>
(nth witness (stack_increment start lidxo t ss ps ad offset) (offset - 1)).`2 = 
(nth witness (stack_increment start lidxo t ss ps ad offset) (offset - 2)).`2 =>
0<= k < offset =>
 0<= (nth witness
   (stack_increment start lidxo t ss ps ad offset) k).`2 < h.
proof.
move => *.
admitted.

(* In the inner loop, the final node in the stack
  is the hash of the last two nodes in the previous
  stack
lemma si_reduced_node start lidxo t ss ps ad offset :
  0 <= t <= h
  => 0 <= start <= 2^h - 2^t
  => 2^t %| start
  => 0 <= lidxo < 2^t =>
  hw (lpathst start (lidxo + 1) t) <= hw (lpathst start lidxo t) =>
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
proof.
move => ? Hw ?? /=.
admitted.
*)
lemma si_reduced_node start lidxo t ss ps ad offset :
  0 <= t <= h
  => 0 <= start <= 2^h - 2^t
  => 2^t %| start
  => 0 <= lidxo < 2^t =>
  hw (lpathst (lidxo + 1) t) <= hw (lpathst lidxo t) =>
  2 <= offset =>
  (nth witness (stack_increment start lidxo t ss ps ad offset) (offset - 1)).`2 =
  (nth witness (stack_increment start lidxo t ss ps ad offset) (offset - 2)).`2 =>
  let si = (stack_increment start lidxo t ss ps ad offset) in
  let si1 = (stack_increment start lidxo t ss ps ad (offset - 1)) in
  (nth witness si1 (offset - 2)).`1 =
  trh ps (set_thtbidx (set_typeidx (adr2ads zero_address) trhtype)
          ((nth witness si (offset - 1)).`2 + 1) ((start + lidxo) %/ 2 ^ ((nth witness si (offset - 1)).`2 + 1)))
          ( (DigestBlock.val (nth witness si (offset - 2)).`1) ++
           (DigestBlock.val (nth witness si (offset - 1)).`1)).
proof.
move => ? Hw ?? /=.
admitted.

(* growth of leaves under the leftmost subtree *)
lemma growth ss ps ad leaves start lidxo t :
    0 <= t <= h
 => 0 <= start <= 2^h - 2^t
 => 2^t %| start
 => 0 <= lidxo < 2^t =>
size leaves = lidxo =>
 take (size (first_subtree_leaves start (size leaves) t ss ps ad)) leaves =
   first_subtree_leaves start (size leaves) t ss ps ad =>
 take (size (first_subtree_leaves start (lidxo + 1) t ss ps ad))
   (rcons leaves (leafnode_from_idx ss ps ad (start + lidxo))) =
 first_subtree_leaves start (lidxo + 1) t ss ps ad.
admitted.

(*
phoare leaves_correct _ps _ss  _ad :
 [ FL_XMSS_TW_ES.leaves_from_sspsad :
  arg = (_ss, _ps, _ad)  ==>
   res =
  map
    (leafnode_from_idx (NBytes.insubd (NBytes.val _ss)) (NBytes.insubd (NBytes.val _ps))
       (set_layer_addr zero_address 0)) (range 0 (2 ^ h)) ] = 1%r.
admitted.
*)

phoare leaves_correct _ps _ss  _ad :
 [ FL_XMSS_TW_ES.leaves_from_sspsad :
  arg = (_ss, _ps, _ad)  ==>
   res =
  map
    (leafnode_from_idx (NBytes.insubd (NBytes.val _ss)) (NBytes.insubd (NBytes.val _ps)) _ad)
      (range 0 (2 ^ h)) ] = 1%r.
admitted.

(*
phoare tree_hash_correct _ps _ss _lstart _sth _ad :
[ XMSS_TreeHash.TreeHash.treehash :
    arg = (_ps,_ss,_lstart,_sth,_ad)
/\  _ad = zero_address /\ 0 <= _sth <= h /\ 0 <= _lstart <= 2^h - 2^_sth  /\ 2^_sth %| _lstart 
 ==>
  DigestBlock.insubd (BytesToBits (NBytes.val res)) =  
    val_bt_trh (list2tree (map (leafnode_from_idx _ss _ps _ad) 
     (range  _lstart (_lstart + 2^_sth)))) _ps (set_typeidx zero_address trhtype) _sth _lstart  ] = 1%r.
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
  call Eqv_WOTS_pkgen_ll.
  + auto => /> &hr ? h o; rewrite uleE /=;split; smt(W64.to_uint_cmp).
  by auto => /> /#.

proc => /=.    
wp;while ( #{/~_ad = zero_address}{~address = _ad}pre
    /\ 0 <= i <= 2^t 
    /\ (forall k, 0<=k<3 => address.[k] = W32.zero)
    /\  size stack = h + 1 /\ size heights = h + 1
    /\ (let stacklist = stack_from_leaf _lstart i _sth _ss _ps _ad in
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
  + move => ad hs i o st 7? H.
    have @/bs2block -> := (H 0 _) => /=.
    have -> : i = 2^_sth by smt(). 
    rewrite sfl_size 1..4:/#; have-> := lpathst_root _lstart _sth _ _ _;1..3:smt(). 
    rewrite /hw /=;smt(count_ge0).
  + rewrite /stack_from_leaf nth0_head /paths_from_leaf /= ifT 1:/# /= cats0 /=.
    rewrite /node_from_path. 
    case (_sth = h) => Ht.
    +  rewrite /prefix ifF;1:by smt(size_lpath StdOrder.IntOrder.expr_gt0 h_g0 take0).  
       rewrite ifT /=;1:by smt(size_lpath StdOrder.IntOrder.expr_gt0 h_g0 take0).    
       congr; -2: by smt(take_size size_take size_ge0 size_lpath StdOrder.IntOrder.expr_gt0). 
       congr;congr; smt(lfp_st).
       rewrite lfp_st /range iotaS_minus;smt(StdOrder.IntOrder.expr_gt0).
    case (_sth = 0) => H0. 
    +  rewrite /prefix ifT;1:smt(take_size size_take size_ge0 size_lpath StdOrder.IntOrder.expr_gt0 h_g0). 
       have -> /= : (range _lstart (_lstart + 2 ^ _sth)) = [_lstart] by rewrite H0 /= rangeS.
        rewrite H0 list2tree1 /=;congr.
        rewrite take_size /lpath revK BS2Int.int2bsK;smt(h_g0 StdOrder.IntOrder.expr_gt0).
    rewrite /prefix ifF;1:by smt(take_size size_take size_ge0 size_lpath StdOrder.IntOrder.expr_gt0 h_g0).  
    rewrite ifT /=;1:by smt(take_size size_take size_ge0 size_lpath StdOrder.IntOrder.expr_gt0 h_g0). 
    congr; -2: by smt(take_size size_take size_ge0 size_lpath StdOrder.IntOrder.expr_gt0). 
    congr;congr; smt(lfp_st).
    by rewrite lfp_st /range iotaS_minus;smt(StdOrder.IntOrder.expr_gt0).

seq 6 : (#pre /\
   bs2block node = leafnode_from_idx _ss _ps _ad (_lstart + i)).  
+ seq 3 : (#pre /\   pk = LenNBytes.insubd
  (map NBytes.insubd
     (chunk n
        (BitsToBytes
           (flatten (map DigestBlock.val (DBLL.val (wots_pk_val _ss _ps (set_kpidx (set_typeidx _ad 0) (_lstart + i)) (_lstart + i))))))))).
  + conseq />;1: smt().
    ecall (Eqv_WOTS_pkgen address sk_seed  pub_seed ).
    auto => /> &1 &2 ????????????;split;1:smt(Array8.get_setE). 
    congr;congr;congr;congr;congr;congr;congr. 
    + rewrite /wots_pk_val;congr. 
      + congr. admit. (* address semantics *)
    rewrite /set_ots_addr /set_kpidx /set_idx.  admit. (* address semantics *)
  ecall  (ltree_eq  pub_seed address  pk ).
  auto => /> &1 &2 ????????????;split;1: by move => *; rewrite /set_ltree_addr /set_type; smt(Array8.get_setE).
  rewrite /leafnode_from_idx /= /bs2block;congr;congr;congr;congr. 
  +  rewrite /set_ltree_addr /set_kpidx /set_idx. admit.  (* address semantics *)

wp. 
while (
 pub_seed = _ps /\
     sk_seed = _ss /\
     s = _lstart /\
     t = _sth /\ 0 <= _sth /\ _sth <= h /\ 0 <= _lstart /\ _lstart <= 2 ^ h - 2 ^ _sth /\ 2 ^ _sth %| _lstart /\ 
    0 <= i <= 2 ^ t 
 /\   (hw (lpathst _lstart i _sth) < hw (lpathst _lstart (i + 1) _sth) => to_uint offset = hw (lpathst _lstart (i + 1) _sth)) 
 /\ (hw (lpathst _lstart (i + 1) _sth) <= hw (lpathst _lstart i _sth) => 
         hw (lpathst _lstart (i + 1) _sth) <= to_uint offset <= hw (lpathst _lstart i _sth) + 1)
 /\size stack = h + 1 /\ size heights = h + 1 
 /\ (forall k, (0<=k<5 \/ k=7) => address.[k] = (set_type zero_address 2).[k])
 /\   0 <= i < 2 ^ t /\ t = _sth /\ s = _lstart 
 /\ (let stacklist = 
      stack_increment _lstart i _sth _ss _ps _ad (to_uint offset) in
        to_uint offset = size stacklist
      /\ forall (k : int), 0 <= k < size stacklist =>
          bs2block (nth witness stack k) = (nth witness stacklist k).`1 /\
          to_uint (nth witness heights k) = (nth witness stacklist k).`2)); last first.
+ auto => /> &2 ??????????Ho Hs?Hn. 
  have -> /= : offset{2} + W64.one - W64.one = offset{2} by ring.
  rewrite /= !W64.to_uintD_small /=. 
  +  rewrite Ho sfl_size;   smt(size_lpathst count_size BS2Int.size_int2bs h_max).
split. 
(* initialization of inner loop invariant *)
+ rewrite /stack_increment /=.
  pose _olds := (stack_from_leaf _lstart i{2} _sth _ss _ps _ad).
  pose _hw1 := (hw (lpathst _lstart (i{2} + 1) _sth)).
  pose _hw := (hw (lpathst _lstart i{2} _sth)).
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
  by move => ?;rewrite  size_cat /= size_take; smt(W64.to_uint_cmp). 
+ move => k kbl kbh.
  case (_hw < _hw1) => /= Hw.
  + (* hw increased by 1, so we have to show that the previous stack plus
         the new leaf is really the stack that we will end up with *)
      rewrite !nth_put;1,2:by rewrite Ho sfl_size; smt(size_lpathst size_ge0 size_rev count_size BS2Int.size_int2bs).
      rewrite nth_cat. 
      case(to_uint offset{2} = k) => Hk.
      + (* this is the leaf just added *)
        rewrite ifF 1:/# ifT 1:/# /= Hn /node_from_path /= ifT;1:smt(size_lpath).
        rewrite revK BS2Int.int2bsK /#.
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
       rewrite !nth_put;smt(size_lpathst size_ge0 size_rev count_size BS2Int.size_int2bs sfl_size).
      rewrite ifT;1: smt(sfl_size size_cat).
      rewrite ifT;1: smt(sfl_size size_cat).
      have -> /= : k = to_uint offset{2}  by smt(sfl_size).
      rewrite !nth_put /=;1,2: by rewrite Ho sfl_size 1:/# /hw /lpath; smt(size_lpathst size_ge0 size_rev count_size BS2Int.size_int2bs).
      rewrite take_oversize; 1: smt(size_lpath).
      rewrite /node_from_path ifT;1: smt(size_lpath).
      rewrite Hn;congr.
      by rewrite /lpath revK /= BS2Int.int2bsK /#.

move => ad hs o s.
+ rewrite uleE /= => Hout. 
  have Hout' : to_uint o < 2 \/ (2 <= to_uint o /\ nth witness hs (to_uint o - 1) <> nth witness hs (to_uint o - 2)).
  + case (to_uint o < 2) => /= *; 1: by smt(). 
    move : Hout;rewrite !to_uintB /=;1,2: by rewrite uleE /= /#. 
    by smt().
 
  move => ???? Ha2 Ho2  H5.
  rewrite /stack_increment /=.
  pose _hw1 := (hw (lpathst _lstart (i{2} + 1) _sth)).
  pose _hw := (hw (lpathst _lstart (i{2}) _sth)).
do split.
  + by smt(size_rcons).
  + by smt().
  + move => k kbl kbh; rewrite Ha2 1:/#.
    rewrite /set_type /zero_address. 
    by rewrite !get_setE 1..5:/#; smt(Array8.initiE).
  + case (_hw < _hw1) => *;1: by smt(sfl_size).
    have /= := hwdec_exit _lstart i{2} _sth _ss _ps _ad (to_uint o) _ _ _ _;1..4:smt().
    + have ->  :size (stack_increment _lstart i{2} _sth _ss _ps _ad (to_uint o)) = to_uint o by smt().
      move : Hout'. 
      case (to_uint o < 2) => /=*;1:  smt(sfl_size size_lpathst size_ge0 size_rev count_size BS2Int.size_int2bs).
   by smt(W32.to_uint_eq sfl_size W64.to_uint_cmp sfl_size hwinc).
   
  + case (_hw < _hw1) => ? k *.
    + case (k < _hw) => *. 
      + have ? := hwinc_pathsprev _lstart i{2} _sth k _ _ _ _ _ _;1..6: smt().
        have ? := hwinc_leaflast  _lstart i{2} _sth _ _ _ _ _;1..5: smt(). 
        by rewrite -!stack_final;smt().
      by rewrite !H5;smt(W32.to_uint_eq sfl_size W64.to_uint_cmp stack_final).
  + have /= := hwdec_exit  _lstart i{2} _sth _ss _ps _ad (to_uint o) _ _ _ _ _ _ _;1..6:smt(). 
    + have ->  :size (stack_increment  _lstart i{2} _sth _ss _ps _ad (to_uint o)) = to_uint o by smt().
      move : Hout'.
      case (to_uint o < 2)  => /=*;1:smt().
      by rewrite -!H5; smt(W32.to_uint_eq sfl_size W64.to_uint_cmp stack_final).
     move => *.
     rewrite !H5;1,2: smt(W32.to_uint_eq sfl_size W64.to_uint_cmp stack_final).
      by smt(W32.to_uint_eq sfl_size W64.to_uint_cmp stack_final).

seq 3  :
  (#pre 
  /\ address = set_tree_index 
      (set_tree_height (set_type zero_address 2) (to_uint (nth witness heights (to_uint offset - 1)))) 
        ((_lstart + i) %/ 2^(to_uint (nth witness heights (to_uint offset - 2)) + 1))).
+ auto => /> &hr ?????????????Ho Hs; rewrite uleE /= => H.
  rewrite !to_uintB /=;1,2: by rewrite uleE /=; smt(). 
  move => H1;rewrite H1.
  move : (Hs (to_uint offset{hr} - 1) _);1: smt(sfl_size).
  move : (Hs (to_uint offset{hr} - 2) _);1: smt(sfl_size).
  move => [# Hs21 Hs22] [# Hs11 Hs12].

have ? :  hw (lpathst _lstart (i{hr} + 1) _sth) <= hw (lpathst _lstart i{hr} _sth) by
 have /=:= hwinc_noentry _lstart i{hr} _sth _ss _ps _ad (to_uint offset{hr}) _;smt(sfl_size). 

have -> : 
     (to_uint
         (W32.of_int (_lstart + i{hr}) `>>`
          truncateu8 ((nth witness heights{hr} (to_uint offset{hr} - 2) + W32.one) `&` W32.of_int 31))) = 
     ((_lstart + i{hr})%/ 2^(to_uint (nth witness heights{hr} (to_uint offset{hr} - 2)) + 1)); last first.  
  + split;1: by move => *;rewrite /set_tree_index /set_tree_height /=; smt(Array8.get_setE).
    rewrite tP => k kb;rewrite /set_tree_index /set_tree_height /=.
    pose x:= 
       (stack_increment _lstart i{hr} _sth _ss _ps _ad (hw (lpathst _lstart i{hr} _sth) + 1 - to_uint offset{hr})).
    pose y := W32.of_int ((_lstart + i{hr})  %/ 2^(to_uint (nth witness heights{hr} (to_uint offset{hr} - 2)) + 1)).
     case (0<=k<5 \/ k= 7);1:by smt(Array8.get_setE).
     case (k=6);1:by smt(Array8.get_setE).
     move => *; have -> : k=5 by smt(). 
     rewrite !get_setE //= /#. 

  + rewrite /(`>>`) /= to_uint_truncateu8.
    have -> : 31 = 2^5 - 1 by rewrite /=.
    rewrite and_mod //= to_uintD_small /=   Hs22 /=.
    + by have := si_heights_in_loop_bnd _lstart i{hr} _sth _ss _ps _ad (to_uint offset{hr})  (to_uint offset{hr} - 2) _ _ _;smt(h_max). 
    rewrite to_uint_shr /=;1: smt(W32.to_uint_cmp).
    rewrite of_uintK  modz_small => /=;1: smt(l_max).
    rewrite of_uintK  modz_small /= 1:/#. 
    rewrite modz_small 1:/#.
    by rewrite modz_small;
     have := si_heights_in_loop_bnd _lstart i{hr} _sth _ss _ps _ad (to_uint offset{hr})  (to_uint offset{hr} - 2) _ _ _;smt(h_max).
  
seq 3 : (#pre /\ 
   node0 = nth XMSS_TreeHash.nbytes_witness stack (to_uint offset - 2)
/\  node1 = nth XMSS_TreeHash.nbytes_witness stack (to_uint offset - 1)   
/\   new_node = block2bs  (trh _ps (set_tree_index (set_tree_height (set_type zero_address 2) (to_uint (nth witness heights{hr} (to_uint offset{hr} - 1))))
  ((_lstart + i{hr}) %/ 2 ^ (to_uint (nth witness heights{hr} (to_uint offset{hr} - 2)) + 1)) ) (BytesToBits (NBytes.val node0) ++ BytesToBits (NBytes.val node1)))).
+ inline *; auto => /> &hr ???????????????; rewrite uleE /= => ?. 
   rewrite !to_uintB /=;1,2:by  rewrite ?uleE /=; smt().
   move => ?.
   rewrite /trh /thfc /= ifF. smt(@StdOrder gt0_n gt2_len).
   rewrite /block2bs DigestBlock.insubdK. 
   + rewrite /BytesToBits (size_flatten_ctt 8);1:smt(mapP W8.size_w2bits).
     rewrite size_map;1: smt(NBytes.valP).
   rewrite BytesToBitsK NBytes.valKd /rand_hash /=.
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

congr;congr;congr;1,4..:by rewrite /prf.

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

+ auto => /> &hr ?????????????Ho Hs; rewrite uleE /= => H.
  rewrite !to_uintB /=;1..2,4: by rewrite uleE /=; smt(). 
  + by rewrite uleE /= to_uintB /=; rewrite ?uleE /=; smt().
  
  move => H1;rewrite H1.
  move : (Hs (to_uint offset{hr} - 1) _);1: smt(sfl_size).
  move : (Hs (to_uint offset{hr} - 2) _);1: smt(sfl_size).
  move => [# Hs21 Hs22] [# Hs11 Hs12].

have ? :  hw (lpathst _lstart (i{hr} + 1) _sth) <= hw (lpathst _lstart i{hr} _sth) by
 have /=:= hwinc_noentry _lstart i{hr} _sth _ss _ps _ad (to_uint offset{hr}) _;smt(). 

split;1: smt().

have Hsil := si_size_in_loop _lstart i{hr} _sth _ss _ps _ad (to_uint offset{hr}) _ _ _ _ _ _ _ _; 1..8: smt(). 

  do split.
  + move => *;split;2:smt().
    rewrite Ho.
    rewrite Ho /stack_increment /= ifF 1:/# ifF 1:/# /= !size_cat /=.
    rewrite size_take;1:smt(size_ge0).
    by  smt(sfl_size size_take).
  + by smt(size_put).
  + by smt(size_put).
  + rewrite Ho /stack_increment /= ifF 1:/# /= !size_cat /=.
    rewrite size_take;1:smt(size_ge0).
    have -> /= : !(hw (lpathst _lstart i{hr} _sth) < hw (lpathst _lstart (i{hr} + 1) _sth)) by smt().
    by case (to_uint offset{hr} - 1 < size (stack_from_leaf _lstart i{hr} _sth _ss _ps _ad));rewrite size_cat /=; by  smt(sfl_size size_take).

  + move => k kbl kbh. 
    rewrite !nth_put;1,2: smt(size_lpathst count_size BS2Int.size_int2bs size_rev).
    have kbh1 : k < to_uint offset{hr} -1.
    + move : kbh;rewrite /stack_increment /= ifF 1:/# size_cat /=.
      smt(size_take sfl_size).
    case (to_uint offset{hr} - 2 = k) => Hk; last first. 
    + rewrite !Hs;1,2:smt().
      rewrite /stack_increment /= ifF 1:/#.
      have -> /= : !(hw (lpathst _lstart i{hr} _sth) < hw (lpathst _lstart (i{hr} + 1) _sth)) by smt().
      rewrite !nth_cat /= ifT;1:smt(size_take sfl_size size_ge0).
      have -> /=: !(k - size (take (to_uint offset{hr} - 2) (stack_from_leaf _lstart i{hr} _sth _ss _ps _ad)) = 0) by smt(sfl_size size_take).
      rewrite !ifT;1:smt(size_take sfl_size size_ge0).
      by rewrite !nth_take;smt(size_take sfl_size size_ge0). 
   split. 
  + rewrite /bs2block /block2bs NBytes.insubdK;1: 
      by rewrite /BitsToBytes size_map size_chunk 1:/# DigestBlock.valP /#.   
    rewrite BitsToBytesK;1: by rewrite DigestBlock.valP /=; smt().
    rewrite DigestBlock.valKd /=.
    have /= := si_reduced_node _lstart i{hr} _sth _ss _ps _ad (to_uint offset{hr}) _ _ _ _ _ _ _;1..7:smt().
    rewrite Hk => ->; congr; 1: smt(). 
    congr.
    + rewrite -Hk -Hs21 /bs2block DigestBlock.insubdK.
      + rewrite /BytesToBits (size_flatten_ctt 8);  smt(mapP W8.size_w2bits size_map NBytes.valP).
      congr; congr; rewrite (nth_change_dfl XMSS_TreeHash.nbytes_witness witness);  smt(size_lpathst count_size BS2Int.size_int2bs size_rev).
     rewrite  -Hs11 /bs2block DigestBlock.insubdK.
      + rewrite /BytesToBits (size_flatten_ctt 8);  smt(mapP W8.size_w2bits size_map NBytes.valP).
      congr; congr; rewrite (nth_change_dfl XMSS_TreeHash.nbytes_witness witness);  smt(size_lpathst count_size BS2Int.size_int2bs size_rev).
  rewrite to_uintD_small /=.
  + rewrite Hs22. 
    + have := si_heights_in_loop_bnd _lstart i{hr} _sth _ss _ps _ad (to_uint offset{hr}) (to_uint offset{hr} - 2) _ _ _ _ _ _ _ _;smt(h_max).
  rewrite Hs22.  
    rewrite /stack_increment /= ifF 1:/# nth_cat /=.
      have -> /= : !(hw (lpathst _lstart i{hr} _sth) < hw (lpathst _lstart (i{hr} + 1) _sth)) by smt().
      rewrite !nth_cat /= ifT;1:smt(size_take sfl_size size_ge0).
    rewrite ifF;1:smt(size_take sfl_size size_ge0).
    rewrite ifT;1:smt(size_take sfl_size size_ge0).
    rewrite ifF;1:smt(size_take sfl_size size_ge0).
   rewrite /node_from_path /=.    
   smt(nth_take).
qed.
*)

lemma zeroidxsE:
  adr2idxs zero_address = [0; 0; 0; 0].
proof.
rewrite /zero_address /adr2idxs.
rewrite &(eq_from_nth witness) /=; 1: smt(size_rev size_map size_sub).
move=> i ?; rewrite nth_rev 2:(nth_map witness) 3:nth_sub; 1..3:smt(size_rev size_map size_sub).
by rewrite size_map size_sub 1:// initE /= ifT; smt(size_rev size_map size_sub to_uint0).
qed.

lemma zeroadsE:
  adr2ads zero_address = HAX.Adrs.insubd [0; 0; 0; 0].
proof. by rewrite /adr2ads zeroidxsE. qed.

lemma zeroxadiP:
  valid_xadrsidxs [0; 0; 0; 0].
proof. by smt(val_w ge2_len expr_gt0). qed.

lemma zeroadiP:
  valid_adrsidxs [0; 0; 0; 0].
proof. rewrite valid_xadrsidxs_adrsidxs zeroxadiP. qed.

phoare tree_hash_correct _ps _ss _lstart _sth :
  [ TreeHash.treehash :
      arg = (_ps,_ss,_lstart,_sth, zero_address)
  /\ 0 <= _sth <= h /\ 0 <= _lstart <= 2^h - 2^_sth  /\ 2^_sth %| _lstart
 ==>
  DigestBlock.insubd (BytesToBits (NBytes.val res)) =
    val_bt_trh (list2tree (map (leafnode_from_idx _ss _ps (adr2ads zero_address))
     (range _lstart (_lstart + 2^_sth)))) _ps (set_typeidx (adr2ads zero_address) trhtype) _sth _lstart  ] = 1%r.
proof.
conseq (: _ ==> true) (: _ ==> _);1,2:smt(); last first.
+ proc.
  wp;while (true) (2^t - i).
  + move => *; wp; while (true) (to_uint offset).
    + move => *;inline *; auto => &hr;rewrite uleE /= => *.
      rewrite W64.to_uintB => /=;1: by rewrite uleE /= /#.
      by smt().
    (*
    wp;call(:true).
    wp; while (true) (Params.len - i).
    + move => *.
      wp;while (true) (Params.len %/ 2 - i).
      move => *.
      inline *;auto => /> /#.
    by auto => /> /#.
   by auto => /> /#.
   *)
  sp;wp;exlim sk_seed, pub_seed, address => ss ps ad.
  call Eqv_WOTS_pkgen_ll.
  + auto => /> &hr ? h o; rewrite uleE /=;split; smt(W64.to_uint_cmp).
  by auto => /> /#.

proc => /=.
wp;while ( #{/~address = zero_address}pre
    /\ 0 <= i <= 2^t
    /\ (forall k, 0 <= k < 3 => address.[k] = W32.zero)
    /\ address.[7] = W32.zero
    /\ size stack = h + 1 /\ size heights = h + 1
    /\ (let stacklist = stack_from_leaf _lstart i _sth _ss _ps (adr2ads zero_address) in
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
  + move => ad hs i o st 8? H.
    have steq:
      forall (tp : int), valid_typeidx tp =>
        set_typeidx (adr2ads ad) tp = set_typeidx (adr2ads zero_address) tp.
    + move=> tp valtp @/set_typeidx.
      by congr; rewrite &(eq_from_nth witness); smt(nth_put size_put HAX.Adrs.valP).
    have @/bs2block -> := (H 0 _) => /=.
    have -> : i = 2^_sth by smt().
    rewrite sfl_size 1..4:/#; have-> := lpathst_root _sth _;1:smt().
    rewrite /hw /=;smt(count_ge0).
  + rewrite /stack_from_leaf nth0_head /paths_from_leaf /= ifT 1:/# /= cats0 /=.
    rewrite /node_from_path.
    case (_sth = h) => Ht.
    +  rewrite /prefix ifF;1:by smt(size_lpath StdOrder.IntOrder.expr_gt0 h_g0 take0).
       rewrite ifT /=;1: by smt(size_lpath StdOrder.IntOrder.expr_gt0 h_g0 take0).
       congr; 2,-2: by smt(take_size size_take size_ge0 size_lpath StdOrder.IntOrder.expr_gt0).
       congr;congr; smt(lfp_st).
       rewrite lfp_st /range iotaS_minus;smt(StdOrder.IntOrder.expr_gt0).
    case (_sth = 0) => H0.
    +  rewrite /prefix ifT;1:smt(take_size size_take size_ge0 size_lpath StdOrder.IntOrder.expr_gt0 h_g0).
       have -> /= : (range _lstart (_lstart + 2 ^ _sth)) = [_lstart] by rewrite H0 /= rangeS.
        rewrite H0 list2tree1 /=.
        suff /#: BS2Int.bs2int (rev (take (size (lpath _lstart)) (lpath _lstart))) = _lstart.
        rewrite take_size /lpath revK BS2Int.int2bsK;smt(h_g0 StdOrder.IntOrder.expr_gt0).
    rewrite /prefix ifF;1:by smt(take_size size_take size_ge0 size_lpath StdOrder.IntOrder.expr_gt0 h_g0).
    rewrite ifT /=;1:by smt(take_size size_take size_ge0 size_lpath StdOrder.IntOrder.expr_gt0 h_g0).
    congr; 2,-2: by smt(take_size size_take size_ge0 size_lpath StdOrder.IntOrder.expr_gt0).
    congr;congr; smt(lfp_st).
    by rewrite lfp_st /range iotaS_minus;smt(StdOrder.IntOrder.expr_gt0).

seq 6 : (#pre /\
   bs2block node = leafnode_from_idx _ss _ps (adr2ads zero_address) (_lstart + i)).
+ seq 3 : (#pre /\   pk = LenNBytes.insubd
  (map NBytes.insubd
     (chunk n
        (BitsToBytes
           (flatten (map DigestBlock.val (DBLL.val (wots_pk_val _ss _ps (set_kpidx (set_typeidx (adr2ads zero_address) 0) (_lstart + i)) (_lstart + i))))))))).
  + conseq />;1: smt().
    ecall (Eqv_WOTS_pkgen (adr2ads address) sk_seed pub_seed).
    auto => /> &1 &2 ?????????????; split.
    rewrite adr2adsK 3://.
    + by move => ii valii; smt(get_setE).
    rewrite /valid_adrsidxs; split; 1: smt(size_rev size_map size_sub).
    rewrite /valid_xidxvalslp /valid_xidxvalslpch; left.
    rewrite ?nth_rev ?(nth_map witness); 1..12: smt(size_map size_sub).
    rewrite /= /set_ots_addr /set_type ?size_map ?nth_iota ?size_iota 1..4:// /=.
    rewrite ?get_setE // (: max 0 4 = 4) 1:// /= to_uintK_small; smt(l_max val_w ge2_len).
    move => ?; split => [k ? ?|]; 1: by rewrite /set_ots_addr /set_type ?get_setE // /#.
    congr;congr;congr;congr;congr;congr;congr.
    + rewrite /wots_pk_val.
      suff /#:
        adr2ads (set_ots_addr (set_type address{1} 0) (_lstart + i{1})) =
        set_kpidx (set_typeidx (adr2ads zero_address) 0) (_lstart + i{1}).
      + rewrite zeroadsE /set_typeidx /set_kpidx HAX.Adrs.insubdK 1:zeroadiP /set_idx.
        rewrite /put /= ifT 2:HAX.Adrs.insubdK 2:zeroadiP /=; 1: smt(HAX.Adrs.valP).
        rewrite /adr2ads /adr2idxs; congr; apply (eq_from_nth witness); 1: smt(size_put size_rev size_map size_sub).
        move=> ii rngi.
        rewrite nth_rev 2:(nth_map witness) 3:nth_sub 4:?nth_put //; 1..3: smt(size_put size_rev size_map size_sub).
        rewrite size_map size_sub 1:// /set_ots_addr /set_type ?get_setE 1..6://.
        rewrite (: 3 + (4 - (ii + 1)) = 6 - ii) 1:/#.
        case (ii <> 2) => /= [| -> /=].
        smt(get_setE W32.to_uint0 size_rev size_map size_sub).
        by rewrite to_uintK_small; smt(l_max).
  (* ecall (ltree_eq pub_seed address  pk ). *)
  auto => /> &1 &2 ???????????H?; do split.
  + move=> k gek ltk.
    by rewrite /set_ltree_addr /set_type; do ? rewrite get_setE 1:// ifF 1:/# => /#.
  rewrite /leafnode_from_idx.
  suff /#:
    ads2adr (set_kpidx (set_typeidx (adr2ads zero_address) 1) (_lstart + i{1}))
    =
    set_ltree_addr (set_type address{1} 1) (_lstart + i{1}).
  + rewrite zeroadsE /set_typeidx /set_kpidx HAX.Adrs.insubdK 1:zeroadiP /set_idx.
    rewrite /put /= ifT 2:HAX.Adrs.insubdK /=; 1,2: smt(HAX.Adrs.valP).
    rewrite /ads2adr /idxs2adr HAX.Adrs.insubdK 1:/#.
    rewrite tP => ii rngii; rewrite initE rngii /=.
    rewrite /set_ltree_addr /set_type.
    rewrite ?get_setE // /#.
(*
  move=> k ge0_k ltszk.
  move: (H k _); 1: smt(sfl_size).
  move => ^ + -> => ->; split; do 2! congr.
  rewrite /stack_from_leaf.
  rewrite /node_from_path.
  congr. rewrite fun_ext => p.
  suff /#:
    leafnode_from_idx _ss _ps (adr2ads address{1}) (BS2Int.bs2int (rev (prefix (lpath _lstart) _sth ++ p)))
    =
    leafnode_from_idx _ss _ps (adr2ads (set_ltree_addr (set_type address{1} 1) (_lstart + i{1})))
          (BS2Int.bs2int (rev (prefix (lpath _lstart) _sth ++ p)))
    /\
    (let ls = leaves_from_path (prefix (lpath _lstart) _sth ++ p) in
     let nls = map (leafnode_from_idx _ss _ps (adr2ads address{1})) ls in
     let subtree = list2tree nls in
     val_bt_trh subtree _ps (set_typeidx (adr2ads address{1}) trhtype) (h - size (prefix (lpath _lstart) _sth ++ p)) (head witness ls))
    =
    (let ls = leaves_from_path (prefix (lpath _lstart) _sth ++ p) in
     let nls = map (leafnode_from_idx _ss _ps (adr2ads (set_ltree_addr (set_type address{1} 1) (_lstart + i{1})))) ls
     in
     let subtree = list2tree nls in
     val_bt_trh subtree _ps (set_typeidx (adr2ads (set_ltree_addr (set_type address{1} 1) (_lstart + i{1}))) trhtype)
       (h - size (prefix (lpath _lstart) _sth ++ p)) (head witness ls)).
  admit. (* true: operators simply reset addresses *)
  rewrite /stack_from_leaf.
  rewrite /node_from_path.
  congr. rewrite fun_ext => p.
  suff /#:
    leafnode_from_idx _ss _ps (adr2ads address{1}) (BS2Int.bs2int (rev (prefix (lpath _lstart) _sth ++ p)))
    =
    leafnode_from_idx _ss _ps (adr2ads (set_ltree_addr (set_type address{1} 1) (_lstart + i{1})))
          (BS2Int.bs2int (rev (prefix (lpath _lstart) _sth ++ p)))
    /\
    (let ls = leaves_from_path (prefix (lpath _lstart) _sth ++ p) in
     let nls = map (leafnode_from_idx _ss _ps (adr2ads address{1})) ls in
     let subtree = list2tree nls in
     val_bt_trh subtree _ps (set_typeidx (adr2ads address{1}) trhtype) (h - size (prefix (lpath _lstart) _sth ++ p)) (head witness ls))
    =
    (let ls = leaves_from_path (prefix (lpath _lstart) _sth ++ p) in
     let nls = map (leafnode_from_idx _ss _ps (adr2ads (set_ltree_addr (set_type address{1} 1) (_lstart + i{1})))) ls
     in
     let subtree = list2tree nls in
     val_bt_trh subtree _ps (set_typeidx (adr2ads (set_ltree_addr (set_type address{1} 1) (_lstart + i{1}))) trhtype)
       (h - size (prefix (lpath _lstart) _sth ++ p)) (head witness ls)).
  admit. (* true: operators simply reset addresses *)
  rewrite /leafnode_from_idx /= /bs2block;congr;congr;congr;congr.
  +  admit.  (* address semantics *)
*)
wp.
while (
 pub_seed = _ps /\
     sk_seed = _ss /\
     s = _lstart /\
     t = _sth /\ 0 <= _sth /\ _sth <= h /\ 0 <= _lstart /\ _lstart <= 2 ^ h - 2 ^ _sth /\ 2 ^ _sth %| _lstart /\
    0 <= i <= 2 ^ t
 /\   (hw (lpathst i _sth) < hw (lpathst (i + 1) _sth) => to_uint offset = hw (lpathst (i + 1) _sth))
 /\ (hw (lpathst (i + 1) _sth) <= hw (lpathst i _sth) =>
         hw (lpathst (i + 1) _sth) <= to_uint offset <= hw (lpathst i _sth) + 1)
 /\size stack = h + 1 /\ size heights = h + 1
 /\ (forall k, (0<=k<5 \/ k=7) => address.[k] = (set_type zero_address 2).[k])
 /\   0 <= i < 2 ^ t /\ t = _sth /\ s = _lstart
 /\ (let stacklist =
      stack_increment _lstart i _sth _ss _ps (adr2ads zero_address) (to_uint offset) in
        to_uint offset = size stacklist
      /\ forall (k : int), 0 <= k < size stacklist =>
          bs2block (nth witness stack k) = (nth witness stacklist k).`1 /\
          to_uint (nth witness heights k) = (nth witness stacklist k).`2)); last first.
+ auto => /> &2 ???????????Ho Hs?Hn.
  have -> /= : offset{2} + W64.one - W64.one = offset{2} by ring.
  rewrite /= !W64.to_uintD_small /=.
  +  rewrite Ho sfl_size;   smt(size_lpathst count_size BS2Int.size_int2bs h_max).
split.
(* initialization of inner loop invariant *)
+ rewrite /stack_increment /=.
  pose _olds := (stack_from_leaf _lstart i{2} _sth _ss _ps (adr2ads zero_address)).
  pose _hw1 := (hw (lpathst (i{2} + 1) _sth)).
  pose _hw := (hw (lpathst i{2} _sth)).
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
  + rewrite size_cat; smt(hwinc sfl_size).
  by move => ?;rewrite  size_cat /= size_take; smt(W64.to_uint_cmp sfl_size).
+ move => k kbl kbh.
  case (_hw < _hw1) => /= Hw.
  + (* hw increased by 1, so we have to show that the previous stack plus
         the new leaf is really the stack that we will end up with *)
      rewrite !nth_put;1,2:by rewrite Ho sfl_size; smt(size_lpathst size_ge0 size_rev count_size BS2Int.size_int2bs).
      rewrite nth_cat.
      case(to_uint offset{2} = k) => Hk.
      + (* this is the leaf just added *)
        rewrite ifF 2:ifT /=; 1,2: smt(sfl_size).
        rewrite Hn /node_from_path /= ifT;1:smt(size_lpath).
        rewrite revK BS2Int.int2bsK 1,2:/# //.
      + (* this is the previous stack *)
        rewrite ifT;1:smt(sfl_size size_cat).
        move : (Hs k _);1:  smt(sfl_size size_cat).
        move => [-> ->].
          by rewrite /stack_from_leaf !(nth_map witness) /=; 1,2:smt(sfl_size pfl_size size_cat).
    + (* reductions will be needed, but we haven't started
         so we have the old stack in the first positions and a
         new leaf at the next position *)
      move : kbh; rewrite Hw /= !size_cat size_take;1:smt(W64.to_uint_cmp). 
      rewrite ifF /=;1: smt(sfl_size).
      move => kbh;rewrite !nth_cat /=.
      rewrite take_oversize /_olds Ho; 1: smt(sfl_size).
      case (k < size _olds) => *.
      + rewrite !nth_put; 1,2: smt(size_lpathst size_ge0 size_rev count_size BS2Int.size_int2bs sfl_size).
      rewrite ifF. smt(sfl_size size_ge0).
      rewrite ifT. smt(sfl_size size_ge0).
      rewrite ifF. smt(sfl_size size_ge0).
      smt().
      rewrite ifF. smt(size_lpath sfl_size size_ge0).
      rewrite ifT. smt(size_lpath sfl_size size_ge0).
      rewrite ifT. smt(size_lpath sfl_size size_ge0).
      rewrite !nth_put; 1,2: rewrite sfl_size 1:/# /hw /lpath //; 1,2: smt(size_lpathst size_ge0 size_rev count_size BS2Int.size_int2bs).
      (* rewrite !nth_put; 1,2: rewrite sfl_size 1:/# /hw /lpath //; 1,2,3,4: smt(size_lpathst size_ge0 size_rev count_size BS2Int.size_int2bs). *)
      rewrite take_oversize; 1: smt(size_lpath).
      rewrite /node_from_path ifT;1: smt(size_lpath sfl_size).
      rewrite Hn.
      rewrite ifT. smt(size_lpath sfl_size size_ge0).
      rewrite ifT. smt(size_lpath sfl_size size_ge0).
      by rewrite /lpath revK /= BS2Int.int2bsK 1,2:/#.

move => ad hs o s.
+ rewrite uleE /= => Hout.
  have Hout' : to_uint o < 2 \/ (2 <= to_uint o /\ nth witness hs (to_uint o - 1) <> nth witness hs (to_uint o - 2)).
  + case (to_uint o < 2) => /= *; 1: by smt().
    move : Hout;rewrite !to_uintB /=;1,2: by rewrite uleE /= /#.
    by smt().

  move => ???? Ha2 Ho2  H5.
  rewrite /stack_increment /=.
  pose _hw1 := (hw (lpathst (i{2} + 1) _sth)).
  pose _hw := (hw (lpathst (i{2}) _sth)).
do split.
  + by smt(size_rcons).
  + by smt().
  + move => k kbl kbh; rewrite Ha2 1:/#.
    rewrite /set_type /zero_address.
    by rewrite !get_setE 1..5:/#; smt(Array8.initiE).
  + by move: (Ha2 7 _).
  + case (_hw < _hw1) => lthw;1: by smt(sfl_size).
    have /= := hwdec_exit _lstart i{2} _sth _ss _ps (adr2ads zero_address) (to_uint o) _ _ _ _;1..4:smt().
    + have ->  :size (stack_increment _lstart i{2} _sth _ss _ps (adr2ads zero_address) (to_uint o)) = to_uint o by smt().
      move : Hout'.
      case (to_uint o < 2) => /= [|_ [ge neq]];1: smt(sfl_size size_lpathst size_ge0 size_rev count_size BS2Int.size_int2bs).
      by smt(W32.to_uint_eq sfl_size W64.to_uint_cmp sfl_size hwinc).

  + case (_hw < _hw1) => ? k *.
    + case (k < _hw) => *. 
      + have ? := hwinc_pathsprev i{2} _sth k _ _ _ _;1..4: smt().
        have ? := hwinc_leaflast i{2} _sth _ _ _;1..3: smt(). 
        by rewrite -!stack_final;smt().
      by rewrite !H5;smt(W32.to_uint_eq sfl_size W64.to_uint_cmp stack_final).
  + have /= := hwdec_exit  _lstart i{2} _sth _ss _ps (adr2ads zero_address) (to_uint o) _ _ _ _ _ _ _;1..6:smt(). 
    + have ->  :size (stack_increment  _lstart i{2} _sth _ss _ps (adr2ads zero_address) (to_uint o)) = to_uint o by smt().
      move : Hout'.
      case (to_uint o < 2)  => /=*;1:smt().
      by rewrite -!H5; smt(W32.to_uint_eq sfl_size W64.to_uint_cmp stack_final).
     move => *.
     rewrite !H5;1,2: smt(W32.to_uint_eq sfl_size W64.to_uint_cmp stack_final).
      by smt(W32.to_uint_eq sfl_size W64.to_uint_cmp stack_final).

seq 3  :
  (#pre
  /\ address = set_tree_index
      (set_tree_height (set_type zero_address 2) (to_uint (nth witness heights (to_uint offset - 1)))) 
        ((_lstart + i) %/ 2^(to_uint (nth witness heights (to_uint offset - 2)) + 1))).
+ auto => /> &hr ?????????????Ho Hs; rewrite uleE /= => H.
  rewrite !to_uintB /=;1,2: by rewrite uleE /=; smt().
  move => H1;rewrite H1.
  move : (Hs (to_uint offset{hr} - 1) _);1: smt(sfl_size).
  move : (Hs (to_uint offset{hr} - 2) _);1: smt(sfl_size).
  move => [# Hs21 Hs22] [# Hs11 Hs12].

have ? :  hw (lpathst (i{hr} + 1) _sth) <= hw (lpathst i{hr} _sth) by
  have /= := hwinc_noentry _lstart i{hr} _sth _ss _ps (adr2ads zero_address) (to_uint offset{hr}) _; smt(sfl_size).

have -> :
     (to_uint
         (W32.of_int (_lstart + i{hr}) `>>`
          truncateu8 ((nth witness heights{hr} (to_uint offset{hr} - 2) + W32.one) `&` W32.of_int 31))) =
     ((_lstart + i{hr})%/ 2^(to_uint (nth witness heights{hr} (to_uint offset{hr} - 2)) + 1)); last first.
  + split; 1: by move => *;rewrite /set_tree_index /set_tree_height /=; smt(Array8.get_setE).
    rewrite tP => k kb;rewrite /set_tree_index /set_tree_height /=.
    pose x:=
       (stack_increment _lstart i{hr} _sth _ss _ps (adr2ads zero_address) (hw (lpathst i{hr} _sth) + 1 - to_uint offset{hr})).
    pose y := W32.of_int ((_lstart + i{hr})  %/ 2^(to_uint (nth witness heights{hr} (to_uint offset{hr} - 2)) + 1)).
     case (0<=k<5 \/ k= 7);1:by smt(Array8.get_setE).
     case (k=6);1:by smt(Array8.get_setE).
     move => *; have -> : k=5 by smt().
     rewrite !get_setE //= /#.

  + rewrite /(`>>`) /= to_uint_truncateu8.
    have -> : 31 = 2^5 - 1 by rewrite /=.
    rewrite and_mod //= to_uintD_small /=   Hs22 /=.
    + by have := si_heights_in_loop_bnd _lstart i{hr} _sth _ss _ps (adr2ads zero_address) (to_uint offset{hr})  (to_uint offset{hr} - 2) _ _ _;smt(h_max).
    rewrite to_uint_shr /=;1: smt(W32.to_uint_cmp).
    rewrite of_uintK  modz_small => /=;1: smt(l_max).
    rewrite of_uintK  modz_small /= 1:/#.
    rewrite modz_small 1:/#.
    by rewrite modz_small;
     have := si_heights_in_loop_bnd _lstart i{hr} _sth _ss _ps (adr2ads zero_address) (to_uint offset{hr})  (to_uint offset{hr} - 2) _ _ _;smt(h_max).

(*
seq 3 : (#pre
         /\ node0 = nth nbytes_witness stack (to_uint offset - 2)
         /\ node1 = nth nbytes_witness stack (to_uint offset - 1)
         /\ new_node = block2bs  (trh _ps (set_tree_index (set_tree_height (set_type zero_address 2) (to_uint (nth witness heights{hr} (to_uint offset{hr} - 1))))
                                           ((_lstart + i{hr}) %/ 2 ^ (to_uint (nth witness heights{hr} (to_uint offset{hr} - 2)) + 1)) ) (BytesToBits (NBytes.val node0) ++ BytesToBits (NBytes.val node1)))).
+ inline *; auto => /> &hr ???????????????; rewrite uleE /= => ?.
   rewrite !to_uintB /=;1,2:by  rewrite ?uleE /=; smt().
   move => ?.
   rewrite /trh /thfc /= ifF. smt(@StdOrder gt0_n gt2_len).
   rewrite /block2bs DigestBlock.insubdK. 
   + rewrite /BytesToBits (size_flatten_ctt 8);1:smt(mapP W8.size_w2bits).
     rewrite size_map;1: smt(NBytes.valP).
   rewrite BytesToBitsK NBytes.valKd /rand_hash /=.
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

congr;congr;congr;1,4..:by rewrite /prf.

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
*)
+ auto => /> &hr ?????????????Ho Hs; rewrite uleE /= => H.
  rewrite !to_uintB /=;1..2,4: by rewrite uleE /=; smt().
  + by rewrite uleE /= to_uintB /=; rewrite ?uleE /=; smt().

  move => H1;rewrite H1.
  move : (Hs (to_uint offset{hr} - 1) _);1: smt(sfl_size).
  move : (Hs (to_uint offset{hr} - 2) _);1: smt(sfl_size).
  move => [# Hs21 Hs22] [# Hs11 Hs12].

have ? :  hw (lpathst (i{hr} + 1) _sth) <= hw (lpathst i{hr} _sth) by
  have /= := hwinc_noentry _lstart i{hr} _sth _ss _ps (adr2ads zero_address) (to_uint offset{hr}) _; by smt(sfl_size).

(*
have ? :  hw (lpathst _lstart (i{hr} + 1) _sth) <= hw (lpathst _lstart i{hr} _sth) by
 have /=:= hwinc_noentry _lstart i{hr} _sth _ss _ps _ad (to_uint offset{hr}) _;smt().
*)
split;1: smt().

have Hsil := si_size_in_loop _lstart i{hr} _sth _ss _ps (adr2ads zero_address) (to_uint offset{hr}) _ _ _ _ _ _ _ _; 1..8: smt().

  do split.
  + move => *;split;2:smt().
    rewrite Ho.
    rewrite Ho /stack_increment /= ifF 1:/# ifF 1:/# /= !size_cat /=.
    rewrite size_take;1:smt(size_ge0).
    by  smt(sfl_size size_take).
  + by smt(size_put).
  + by smt(size_put).
  + rewrite Ho /stack_increment /= ifF 1:/# /= !size_cat /=.
    rewrite size_take;1:smt(size_ge0).
    have -> /= : !(hw (lpathst i{hr} _sth) < hw (lpathst (i{hr} + 1) _sth)) by smt().
    by case (to_uint offset{hr} - 1 < size (stack_from_leaf _lstart i{hr} _sth _ss _ps (adr2ads zero_address)));rewrite size_cat /=; by  smt(sfl_size size_take).

  + move => k kbl kbh.
    rewrite !nth_put;1,2: smt(size_lpathst count_size BS2Int.size_int2bs size_rev).
    have kbh1 : k < to_uint offset{hr} -1.
    + move : kbh;rewrite /stack_increment /= ifF 1:/# size_cat /=.
      smt(size_take sfl_size).
    case (to_uint offset{hr} - 2 = k) => Hk; last first.
    + rewrite !Hs; 1,2: smt().
      rewrite /stack_increment /= ifF 1:/#.
      have -> /= : !(hw (lpathst i{hr} _sth) < hw (lpathst (i{hr} + 1) _sth)) by smt().
      rewrite !nth_cat /= ifT;1:smt(size_take sfl_size size_ge0).
      have  /=: !(k - size (take (to_uint offset{hr} - 2) (stack_from_leaf _lstart i{hr} _sth _ss _ps (adr2ads zero_address))) = 0) by smt(sfl_size size_take).
      rewrite !ifT;1:smt(size_take sfl_size size_ge0).
      by rewrite !nth_take;smt(size_take sfl_size size_ge0).
   split.
  + (*rewrite /bs2block /block2bs. NBytes.insubdK;1: 
      by rewrite /BitsToBytes size_map size_chunk 1:/# DigestBlock.valP /#. 
    rewrite BitsToBytesK;1: by rewrite DigestBlock.valP /=; smt().
    rewrite DigestBlock.valKd /=.*)
    have /= := si_reduced_node _lstart i{hr} _sth _ss _ps (adr2ads zero_address) (to_uint offset{hr}) _ _ _ _ _ _ _;1..7:smt().

    rewrite Hk => -> @/trh /=.
    rewrite ifF; 1: smt(ge1_n).
    rewrite /bs2block. do 4! congr.
    rewrite -Hs12 H1 Hk.
    rewrite zeroadsE /set_typeidx (HAX.Adrs.insubdK _ zeroadiP) /put /=.
    rewrite /set_thtbidx (HAX.Adrs.insubdK [0; 0; 0; trhtype]) 1:/#.
    rewrite /put /= HAX.Adrs.insubdK /valid_adrsidxs /= /valid_xidxvalslp /valid_xidxvalslptrh /=.
    right; right. rewrite /valid_tbidx /valid_thidx /nr_nodes.
    rewrite divz_ge0 1:expr_gt0 1:// /trhtype /=.
    have ? : 0 <= to_uint (nth witness heights{hr} k) < h by 
      smt(si_heights_in_loop_bnd).

    split; 2:smt().
    split; 1: smt().
    + move => *.
      (* apply (ler_lt_trans (2^h %/ 2 ^ (to_uint (nth witness heights{hr} k) + 1))); 1:  by  apply leq_div2r; 1,2:smt(expr_ge0). *)
      apply (ltr_le_trans (2^h %/ 2 ^ (to_uint (nth witness heights{hr} k) + 1))).
      rewrite ltz_divLR 1:expr_gt0 1:// divzK 1:dvdz_exp2l /#.
      by rewrite -exprD_subz /#.
    rewrite /idxs2adr /set_tree_index /set_tree_height /set_type.
    rewrite tP => ii rngi.
    rewrite /get_tree_height ?initE /= ?to_uintK_small.
    + rewrite -Hk Hs22.
      + have := si_heights_in_loop_bnd _lstart i{hr} _sth _ss _ps (adr2ads zero_address) (to_uint offset{hr}) (to_uint offset{hr} - 2) _ _ _ _ _ _ _ _;smt(h_max).
    rewrite ?get_setE 1..8://.
    case (ii = 0) => [-> //|].
    case (ii = 1) => [-> //|].
    case (ii = 2) => [-> //|].
    case (ii = 3) => [-> //|].
    case (ii = 4) => [-> //|].
    case (ii = 5) => [-> //|].
    case (ii = 6) => [-> //|].
    case (ii = 7) => [-> //| /#].
    (*    rewrite initE rngi /= ?get_setE 1..7://.     *)
 (*    rewrite initE. *)
 (*    case (ii = 0) => [-> //|]. *)
 (*    case (ii = 1) => [-> //|]. *)
 (*    case (ii = 2) => [-> //|]. *)
 (*    case (ii = 3) => [-> //|]. *)
 (*    case (ii = 4) => [-> //|]. *)
 (*    by case (ii = 5) => [-> //| /#].	(* FIXME: WTF is my smt, why does it only solve from here? and not above as `rewrite initE /#`? *) *)
 (*    rewrite take_cat DigestBlock.valP /= take0 cats0 /=. *)
 (*    rewrite -Hk -Hs21 /bs2block DigestBlock.insubdK. *)
 (*    rewrite /BytesToBits (: n = size (map W8.w2bits (NBytes.val (nth witness stack{hr} (to_uint offset{hr} - 2))))). *)
 (*    + by rewrite size_map NBytes.valP. *)
 (*    by rewrite -size_flatten_ctt 2:// => x /mapP [xx [_ ->]]; rewrite size_w2bits. *)
 (*    rewrite BytesToBitsK NBytes.valKd. *)
 (*    + apply nth_change_dfl;split => *;1:smt(). *)
 (*      have : to_uint offset{hr} <= hw (lpathst i{hr} _sth) + 1 by smt(). *)
 (*      by smt( hw_le_size size_drop size_lpathst). *)
 (*    rewrite -Hs 1:/#. *)
 (*    rewrite drop_cat DigestBlock.valP /= drop0 -Hs 1:/# DigestBlock.insubdK. *)
 (*    + rewrite /BytesToBits (: n = size (map W8.w2bits (NBytes.val (nth witness stack{hr} (to_uint offset{hr} - 1))))). *)
 (*      + by rewrite size_map NBytes.valP. *)
 (*      by rewrite -size_flatten_ctt 2:// => x /mapP [xx [_ ->]]; rewrite size_w2bits. *)
 (*    rewrite BytesToBitsK NBytes.valKd. *)
 (*    apply nth_change_dfl;split => *;1:smt(). *)
 (*    have : to_uint offset{hr} <= hw (lpathst i{hr} _sth) + 1 by smt(). *)
 (*    by smt( hw_le_size size_drop size_lpathst). *)
 (* rewrite to_uintD_small /=. *)
 (* + rewrite Hs22. *)
 (*   + have := si_heights_in_loop_bnd _lstart i{hr} _sth _ss _ps (adr2ads zero_address) (to_uint offset{hr}) (to_uint offset{hr} - 2) _ _ _ _ _ _ _ _;smt(h_max). *)
 (*     rewrite Hs22. *)
 (*     rewrite /stack_increment /= ifF 1:/# nth_cat /=. *)
 (*     have -> /= : !(hw (lpathst i{hr} _sth) < hw (lpathst (i{hr} + 1) _sth)) by smt(). *)
 (*     rewrite !nth_cat /= ifT;1:smt(size_take sfl_size size_ge0). *)
 (*     rewrite ifF;1:smt(size_take sfl_size size_ge0). *)
 (*     rewrite ifT;1:smt(size_take sfl_size size_ge0). *)
 (*     rewrite ifF;1:smt(size_take sfl_size size_ge0). *)
 (*     rewrite /node_from_path /=. *)
 (*     smt(nth_take). *)
   rewrite take_cat DigestBlock.valP /= take0 cats0 /=.
    rewrite -Hk -Hs21 /bs2block DigestBlock.insubdK.
    rewrite /BytesToBits (: n = size (map W8.w2bits (NBytes.val (nth witness stack{hr} (to_uint offset{hr} - 2))))).
    + by rewrite size_map NBytes.valP.
    by rewrite -size_flatten_ctt 2:// => x /mapP [xx [_ ->]]; rewrite size_w2bits.
    rewrite BytesToBitsK NBytes.valKd.
    + apply nth_change_dfl;split => *;1:smt().
      have : to_uint offset{hr} <= hw (lpathst i{hr} _sth) + 1 by smt().
      by smt( hw_le_size size_drop size_lpathst).
    rewrite -Hs 1:/#.
    rewrite drop_cat DigestBlock.valP /= drop0 -Hs 1:/# DigestBlock.insubdK.
    + rewrite /BytesToBits (: n = size (map W8.w2bits (NBytes.val (nth witness stack{hr} (to_uint offset{hr} - 1))))).
      + by rewrite size_map NBytes.valP.
      by rewrite -size_flatten_ctt 2:// => x /mapP [xx [_ ->]]; rewrite size_w2bits.
    rewrite BytesToBitsK NBytes.valKd.
    apply nth_change_dfl;split => *;1:smt().
    have : to_uint offset{hr} <= hw (lpathst i{hr} _sth) + 1 by smt().
    by smt( hw_le_size size_drop size_lpathst).
 rewrite to_uintD_small /=.
 + rewrite Hs22.
   + have := si_heights_in_loop_bnd _lstart i{hr} _sth _ss _ps (adr2ads zero_address) (to_uint offset{hr}) (to_uint offset{hr} - 2) _ _ _ _ _ _ _ _;smt(h_max).
     rewrite Hs22.
     rewrite /stack_increment /= ifF 1:/# nth_cat /=.
     have -> /= : !(hw (lpathst i{hr} _sth) < hw (lpathst (i{hr} + 1) _sth)) by smt().
     rewrite !nth_cat /= ifT;1:smt(size_take sfl_size size_ge0).
     rewrite ifF;1:smt(size_take sfl_size size_ge0).
     rewrite ifT;1:smt(size_take sfl_size size_ge0).
     rewrite ifF;1:smt(size_take sfl_size size_ge0).
     rewrite /node_from_path /=.
     smt(nth_take).
qed.

op pkrel (pks : pkXMSSTWRFC) (pkr : xmss_pk) : bool =
  pks.`1 = bs2block pkr.`pk_root 
 /\ pks.`2 = pkr.`pk_pub_seed 
 /\ pkr.`pk_oid = impl_oid.

op skrel (sks : skXMSSTWRFC) (skr : xmss_sk) : bool =
     sks.`1 = skr.`sk_prf
  /\ Index.val sks.`2.`1 = to_uint skr.`idx
  /\ sks.`2.`2 = skr.`sk_seed
  /\ sks.`2.`3.`1 = bs2block skr.`sk_root
  /\ sks.`2.`3.`2 = skr.`pub_seed_sk.


module RFC_O (O : DSS_RFC.RO.POracle) = {
  proc o(xm : threen_bytes * W8.t list) : nbytes  = {
    var x : threen_bytes;
    var m : W8.t list;
    var xs : W8.t list list;
    var mk : nbytes;
    var root : dgstblock;
    var idx : index;
    var cm : dgstblock;

    (x, m) <- xm;
    xs <- chunk n (ThreeNBytesBytes.val x);

    mk <- NBytes.insubd (nth witness xs 0);
    root <- DigestBlock.insubd (BytesToBits (nth witness xs 1));
    (*
      `take h` here to make sure subtype injection is proper
      TODO: Does this cause issues with further proofs/instantiations?
    *)
    idx <- Index.insubd (BS2Int.bs2int (take h (BytesToBits (nth witness xs 2))));

    cm <@ O.o(mk, (root, idx, m));

    return NBytes.insubd (BitsToBytes (DigestBlock.val cm));
  }
}.

module WOTS_Encode = {
  proc encode(m : W8.t list) : int list = {
    var msg, csum, csum_32, len_2_bytes, csum_bytes, csum_base_w;

    (* Convert message to base w *)
    msg <@ Top.BaseW.BaseW.base_w(m, Params.len1);

    (* Compute checksum *)
    csum <@ WOTS.checksum(msg);
    csum_32 <- W32.of_int csum;

    (* Convert checksum to base w *)
    csum_32 <- csum_32 `<<` W8.of_int (8 - ((ceil (Params.len2%r * log2(Params.w%r))) %% 8));
    len_2_bytes <- (ceil ((ceil (Params.len2%r * log2(Params.w%r)))%r / 8%r));

    (* msg = msg || base_w(toByte(csum_32, len_2_bytes), w, len_2); *)
    csum_bytes <- toByte csum_32 len_2_bytes;
    csum_base_w <@ Top.BaseW.BaseW.base_w(csum_bytes, Params.len2);
    msg <- msg ++ csum_base_w;

    return msg;
  }
}.

lemma WOTSEncodeP m :
  phoare[WOTS_Encode.encode : arg = m
         ==>
         res
         =
         map BaseW.val (encode_int Params.len1 (BS2Int.bs2int (rev (BytesToBits m))) Params.len2) ]= 1%r.
admitted.


equiv kg_eq (O <: DSS_RFC.RO.POracle) :
  XMSS_TW_RFC(O).keygen ~ XMSS_RFC_Abs(RFC_O(O)).kg :
    ={arg} ==> pkrel res{1}.`1 res{2}.`2 /\ skrel res{1}.`2 res{2}.`1 /\ to_uint res{2}.`1.`idx = 0.
proof.
have ? := h_g0; have ? := expr_gt0.

proc.
inline {1} keygen.
inline{2} sample_randomness.
swap {2} [5..7] -4.
swap {2} 2 -1; seq 3 3 : (NBytes.val ss{1} = sk_seed0{2}
                          /\ NBytes.val ms{1} = sk_prf0{2}
                          /\ NBytes.val ps{1} = pub_seed0{2}).
+ do 3!(rnd NBytes.val NBytes.insubd); auto => />.
   have H := supp_dlist W8.dword n.
   have Hn:= ge1_n.
   split => *; 1: smt(NBytes.insubdK ge1_n supp_dlist).
   split => *;1: (rewrite dmapE; apply mu_eq_support => x Hx;smt(NBytes.valK)).
   split => *;1:smt(NBytes.valP supp_dmap).
   split => *;1: smt(NBytes.insubdK NBytes.valK ge1_n supp_dlist).
   smt(NBytes.valP supp_dmap).

sp;wp => /=.
conseq (: _
        ==>
        (val_bt_trh (list2tree leafl{1}) ps{1} (set_typeidx (XAddress.val adc) trhtype) h 0 =
         DigestBlock.insubd (BytesToBits (NBytes.val root{2})))).
+ auto => /> &1 *; smt(NBytes.valK Index.insubdK).
ecall {1} (leaves_correct  ps0{1} ss0{1} ad{1}) => /=.
ecall {2} (tree_hash_correct pub_seed{2} sk_seed{2} 0 h).
auto => /> &2; do split.
+ rewrite /set_layer_addr /zero_address /= tP => *;  smt(Array8.get_setE Array8.initiE).
+ smt(h_g0).

move=> ??? rr ->.
suff @/adc ->: XAddress.val (XAddress.insubd (HAX.Adrs.insubd (adr2idxs zero_address))) = adr2ads zero_address.
+ by smt(NBytes.valK).
by rewrite XAddress.insubdK /valid_xadrs; smt(HAX.Adrs.valP take_size).
qed.


(*
op skrel(ask : skXMSSTW, sk : xmss_sk) =
   ask.`1 = sk.`sk_prf /\
   Index.val ask.`2.`1 = to_uint sk.`idx /\ 0 <= Index.val ask.`2.`1 <= 2^h /\
   ask.`2.`2 = sk.`sk_seed  /\
   ask.`2.`3 = sk.`pub_seed_sk
   (* ask.`2.`4 = ??? Why is the address in/not in the sk/pk? *)
   (* ??? = sk.`pk_root Why is the root not in/in the sk? *).

op pkrel(apk : pkXMSSTW, pk : xmss_pk) =
   apk.`1 = DigestBlock.insubd (BytesToBits (NBytes.val pk.`pk_root)) /\
   apk.`2 = pk.`pk_pub_seed
   (* apk.`3 = ??? Why is the address in the sk/pk? *)
   (* ??? = pk.`pk_oid I guess abstract proofs fon't care about oid *).
*)


(*
(* FD + WR *)
equiv kg_eq : XMSS_TW(FakeRO).keygen ~ XMSS_PRF.kg :
  ={arg} ==> pkrel res{1}.`1 res{2}.`2 /\ skrel res{1}.`2 res{2}.`1.
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
+ auto => /> &1 *; smt(NBytes.valK Index.insubdK). 

ecall {1} (leaves_correct  ps0{1} ss0{1} ad{1}) => /=.
ecall {2} (tree_hash_correct pub_seed{2} sk_seed{2} 0 h address{2}).
auto => /> &1;do split. 
+ rewrite /set_layer_addr /zero_address /= tP => *;  smt(Array8.get_setE Array8.initiE).  
+ smt(h_g0).
move=> -> ?? rr ->;congr;1:smt(NBytes.valK).
rewrite /set_typeidx;congr.
apply (eq_from_nth witness);rewrite !size_put;1: smt(HAX.Adrs.valP).
by move => i ib;rewrite !(nth_put);smt(size_put HAX.Adrs.valP).
qed.
*)


(* Signature type is abused with two index copies because I need this to simulate
   the actual operation of the implementation *)

op sigrel(asig : sigXMSSTW, sig : sig_t) =
   asig.`1 = sig.`r /\
   Index.val asig.`2.`1 = to_uint sig.`sig_idx /\
   asig.`2.`2 = DBLL.insubd
     (map (fun (b : nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (LenNBytes.val sig.`r_sig.`1)) /\
   (rev (DBHL.val asig.`2.`3) =
     (map (fun (b : nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (AuthPath.val sig.`r_sig.`2))).


(*
op sigrel(asig : sigXMSSTW, sig : sig_t) =
   asig.`1.`1 = sig.`r /\
   asig.`1.`2 = to_uint sig.`sig_idx /\
   Index.val asig.`2.`1 = to_uint sig.`sig_idx /\ 0 <= Index.val asig.`2.`1 <= 2^h /\
   asig.`2.`2 = DBLL.insubd
     (map (fun (b : nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (LenNBytes.val sig.`r_sig.`1)) /\
   asig.`2.`3 = DBHL.insubd
     (map (fun (b : nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (AuthPath.val sig.`r_sig.`2)).
*)

(*
(* FD + WR : FIXME : THERE IS SOMETHING WRONG IN THE DEFINITION OF INSUBD FOR INDEX *)
equiv sig_eq : XMSS_TW(FakeRO).sign ~ XMSS_PRF.sign : skrel sk{1} sk{2} /\ ={m} /\ Index.val sk{1}.`2.`1 < 2^h -1  ==>
   sigrel res{1}.`1 res{2}.`1 /\ skrel res{1}.`2 res{2}.`2.
proof.
proc. inline {1} 6. inline {1} 8. inline {1} 5.
swap {1} 21 -4. swap {1} [13..17] -1. swap {1} [11..16] -1. swap {1} [9..15] -6. inline {2} 7. inline {2} 16.

wp 20 25. 
sp 8 3 => /=.  
seq 1 1 : (skrel (ms{1},sk1{1}) sk{2} 
        /\ ={m} 
        /\ 0 <= Index.val idx0{1} < 2 ^ h
        /\ Index.val idx0{1} = to_uint idx{2}
        /\ sk_prf{2} = sk{2}.`Types.sk_prf 
        /\ Index.val skfl{1}.`1 = to_uint idx{2}).
+ auto => /> &1 &2 *;do split. 
  + rewrite Index.insubdK 1:/# to_uintD_small;smt(pow2_32 expr_ge0 h_max gt_exprsbde h_g0).
  + smt(Index.valP).
  + move => *;rewrite Index.insubdK /#. 
  + smt().

sp;conseq => />. 

seq 1 0 : #pre. admit.  (* we need to meta-swap this *)

seq 2 1 : (#pre /\ ap{1} =
   DBHL.insubd
     (map (fun (b : Params.nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (AuthPath.val auth0{2}))); last first.  

+ seq 0 3 : (#pre /\ sigWOTS{1} =
   DBLL.insubd
     (map (fun (b : Params.nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (LenNBytes.val sig_ots{2}))). admit.  (* we need to meta-swap this *)


   auto => /> &1 &2; rewrite /mkg => />  *; split;2:smt().
 + congr; congr.
   + by congr;rewrite /W64toBytes_ext /toByte_64 //.
   + rewrite NBytes.insubdK /toByte.
     + rewrite size_rev size_mkseq; smt(gt0_n). 
   + congr.  
     + congr => /=;congr;congr;congr. 
       + apply W32.to_uint_eq=> /=; rewrite of_uintK /=.
         by rewrite modz_small /=;smt(pow2_32 expr_ge0 h_max gt_exprsbde h_g0).

inline {2} 1. wp; conseq />.
ecall {1} (leaves_correct  ps{1} ss{1} ad{1}) => /> /=.
swap {2} [6..7] -5; seq 0 2: (#pre /\ size authentication_path{2} = h); 1: by auto => />;smt(size_nseq h_g0). 
sp 0 4.

while {2} (#pre /\ 0 <= j{2} <= h /\ forall kk, 0 <= kk < j{2} => 
        nth witness (map (fun (b : Params.nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b)))
       (AuthPath.val (AuthPath.insubd authentication_path{2}))) kk =
    nth witness (DBHL.val (cons_ap_trh
    (list2tree
       (map
          (leafnode_from_idx (NBytes.insubd (NBytes.val ss{1})) (NBytes.insubd (NBytes.val ps{1}))
             (set_layer_addr zero_address 0)) (range 0 (2 ^ h)))) idx0{1} ps{1} (
    set_typeidx ad{1} 2))) kk) (h - j{2});last first. 
+ auto => /> &1 &2 *;split;1: smt(h_g0).
  move => ap2 j2;do split;1:smt().
  move => ? <-?? H. 
  rewrite -DBHL.valKd;congr.
  apply (eq_from_nth witness);1: smt(DBHL.valP size_map AuthPath.valP).
  move => k kb.
  rewrite  (H k _);1:smt(DBHL.valP size_map AuthPath.valP).
  by smt().

move => &1 ?. 
sp;wp. 
exlim pub_seed0, sk_seed0,  (k * 2 ^ j), j,  address1 => _ps _ss _start _sth _ad. 
call (tree_hash_correct _ps _ss _start _sth _ad).
auto => /> &2 ?????????????H?;do split. 
+ smt(W32.to_uint_cmp StdOrder.IntOrder.expr_ge0).
+ move => *.
  pose xx := to_uint ((idx{2} `>>` W8.of_int _sth) `^` W32.one).
  have -> :  xx =
            if (to_uint idx{2} %/ 2^_sth) %% 2 = 0 
            then (to_uint idx{2} %/ 2^_sth) + 1  
            else (to_uint idx{2} %/ 2^_sth) - 1 by admit. (* xor 1 over integers *)
  case (to_uint idx{2} %/ 2^ _sth %% 2 = 0) => He.
  + have ? : to_uint idx{2} + 2*2^_sth < 2^h. admit. (* adding a missing bit *)
    rewrite mulrDl /= divzE.  smt(@StdOrder).
  + rewrite mulrDl /= divzE /=.  smt(@StdOrder).
  + smt(@IntDiv).
move => ???rr Hrr; do split. 
+ smt(size_put).
+ smt().
+ smt().
+ move => k *. 
  rewrite (nth_map witness) /=;1:smt(AuthPath.valP). 
  rewrite AuthPath.insubdK;1:smt(size_put).
  rewrite nth_put 1:/#. 
  case (k = _sth) => Hk.
  + rewrite Hk /= Hrr /cons_ap_trh DBHL.insubdK.
    + admit. (* properties of functional ap operators *)
    + admit. (* properties of functional ap operators *)
  + rewrite ifF 1:/# /=. 
    rewrite -H 1:/# (nth_map witness) /=;smt(AuthPath.valP AuthPath.insubdK). 
+ smt().
qed.
*)

lemma eq_len1s :
  XMSS_Security.FLXMSSTW.len1 = Params.len1.
proof.
rewrite /len1 /w.
by case: w_vals => -> /=; rewrite fromintM.
qed.


lemma eq_len2s :
  XMSS_Security.FLXMSSTW.len2 = Params.len2.
proof.
rewrite /len2 /len1 /w.
by case: w_vals => -> /=; rewrite ?fromintM.
qed.


lemma eq_lens :
  XMSS_Security.FLXMSSTW.len = Params.len.
proof. by rewrite /len eq_len1s eq_len2s. qed.

equiv sig_eq (O <: DSS_RFC.RO.POracle) _idx :
  XMSS_TW_RFC(O).sign ~ XMSS_RFC_Abs(RFC_O(O)).sign :
  ={glob O} /\ skrel sk{1} sk{2} /\ ={m} /\ to_uint sk{2}.`idx = _idx /\ _idx <= 2^h - 1  ==>
     sigrel res{1}.`1 res{2}.`1 /\ to_uint res{2}.`2.`idx = _idx+1 /\ (_idx < 2^h - 1 => skrel res{1}.`2 res{2}.`2).
proof.
proc.
inline{1} RFC.FL_XMSS_TW_RFC.sign.
inline{1} FL_XMSS_TW_ES.sign.
inline{2} treesig.
swap{1} 15 2.
swap{1} ^m0<- -1.
swap{1} ^m1<- -2.
swap{1} [^sk0<- .. ^ad<-] -3.
swap{2} [^sk0<- .. ^pub_seed<-] -2.
sp.
wp 17 20 => />;1:smt().
elim*=> skt.
seq 1 1 : (#pre /\ cm{1} = bs2block _M'{2}).
+ inline{2} *.
  wp; sp.
  call (: true).
  skip => &1 /> eqsk1 eqsk21 eqsk22 eqsk231 eqsk232.
  pose kprt := _ ++ _ ++ _; have eq3n_sz : size kprt = 3 * n.
  + by rewrite ?size_cat ?NBytes.valP /#.
  rewrite ?ThreeNBytesBytes.insubdK 1://.
  rewrite ?nth_mkseq 4:/=; 1..3:smt(mulzK ge1_n).
  rewrite drop0 ?take_cat ?drop_cat.
  rewrite ?size_cat ?NBytes.valP /= (: n < n + n) 2:take0 2:drop0 /=; 1:smt(ge1_n).
  rewrite cats0 ?ifF 2:(: n * 2 - (n + n) = 0) 3:drop0; 1,2: smt(ge1_n).
  rewrite ?take_cat ?NBytes.valP /= take0 cats0.
  rewrite eqsk1 eqsk21 eqsk231 /bs2block /= ?NBytes.insubdK ?NBytes.valKd /=.
  + rewrite size_rev size_mkseq; smt(ge1_n).
  move => ?;split => [| _ r *].
  + admit.
  rewrite NBytes.insubdK 1:size_map 1:size_chunk // 1:DigestBlock.valP 1:mulKz 1,2://.
  by rewrite BitsToBytesK 1:DigestBlock.valP 1:dvdz_mulr 1:dvdzz DigestBlock.valKd.
sp.
seq 2 1 : (   #pre
           /\ rev (DBHL.val ap{1})
              =
              (map (fun (b : nbytes) => bs2block b) (AuthPath.val auth0{2}))).
+ wp; ecall{1} (leaves_correct ps{1} ss{1} ad{1}).
  inline{2} buildAuthPath.
  sp 0 4; wp => /=.
  admit.
(*
  while{2} (   #pre
            /\ size authentication_path{2} = h
            /\ 0 <= j{2} <= h
            /\ (forall kk, 0 <= kk < j{2} =>
                 nth witness (DBHL.val (DBHL.insubd (map (fun (b : nbytes) => bs2block b)
                                                     (AuthPath.val (AuthPath.insubd authentication_path{2}))))) kk
                 =
                 nth witness (rev
                              (DBHL.val
                               (cons_ap_trh_gen
                                (list2tree (map (leafnode_from_idx ss{1} ps{1} (adr2ads (set_layer_addr zero_address 0))) (range 0 (2 ^ h))))
                                idx0{1} ps{1} (set_typeidx ad{1} 2)))) kk))
             (h - j{2}); last first.
  + auto => &1 &2 />.
    move=> eqsk1 eqsk21 eqsk22 eqsk231 eqsk232 lt2h1_idx.
    split; 1: smt(size_nseq h_g0).
    move=> apt jt; split; 1: smt().
    move=> 4? eqnth.
    pose rvap := rev _; have szrvap : size rvap = h by rewrite /rvap size_rev DBHL.valP.
    apply (eq_from_nth witness); 1: by rewrite size_map AuthPath.valP szrvap.
    move=> i; rewrite szrvap => rng_i.
    rewrite /rvap ?NBytes.valKd; move: (eqnth i _); 1: smt().
    rewrite (: set_layer_addr zero_address 0 = zero_address).
    + by rewrite /set_layer_addr setE /zero_address &(ext_eq) => x rngx; smt(initE).
    rewrite /RFC.skr2sko /= ?XAddress.insubdK /valid_xadrs -/(adr2ads zero_address) ?zeroadsE 2://.
    + by rewrite HAX.Adrs.insubdK 1:zeroadiP zeroxadiP.
    by move => <-; rewrite DBHL.insubdK 1:size_map 1:AuthPath.valP.
  auto.
  sp.
  exlim pub_seed0, sk_seed0, (k * 2 ^ j), j, address1 => _ps _ss _start _sth _ad.
  call (tree_hash_correct _ps _ss _start _sth).
  auto => &2 />.
  move=> eqsk1 eqsk21 eqsk22 eqsk231 eqsk232 lt2h1_i eqszhap
         ge0_j _ eqnth lth_j; split.
  + rewrite mulr_ge0 1:/to_uint 1:BS2Int.bs2int_ge0 ?expr_ge0 1:// /=.
    rewrite dvdz_mull // 1:dvdzz /=.
    admit.
  move=> 3? rr rval; split; 2: smt().
  split; 1: smt(size_put).
  split; 1: smt(size_put).
  move=> kk g0k ltj1k.
  case (kk < j{2}) => kkj.
  + rewrite -eqnth 1:/#.
    rewrite ?AuthPath.insubdK ?DBHL.insubdK ?size_map ?size_put 1..4://.
    by rewrite ?(nth_map witness) 1:size_put 1,2:/# nth_put /#.
  rewrite (: kk = j{2}) 1:/# nth_rev DBHL.valP 1:/#.
  rewrite AuthPath.insubdK 2:DBHL.insubdK 3:(nth_map witness); 1..3: smt(size_map size_put).
  rewrite nth_put 1:/# /= /bs2block rval.
  rewrite /RFC.skr2sko /= /cons_ap_trh DBHL.insubdK.
  + have sz_cnsap :
       forall ps ad i lfs bs hidx bidx, 0 <= i =>
        size lfs = 2 ^ i => size bs = i =>
          size (cons_ap_trh_gen (list2tree lfs) bs ps ad hidx bidx) = i.
    + move=> ps ad; elim/natind.
      move => t ge0t lfs bs hi bi; case (t = 0) => eqt.
      + rewrite eqt size_eq0 size_eq1 /= => -[x ->] ->.
        by rewrite list2tree1.
      smt().
    move => t ^ ge0_t -> /= ih lfs bs hi bi ge0t1 szlfs szbs.
    rewrite -(cat_take_drop (2 ^ t) lfs).
    rewrite (list2treeS t) 1:/#.
    + by rewrite size_take 1:expr_ge0 1:// ifT // szlfs exprD_nneg 1://; smt(@IntOrder).
    + by rewrite size_drop 1:expr_ge0 1:// szlfs exprD_nneg 1://; smt(@IntOrder).
    case: bs szbs. smt(size_eq0).
    move=> b bs' /= szbs'.
    move: (ih (if b then (drop (2 ^ t) lfs) else (take (2 ^ t) lfs)) bs' (hi - 1) (if b then 2 * bi + 1 else 2 * bi) _ _).
    case b => ?.
    + by rewrite size_drop 1:expr_ge0 1:// szlfs exprD_nneg 1://; smt(@IntOrder).
    + by rewrite size_take 1:expr_ge0 1:// ifT // szlfs exprD_nneg 1://; smt(@IntOrder).
    smt().
    by case b => ? -> /#.
    apply sz_cnsap. smt(ge1_h). rewrite size_map size_range. smt(expr_ge0).
    rewrite size_rev BS2Int.size_int2bs. smt(ge1_h).
  rewrite /val_bt_trh eqsk21 eqsk22 eqsk232 (: (set_layer_addr zero_address 0) = zero_address).
  + by rewrite /set_layer_addr setE /zero_address &(ext_eq) => x rngx; smt(initE).
  rewrite -/(adr2ads zero_address) /trhtype XAddress.insubdK /valid_xadrs zeroadsE.
  + by rewrite HAX.Adrs.insubdK 1:zeroadiP zeroxadiP.
  rewrite (range_cat (2 ^ (h - 1)) 0) 1:expr_ge0 1:// 1:ler_weexpn2l 1://; 1: smt(ge1_h).
  rewrite map_cat (list2treeS (h - 1)) 2,3:size_map 2,3:size_range; 1,2:smt(expr_ge0 ge1_h).
  + rewrite (: h = (h - 1 + 1)) 1:// exprD_nneg 2:// /=.
    smt(ge1_h).
    smt(ge1_h expr_ge0).
  rewrite (: h = (h - 1) + 1) 1:// 1:(BS2Int.int2bsS (h - 1)); 1:smt(ge1_h).
  rewrite rev_rcons /=; case (h - (j{2} + 1) = 0) => [eq0_h1j | neq0_h1j] /=.
  + have eqh1j : j{2} = h - 1 by smt().
    rewrite eqh1j /=.
    case (to_uint skt.`Top.XMSS_RFC_Abs.idx %/ 2 ^ (h - 1) %% 2 <> 0) => /= parity.
    + rewrite (: to_uint ((skt.`Top.XMSS_RFC_Abs.idx `>>` W8.of_int (h - 1)) `^` W32.one) = 0) 2://.
      admit.
    rewrite (: to_uint ((skt.`Top.XMSS_RFC_Abs.idx `>>` W8.of_int (h - 1)) `^` W32.one) = 1) 2:/=.
    + admit.

  case (to_uint skt.`Top.XMSS_RFC_Abs.idx %/ 2 ^ (h - 1) %% 2 <> 0) => parity.
  + rewrite (: to_uint ((skt.`Top.XMSS_RFC_Abs.idx `>>` W8.of_int (h - 1)) `^` W32.one) * 2 ^ (h - 1) = 1) 2://.
      admit.
      admit.
  admit.
*)

sp; elim*=> adt.
seq 1 1 : (   #pre
           /\ sigWOTS{1}
              =
              DBLL.insubd (map (fun (b : nbytes) => bs2block b) (LenNBytes.val sig_ots{2}))).
+ inline{1} WOTS_TW_ES.sign; inline{2} WOTS.sign_seed.
  wp.
  while (   ps0{1} = pub_seed0{2} /\ idx_new{2} = skt.`Top.XMSS_RFC_Abs.idx + W32.one 
         /\ ad0{1} = set_kpidx (XAddress.val (XAddress.insubd (HAX.Adrs.insubd (adr2idxs zero_address)))) (Index.val idx0{1})
         /\ address1{2} = set_chain_addr (set_ots_addr zero_address (to_uint idx0{2})) (if i{2} = 0 then 0 else i{2} - 1)
         /\ set_chidx ad0{1} (if size sig2{1} = 0 then 0 else size sig2{1} - 1)
            =
            adr2ads address1{2}
         /\ map BaseW.val (EmsgWOTS.val em{1}) = msg{2}
         /\ DBLL.val skWOTS0{1} = map bs2block (LenNBytes.val wots_skey{2})
         /\ (forall j, 0 <= j < size sig2{1} =>
             nth witness sig2{1} j = bs2block (nth witness sig0{2} j))
         /\ size sig2{1} = i{2}
         /\ size sig0{2} = Params.len
         /\ size sig2{1} <= XMSS_Security.FLXMSSTW.len
         /\ 0 <= i{2} <= Params.len).
  + wp.
    inline{2} chain; wp; sp => /=; elim*=> adrn.
    exlim address2{2}, t0{2} => ad2t t02t.
    while{2} ((BytesToBits (NBytes.val t0{2})
              =
              DigestBlock.val (cf _seed{2} (adr2ads ad2t) 0 chain_count{2}
                               (BytesToBits (NBytes.val t02t))))
              /\ address2{2} = set_hash_addr ad2t (if chain_count{2} = 0 then 0 else chain_count{2} - 1)
              /\ ad2t = (set_chain_addr (set_ots_addr zero_address (to_uint idx0{2})) i{2})
              /\ 0 <= chain_count{2} <= s{2}
              /\ 0 <= s{2} < Top.XMSS_Security.FLXMSSTW.w - 1
              /\ i0{2} = 0
              /\ i{2} < Params.len)
             (s{2} - chain_count{2}).
    + auto => &2 /> ih ge0_cc lts_cc *.
      do ? split; 3..:smt(w_vals).
      + rewrite /cf iteriS //=.
        move: (ih).
        move/(congr1 BitsToBytes).
        move/(congr1 NBytes.insubd).
        rewrite BytesToBitsK NBytes.valKd => ->.
        rewrite DigestBlock.valKd /cf /f /= ?DigestBlock.insubdK.
        case (chain_count{2} = 0) => [-> | neq0cc].
        + rewrite iteri0 // /BytesToBits (: n = size (map W8.w2bits (NBytes.val t02t))).
          + by rewrite size_map NBytes.valP.
          by rewrite (size_flatten_ctt 8) => // bs /mapP [x] ->; rewrite size_w2bits.
        by rewrite (: chain_count{2} = chain_count{2} - 1 + 1) 1:// iteriS 1:/# /= DigestBlock.valP.
        + pose ft :=  Top.WOTS_RFC_Abs.f _ _ _.
          rewrite /BytesToBits (: n = size (map W8.w2bits (NBytes.val ft))).
          + by rewrite size_map NBytes.valP.
          by rewrite (size_flatten_ctt 8) => // bs /mapP [x] ->; rewrite size_w2bits.
        do ? congr. admit.
      rewrite /set_hash_addr ?setE /=; congr; rewrite fun_ext => i.
      case (i = 6) => [// /#| ?].
      rewrite initE /=.
      case (0 <= i < 8) => rngi //. by rewrite ifF.
      by rewrite get_out.
    skip => &1 &2 /> *.
    do ? split.
    rewrite /cf iteri0 // DigestBlock.insubdK //.
    rewrite /BytesToBits (: n = size (map W8.w2bits (NBytes.val (nth witness (LenNBytes.val wots_skey{2}) (size sig2{1}))))).
    + by rewrite size_map NBytes.valP.
    by rewrite (size_flatten_ctt 8) => // bs /mapP [x] ->; rewrite size_w2bits.
    rewrite /set_chain_addr /set_hash_addr /set_ots_addr ?setE.
    apply ext_eq => i rngi; rewrite ?initE rngi /=.
    case (i = 6) => [// | ?].
    case (i = 5) => [// | nf /=].
    rewrite ?initE rngi /= 2?ifF // ?initE rngi /=.
    rewrite nf /= ?initE rngi /= /zero_address.
    case (i = 4) => [// | nfr /=].
    by rewrite initE rngi /=.
    rewrite (nth_map witness) 1:EmsgWOTS.valP //.
    smt(BaseW.valP).
    rewrite (nth_map witness) 1:EmsgWOTS.valP //.
    smt(BaseW.valP).
    admit.
    progress.
    smt().
    rewrite /set_chain_addr /set_hash_addr /set_ots_addr ?setE.
    apply ext_eq => i rngi; rewrite ?initE rngi /=.
    case (i = 6) => [// | ?].
    case (i = 5) => [// | nf /=]. smt(size_ge0).
    rewrite ?initE rngi /= ifF // ?initE rngi /=.
    case (i = 4) => [// | nfr /=].
    by rewrite initE rngi /=.
    rewrite size_rcons /set_chidx /set_kpidx /set_idx.
    move: zeroadsE => @/adr2ads ->.
    admit.
    rewrite nth_rcons.
    admit.
    by rewrite size_rcons.
    smt(size_put).
    by rewrite size_rcons /#.
    smt(size_ge0).
    smt(size_ge0).
    smt(size_rcons eq_lens).
    smt(size_rcons eq_lens).
  wp -1 -1.
  sp; seq 1 1 : (#pre /\ DBLL.val skWOTS0{1} = map bs2block (LenNBytes.val wots_skey{2})).
  + admit.
  outline{2} [1 .. 8] by { msg <@ WOTS_Encode.encode(M0); }.
  ecall{2} (WOTSEncodeP M0{2}).
  skip => &1 &2 />.
  progress.
  rewrite /RFC.skr2sko /= zeroidxsE XAddress.insubdK.
  + by rewrite /valid_xadrs HAX.Adrs.insubdK 1:zeroadiP zeroxadiP.
  by rewrite /set_typeidx /set_kpidx HAX.Adrs.insubdK /put /= 1:zeroadiP.
  rewrite /set_ots_addr /set_type /set_chain_addr /set_ots_addr.
  rewrite ?setE &(ext_eq) => i rngi; rewrite ?initE rngi /=.
  case (i = 6) => [// | ns].
  case (i = 5) => [// | nf /=].
  rewrite ?initE rngi /=.
  case (i = 4) => [// | nfr /=].
  case (i = 7) => [// | nfs /=].
  smt(initE). 
  rewrite /RFC.skr2sko /= zeroidxsE XAddress.insubdK.
  + by rewrite /valid_xadrs HAX.Adrs.insubdK 1:zeroadiP zeroxadiP.
  rewrite /set_typeidx /set_kpidx HAX.Adrs.insubdK /put /= 1:zeroadiP.
  rewrite /set_chidx /set_idx ?HAX.Adrs.insubdK /put /= 1,3:zeroadiP.
  rewrite /valid_adrsidxs /= /valid_xidxvalslp /valid_xidxvalslpch /=; left.
  smt(val_w ge2_len Index.valP).
  rewrite /adr2ads /set_type /set_ots_addr /adr2idxs ?setE /=; congr.
  apply (eq_from_nth witness); 1: smt(size_rev size_map size_sub).
  move=> i /= rngi.
  rewrite nth_rev. smt(size_rev size_map size_sub).
  rewrite (nth_map witness). smt(size_rev size_map size_sub).
  rewrite nth_sub. smt(size_rev size_map size_sub).
  do ? (rewrite initE /=). pose t := size _.
  smt(size_rev size_map size_sub W32.initE W32.to_uintK_small W32.to_uint0 Index.valP ge1_h).
  rewrite eq_len1s eq_len2s.
  rewrite /bs2block DigestBlock.insubdK /BytesToBits.
  rewrite (: n = size (map W8.w2bits (NBytes.val _M'{2}))) 1:size_map 1:NBytes.valP 1://.
  by rewrite (size_flatten_ctt 8) => // bs /mapP [x] ->; rewrite size_w2bits.
  rewrite -/EmsgWOTS.ofemsgWOTS EmsgWOTS.ofemsgWOTSK //.
  rewrite /encode_int size_cat /checksum /int2lbw /= ?size_mkseq.
  smt(eq_len1s eq_len2s ge1_len1 ge1_len2).
  smt().
  rewrite size_nseq. smt(ge0_len).
  smt(ge2_len).
  smt(Params.ge0_len).
  by smt(eq_lens).
  smt(ge2_len).
  rewrite LenNBytes.insubdK. smt().
  congr; apply (eq_from_nth witness).
  smt(size_map). move=> i rngi.
  by rewrite (nth_map witness); smt().
auto => &1 &2 /> ? eqv *.
do split;last first. 
+ move => *; rewrite Index.insubdK; 1:smt(Index.valP).
by rewrite /RFC.skr2sko /= eqv /= to_uintD_small; smt(pow2_32 expr_ge0 h_max gt_exprsbde h_g0).
by rewrite /RFC.skr2sko /= eqv /=; smt(pow2_32 expr_ge0 h_max gt_exprsbde h_g0).
by rewrite to_uintD_small /=;smt( l_max h_max).
qed.

(*
inline{2} WOTS.checksum.
swap {1} 22 -4.
swap {1} [14..18] -1.
swap {1} [11..16] -1.
swap {1} [9..15] -6.
inline {2} 7. inline {2} 16.

wp 20 25.
sp 8 3 => /=.
seq 1 1 : (skrel (ms{1},sk1{1}) sk{2}
        /\ ={m}
        /\ Index.val idx0{1} = to_uint idx{2}
        /\ sk_prf{2} = sk{2}.`sk_prf
        /\ Index.val skfl{1}.`1 = to_uint idx{2}).
+ auto => /> &1 &2 *;do split.
  + rewrite Index.insubdK 1:/# to_uintD_small;smt(pow2_32 expr_ge0 h_max gt_exprsbde h_g0).
  + smt(Index.valP).
  + move => *;rewrite Index.insubdK /#.
  + smt().

sp;conseq => />.

seq 1 0 : #pre. admit.  (* we need to meta-swap this *)

seq 2 1 : (#pre /\ ap{1} =
   DBHL.insubd
     (map (fun (b : Params.nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (AuthPath.val auth0{2}))); last first.  

+ seq 0 3 : (#pre /\ sigWOTS{1} =
   DBLL.insubd
     (map (fun (b : Params.nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (LenNBytes.val sig_ots{2}))). admit.  (* we need to meta-swap this *)


   auto => /> &1 &2; rewrite /mkg => />  *; split;2:smt().
 + congr; congr.
   + by congr;rewrite /W64toBytes_ext /toByte_64 //.
   + rewrite NBytes.insubdK /toByte.
     + rewrite size_rev size_mkseq; smt(gt0_n). 
   + congr.  
     + congr => /=;congr;congr;congr. 
       + apply W32.to_uint_eq=> /=; rewrite of_uintK /=.
         by rewrite modz_small /=;smt(pow2_32 expr_ge0 h_max gt_exprsbde h_g0).

inline {2} 1. wp; conseq />.
ecall {1} (leaves_correct  ps{1} ss{1} ad{1}) => /> /=.
swap {2} [6..7] -5; seq 0 2: (#pre /\ size authentication_path{2} = h); 1: by auto => />;smt(size_nseq h_g0). 
sp 0 4.

while {2} (#pre /\ 0 <= j{2} <= h /\ forall kk, 0 <= kk < j{2} => 
        nth witness (map (fun (b : Params.nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b)))
       (AuthPath.val (AuthPath.insubd authentication_path{2}))) kk =
    nth witness (DBHL.val (cons_ap_trh
    (list2tree
       (map
          (leafnode_from_idx (NBytes.insubd (NBytes.val ss{1})) (NBytes.insubd (NBytes.val ps{1}))
             (set_layer_addr zero_address 0)) (range 0 (2 ^ h)))) idx0{1} ps{1} (
    set_typeidx ad{1} 2))) kk) (h - j{2});last first. 
+ auto => /> &1 &2 *;split;1: smt(h_g0).
  move => ap2 j2;do split;1:smt().
  move => ? <-?? H. 
  rewrite -DBHL.valKd;congr.
  apply (eq_from_nth witness);1: smt(DBHL.valP size_map AuthPath.valP).
  move => k kb.
  rewrite  (H k _);1:smt(DBHL.valP size_map AuthPath.valP).
  by smt().

move => &1 ?. 
sp;wp. 
exlim pub_seed0, sk_seed0,  (k * 2 ^ j), j,  address1 => _ps _ss _start _sth _ad. 
call (tree_hash_correct _ps _ss _start _sth _ad).
auto => /> &2 ?????????????H?;do split. 
+ smt(W32.to_uint_cmp StdOrder.IntOrder.expr_ge0).
+ move => *.
  pose xx := to_uint ((idx{2} `>>` W8.of_int _sth) `^` W32.one).
  have -> :  xx =
            if (to_uint idx{2} %/ 2^_sth) %% 2 = 0 
            then (to_uint idx{2} %/ 2^_sth) + 1  
            else (to_uint idx{2} %/ 2^_sth) - 1 by admit. (* xor 1 over integers *)
  case (to_uint idx{2} %/ 2^ _sth %% 2 = 0) => He.
  + have ? : to_uint idx{2} + 2*2^_sth < 2^h. admit. (* adding a missing bit *)
    rewrite mulrDl /= divzE.  smt(@StdOrder).
  + rewrite mulrDl /= divzE /=.  smt(@StdOrder).
  + smt(@IntDiv).
move => ???rr Hrr; do split. 
+ smt(size_put).
+ smt().
+ smt().
+ move => k *. 
  rewrite (nth_map witness) /=;1:smt(AuthPath.valP). 
  rewrite AuthPath.insubdK;1:smt(size_put).
  rewrite nth_put 1:/#. 
  case (k = _sth) => Hk.
  + rewrite Hk /= Hrr /cons_ap_trh DBHL.insubdK.
    + admit. (* properties of functional ap operators *)
    + admit. (* properties of functional ap operators *)
  + rewrite ifF 1:/# /=. 
    rewrite -H 1:/# (nth_map witness) /=;smt(AuthPath.valP AuthPath.insubdK). 
+ smt().
*)

equiv ver_eq (O <: DSS_RFC.RO.POracle) :
  XMSS_TW_RFC(O).verify ~ XMSS_RFC_Abs(RFC_O(O)).verify :
    pkrel pk{1} pk{2} /\ ={m, glob O} /\ sigrel sig{1} s{2}
  ==>
    ={res}.
proof.
proc.
seq 5 9 : (   pkrel pk{1} pk{2}
           /\ to_uint idx_sig{2} < l
           /\ Index.val sigfl{1}.`1 = to_uint idx_sig{2}
           /\ (map DigestBlock.val (DBLL.val sigfl{1}.`2)) = map (BytesToBits \o NBytes.val) (LenNBytes.val sig_ots{2})
           /\ (rev (map DigestBlock.val (DBHL.val sigfl{1}.`3)) = map (BytesToBits \o NBytes.val) (AuthPath.val auth{2}))
           /\ DigestBlock.val cm{1} = BytesToBits (NBytes.val _M'{2})
           /\ address{2} = zero_address
           /\ DigestBlock.val pk{1}.`1 = BytesToBits (NBytes.val root{2})
           /\ pk{1}.`2 = _seed{2}
           /\ root{2} = pk{2}.`pk_root).
+ inline{2} 9.
  wp; call (_: true).
  auto=> &1 &2 /> eqpk1 eqpk2 eqoid eqs1 eqs21 eqs22 eqs23.
  pose kprt := _ ++ _ ++ _; have eq3n_sz : size kprt = 3 * n.
  + by rewrite ?size_cat ?NBytes.valP /#.
  rewrite ?ThreeNBytesBytes.insubdK 1://.
  rewrite ?nth_mkseq 4:/=; 1..3:smt(mulzK ge1_n).
  rewrite drop0 ?take_cat ?drop_cat.
  rewrite ?size_cat ?NBytes.valP /= (: n < n + n) 2:take0 2:drop0 /=; 1:smt(ge1_n).
  rewrite cats0 ?ifF 2:(: n * 2 - (n + n) = 0) 3:drop0; 1,2: smt(ge1_n).
  rewrite ?take_cat ?NBytes.valP /= take0 cats0 NBytes.valKd /=.
  do ? split => //.
  rewrite NBytes.insubdK 1:size_rev 1:size_mkseq; 1: smt(ge1_n).
  rewrite (take_oversize n) 1:size_rev 1:size_mkseq; 1: smt(ge1_n).
  rewrite &(Index.val_inj) Index.insubdK 1:BS2Int.bs2int_ge0 /=.
  + (*
      TODO:
      This exactly requires that the index on
      the RFC/implementation side can be injected into the
      Index subtype (without losing values)
    *)
    pose tkh := take h _; rewrite (ltr_le_trans (2 ^ (size tkh))); 1: smt(BS2Int.bs2int_le2Xs).
    + rewrite ler_weexpn2l // size_take 2:(size_flatten_ctt 8); 1: smt(ge1_h).
      + by move=> x /mapP [t] ->; rewrite size_w2bits.
      by rewrite size_map size_rev size_mkseq; smt(ge1_n ge1_h).
    rewrite eqs21; have rng_s21 : 0 <= to_uint s{2}.`sig_idx < l by smt(Index.valP).
    rewrite -(pmod_small _ l) 1:// /to_uint /l BS2Int.bs2int_mod; 1: smt(ge1_h).
    congr; rewrite &(eq_from_nth witness).
    + rewrite ?size_take /w2bits 3:size_mkseq 3:(size_flatten_ctt 8); 1,2: smt(ge1_h).
      + by move=> x /mapP [t] ->; rewrite size_w2bits.
      rewrite size_map; have len8_h : h <= 8 * n by admit. (* TODO: Axiomatize  *)
      by rewrite size_rev size_mkseq; smt(ge1_n ge1_h h_max).
    move=> i; rewrite size_take /w2bits 2:size_mkseq 2:ifT; 1,2: smt(ge1_h h_max).
    move=> rngi; rewrite ?nth_take //; 1..4: smt(ge1_h).
    rewrite /BytesToBits /toByte nth_mkseq /=; 1: smt(h_max).
    admit.
  move=> *.
  do ? split; 1: smt(Index.valP).
  + rewrite eqs22 DBLL.insubdK 1:size_map 1:LenNBytes.valP; 1: smt(eq_lens).
    rewrite -map_comp /(\o) -eq_in_map => x /=; rewrite DigestBlock.insubdK 2://.
    rewrite (size_flatten_ctt 8); 1: by move=> y /mapP [t] ->; rewrite size_w2bits.
    by rewrite size_map NBytes.valP.
  + move/(congr1 (List.map DigestBlock.val)): eqs23.
    rewrite map_rev => ->; rewrite -map_comp /(\o) -eq_in_map => x xin /=.
    rewrite DigestBlock.insubdK 2:// 1:(size_flatten_ctt 8).
    + by move=> y /mapP [t] ->; rewrite size_w2bits.
    by rewrite size_map NBytes.valP.
  + rewrite NBytes.insubdK 1:size_map 1:size_chunk // 1:DigestBlock.valP 1:mulKz //.
    by rewrite BitsToBytesK 1:DigestBlock.valP 1:dvdz_mulr 1:dvdzz.
  rewrite eqpk1 /bs2block 1:DigestBlock.insubdK 2://.
  rewrite (size_flatten_ctt 8); 1: by move=> y /mapP [t] ->; rewrite size_w2bits.
  by rewrite size_map NBytes.valP.
wp; inline{1} verify; inline{1} root_from_sigFLXMSSTW; inline{2} rootFromSig.
sp; seq 1 1 : (   #pre
               /\ map DigestBlock.val (DBLL.val pkWOTS0{1}) = map (BytesToBits \o NBytes.val) (LenNBytes.val pk_ots{2})).
+ inline{1} pkWOTS_from_sigWOTS; inline{2} pkFromSig.
  admit.
wp; sp 0 5; elim* => ad2.
exlim nodes0{2} => lf2.
while{2} (BytesToBits (NBytes.val nodes0{2})
          =
          (
           (* let app = drop (h - k{2}) (map bs2block (AuthPath.val auth0{2})) in *)
           let app = rev (take k{2} (map bs2block (AuthPath.val auth0{2}))) in
           let idp = (rev (BS2Int.int2bs k{2} (to_uint idx_sig0{2}))) in
           let lfp = bs2block lf2 in
           DigestBlock.val (val_ap_trh_gen app idp lfp _seed0{2}
                            (adr2ads (set_type zero_address 2)) k{2} (* Off by one... *)
                            (to_uint idx_sig0{2} %/ 2 ^ k{2})))
          /\ get_tree_index address0{2} = (to_uint idx_sig0{2} %/ 2 ^ k{2})
          /\ 0 <= k{2} <= h)
         (h - k{2}).
+ move => _ z.
  proc change 2 : (! odd (to_uint idx_sig0 %/ 2 ^ k)).
  + move=> &2; rewrite oddPn.
    admit.
  auto => &2 /> eqnds ad0tidx ge0k _ lthk; split => parity.
  + do ? split; 3..: smt(); last first.
    + admit.
    (* rewrite (drop_nth witness). *)
    (* + by rewrite size_map AuthPath.valP; smt(ge1_h). *)
    rewrite (take_nth witness); 1: by rewrite size_map AuthPath.valP; smt(ge1_h).
    rewrite rev_rcons BS2Int.int2bsS 1:// rev_rcons /= ifF 1:-oddPn 1://.
    (* rewrite (: (h - (k{2} + 1) + 1) = h - k{2}) 1:/# /trh /=. *)
    rewrite /trh /= ifF; 1: smt(Params.ge1_n).
    move/(congr1 BitsToBytes) /(congr1 NBytes.insubd): eqnds.
    rewrite BytesToBitsK NBytes.valKd => ->.
    move: ad0tidx; rewrite /set_tree_height /get_tree_index get_setE 1:// /=.
    move => ->; rewrite -divz_mul 1:expr_ge0 1:// -{2}(Ring.IntID.expr1 2).
    rewrite -exprD_nneg //= take_cat drop_cat ?DigestBlock.valP /= take0 drop0 cats0.
    rewrite DigestBlock.insubdK.
    + rewrite (size_flatten_ctt 8); 1: by move=> y /mapP [t] ->; rewrite size_w2bits.
      by rewrite size_map NBytes.valP.
    do 3! congr.
    + admit.
    + do ? congr.
      admit.
    admit.
  do ? split; 3..: smt(); last first.
  + admit.
  (* rewrite (drop_nth witness). *)
  (* + by rewrite size_map AuthPath.valP; smt(ge1_h). *)
  rewrite (take_nth witness); 1: by rewrite size_map AuthPath.valP; smt(ge1_h).
  rewrite rev_rcons BS2Int.int2bsS 1:// rev_rcons /= ifT 1:-oddP 1://.
  (* rewrite (: (h - (k{2} + 1) + 1) = h - k{2}) 1:/# /trh /=. *)
  rewrite /trh /= ifF; 1: smt(Params.ge1_n).
  move/(congr1 BitsToBytes) /(congr1 NBytes.insubd): eqnds.
  rewrite BytesToBitsK NBytes.valKd => ->.
  move: ad0tidx; rewrite /set_tree_height /get_tree_index get_setE 1:// /=.
  move => ->; move/oddW: (parity) => [ a ^ adf -> /=].
  rewrite mulKz //= take_cat drop_cat ?DigestBlock.valP /= take0 drop0 cats0.
  rewrite DigestBlock.insubdK.
  + rewrite (size_flatten_ctt 8); 1: by move=> y /mapP [t] ->; rewrite size_w2bits.
    by rewrite size_map NBytes.valP.
  do 3! congr.
  + admit.
  + admit.
  do ? congr.
  rewrite exprD_nneg // divz_mul 1:expr_ge0 // adf /=.
  by rewrite mulrC divzMDl.
auto => &1 &2 /> eqpk1 eqpk2 ? ltlidx eqidx eqsfl2 eqsfl3 eqcm eqpk11 eqpkots.
split.
+ split; 2: smt(ge0_h).
  rewrite BS2Int.int2bs0s take0 ?rev_nil //= /bs2block.
  rewrite DigestBlock.insubdK 2://.
  rewrite (size_flatten_ctt 8); 1: by move=> y /mapP [t] ->; rewrite size_w2bits.
  by rewrite size_map NBytes.valP.
move=> ad0r kr ndsr; split; 1: smt().
move/lezNgt => gehk + tridx + leh_kr @/RFC.pkr2pko /=.
rewrite (: kr = h) 1:/#.
rewrite (: h = size (map bs2block (AuthPath.val auth{2}))).
+ by rewrite size_map AuthPath.valP.
rewrite take_size => + _.
rewrite /pkco /= ifF 2:ifF.
smt(Params.ge1_n gt2_len @IntOrder).
smt(Params.ge1_n gt2_len ltr_pmul2l).
move/(congr1 BitsToBytes) /(congr1 NBytes.insubd).
rewrite BytesToBitsK NBytes.valKd => ->.
rewrite /val_ap_trh.
pose valap1 := val_ap_trh_gen _ _ _ _ _ _ _.
pose valap2 := val_ap_trh_gen _ _ _ _ _ _ _.
suff : valap1 = valap2.
+ move=> ->; rewrite eqpk1 eq_iff.
  split => [| <-] @/bs2block.
  + move/(congr1 block2bs) => @/block2bs.
    rewrite DigestBlock.insubdK.
    rewrite (size_flatten_ctt 8); 1: by move=> y /mapP [t] ->; rewrite size_w2bits.
    + by rewrite size_map NBytes.valP.
    by rewrite BytesToBitsK NBytes.valKd => <-.
  rewrite NBytes.insubdK 1:size_map 1:size_chunk 1:// 1:DigestBlock.valP 1:mulKz //.
  by rewrite BitsToBytesK 1:DigestBlock.valP 1:dvdz_mulr 1:dvdzz DigestBlock.valKd.
rewrite /valap1 /valap2.
congr.
+ move/(congr1 (List.map DigestBlock.insubd)): eqsfl3.
  rewrite -?map_comp /(\o) -/bs2block => <-.
  rewrite map_rev revK -map_comp /(\o).
  rewrite (eq_map _ idfun); 1: move=> x /=; 1: by rewrite DigestBlock.valKd.
  by rewrite map_id.
+ by congr; smt(size_map AuthPath.valP).
+ rewrite /bs2block; do ? congr.
  admit.
  rewrite &(LenNBytes.val_inj) &(inj_map NBytes.val NBytes.val_inj).
  move/(congr1 (List.map BitsToBytes)): (eqpkots).
  rewrite -(map_comp BitsToBytes (BytesToBits \o NBytes.val)).
  rewrite (eq_map (_ \o (_ \o NBytes.val)) NBytes.val); 1: smt(BytesToBitsK).
  move => <-; rewrite LenNBytes.insubdK 1:size_map 1:size_chunk; 1: smt(ge1_n).
  + rewrite size_map size_chunk 1:// (size_flatten_ctt (8 * n)); 1: by move=> y /mapP [t] ->; rewrite DigestBlock.valP.
    by rewrite size_map DBLL.valP mulzA ?mulKz 1://; smt(ge1_n eq_lens).
  rewrite -map_comp; pose chn := chunk _ _.
  move/iffLR: (eq_in_map (NBytes.val \o NBytes.insubd) idfun chn) => /(_ _).
  + move => x /mapP [y] @/idfun /= [/mem_iota [ge lt] ->] @/(\o); rewrite NBytes.insubdK 2://.
    rewrite size_take 2:size_drop; 1,2: smt(ge1_n).
    move: lt; rewrite size_map size_chunk 1://.
    rewrite (size_flatten_ctt (8 * n)) 2:size_map 2:DBLL.valP /=.
    + by move=> z /mapP [x' [_ ->]]; rewrite DigestBlock.valP.
    rewrite ?mulzA ?mulKz 1:// ; 1: smt(ge1_n).
    by rewrite -mulrBr; smt(ge1_n @StdOrder.IntOrder).
  move=> ->; rewrite map_id.
  rewrite /chn /BitsToBytes.
  admit.
+ rewrite zeroidxsE /set_type /set_typeidx.
  rewrite XAddress.insubdK /valid_xadrs 1:HAX.Adrs.insubdK 1:zeroadiP 1:zeroxadiP.
  rewrite HAX.Adrs.insubdK 1:zeroadiP ?setE /put /= /adr2ads /adr2idxs; congr.
  apply (eq_from_nth witness); 1: smt(size_rev size_map size_sub).
  move=> i /= rngi.
  rewrite nth_rev; 1: smt(size_rev size_map size_sub).
  rewrite (nth_map witness); 1: smt(size_rev size_map size_sub).
  rewrite nth_sub; 1: smt(size_rev size_map size_sub).
  do ? (rewrite initE /=).
  pose t := size _; have ->: t = 4 by smt(size_rev size_map size_sub).
  case (i = 0) => [-> //|].
  case (i = 1) => [-> //|].
  case (i = 2) => [-> //|].
  by case (i = 3) => [-> //| /#].  (* smt... *)
+ by rewrite size_map AuthPath.valP.
rewrite size_map AuthPath.valP.
rewrite eq_sym -divz_eq0 1:expr_gt0 1://; split => [| /#].
by rewrite /to_uint BS2Int.bs2int_ge0.
qed.
(* PY *)
(*
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
+ auto => &1 &2 /> eqpk11 eqpk12 eqsig11 eqsig12 eqsig21 ?? eqsig22 eqsig23 ltl_sig.
  do ! split.
(*   + rewrite eqsig21 Index.insubdK 2://.
    smt(W32.to_uint_cmp). *)
  + rewrite eqsig22 DBLL.insubdK.
    + admit.x
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
call{2} (_: arg = (pkots2, add02, sd02) ==> res = ltree  sd02 add02 pkots2).  print Eqv_Ltree_ltree.
by conseq ltree_ll (ltree_eq sd02 add02 pkots2).
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
*)
