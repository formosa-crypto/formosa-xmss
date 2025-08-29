require import AllCore IntDiv List Distr DList StdOrder RealExp.
require import BitEncoding.
(*---*) import BitChunking BS2Int.

from Jasmin require import JModel.
require import Array8.

require XMSS_TW Checksum.
require XMSS_RFC_Abs.
clone import XMSS_RFC_Abs as XMSSRFCAbs.
import XMSS_Params Types Address BaseW.

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

(* -- Checksum instantiation -- *)
clone import Checksum as CS with
  op w <- w

proof *.
realize gt0_w by rewrite expr_gt0.


lemma rev_flatten (s : 'a list list) :
  rev (flatten s) = flatten (rev (map rev s)).
proof.
elim: s. smt().
move => i s ih /=.
by rewrite rev_cons flatten_rcons -ih flatten_cons rev_cat.
qed.

clone import XMSS_TW as XMSS_Security with
  type mseed <- nbytes,
  type mkey <- nbytes,
  type msgXMSSTW <- msg_t,
  op MsgXMSSTW.enum <= map Msg_t.insubd
                           (flatten
                              (mkseq (fun (i : int) =>
                                        map BitsToBytes
                                            (mkseq (fun (j : int) =>
                                                    (BS2Int.int2bs (8 * i) j)) (2 ^ (8 * i)))) mmb)),
  op mkg <-
    (fun (ms : nbytes) (i : FLXMSSTW.SA.index) =>
     prf ms (NBytes.insubd (toByte (W32.of_int (FLXMSSTW.SA.Index.val i)) n))),
  op dmseed <- dmap (dlist W8.dword Params.n) NBytes.insubd,
  op MKey.enum <= map NBytes.insubd (mkseq (fun (i : int) =>
                                            BitsToBytes (BS2Int.int2bs (8 * n) i)) (2 ^ (8 * n))),
  op dmkey <- duniform MKey.enum,
  op FLXMSSTW.n <- n,
  op FLXMSSTW.log2_w <- log2_w,
  op FLXMSSTW.w <- w,
  op FLXMSSTW.len1 <- len1,
  op FLXMSSTW.len2 <- len2,
  op FLXMSSTW.len <- len,
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
  (* op FLXMSSTW.SA.WTW.encode_msgWOTS <= (fun (m : msgWOTS) => *)
  (*                                       EmsgWOTS.mkemsgWOTS (encode_int len1 *)
  (*                                                            (BS2Int.bs2int (rev (DigestBlock.val m))) len2)), *)
  op FLXMSSTW.SA.WTW.encode_msgWOTS <= (fun (m : msgWOTS) =>
                                        EmsgWOTS.mkemsgWOTS (encode_int len1
                                                             (BS2Int.bs2int (flatten (rev (chunk 8 (DigestBlock.val m))))) len2)),
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
realize FLXMSSTW.val_log2w by case: logw_vals => ->.
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
move: (checksum_prop_var len1 len2 (BS2Int.bs2int (flatten (rev (chunk 8 (DigestBlock.val m')))))
       (BS2Int.bs2int (flatten (rev (chunk 8 (DigestBlock.val m)))))).
move=> /(_ _ _ _); first 2 by smt(ge1_len1 ge1_len2).
+ rewrite -lt_fromint -RField.fromintXn 1:#smt:(ge1_len2) -rpow_int 1:#smt:(val_w).
  have <- := rpowK w%r ((w - 1) * len1)%r _ _ _; first 3 by smt(val_w ge1_len1).
  apply: rexpr_hmono_ltr; first by smt(val_w).
  split=> [|_]; first by rewrite log_ge0 #smt:(val_w ge1_len1).
  rewrite /len2; pose l1w1 := len1 * (w - 1).
  have ->: log2 l1w1%r / log2 w%r = log w%r l1w1%r; last by smt(floor_bound).
  by rewrite /log2 /log; field; first 2 by smt(ln_eq0 val_w).
have szmfl : size (flatten (rev (chunk 8 (DigestBlock.val m)))) = 8 * n.
+ rewrite (size_flatten_ctt 8); first by move => x; rewrite mem_rev; smt(in_chunk_size DigestBlock.valP).
  by rewrite size_rev size_chunk 1://; smt(DigestBlock.valP).
have szmpfl : size (flatten (rev (chunk 8 (DigestBlock.val m')))) = 8 * n.
+ rewrite (size_flatten_ctt 8); first by move => x; rewrite mem_rev; smt(in_chunk_size DigestBlock.valP).
  by rewrite size_rev size_chunk 1://; smt(DigestBlock.valP).
move=> /(_ _ _); first 2 by smt(BS2Int.bs2int_ge0 DigestBlock.valP size_rev BS2Int.bs2int_le2Xs).
move=> /contra; rewrite negb_forall=> //= /(_ _).
+ rewrite -negP=> /(congr1 (BS2Int.int2bs (8 * n))).
  rewrite -{-1}szmfl -{1}szmpfl.
  (* -{1}(DigestBlock.valP m') -{1}(DigestBlock.valP m). *)
  rewrite !BS2Int.bs2intK => /(congr1 (chunk 8)); rewrite ?flattenK //.
  + by move => x; rewrite mem_rev; smt(in_chunk_size DigestBlock.valP).
  + by move => x; rewrite mem_rev; smt(in_chunk_size DigestBlock.valP).
  move => /(congr1 rev); rewrite ?revK; move => /(congr1 flatten); rewrite ?chunkK //.
  + by rewrite DigestBlock.valP dvdz_mulr dvdzz.
  + by rewrite DigestBlock.valP dvdz_mulr dvdzz.
  move=> /(congr1 (DigestBlock.insubd)).
  by rewrite ?DigestBlock.valKd /#.
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
move => x; rewrite count_uniq_mem.
+ rewrite ?map_inj_in_uniq.
  + move => y z; rewrite -?flatten_mapP => -[i] [+ /= +] [j] [] /=.
    rewrite ?mem_iota ?mapP => /= -[ge0_i ltmmb_i] [bs +] [ge0_j ltmmb_j] [bs'].
    rewrite ?mkseqP => -[] -[k] [rngk -> ->] -[] -[l] [rngl -> ->].
    move/(congr1 Msg_t.val); rewrite ?Msg_t.insubdK 3://.
    + by rewrite /BitsToBytes 1:size_map size_chunk 1:// size_int2bs lez_maxr 1:/# mulKz.
    by rewrite /BitsToBytes 1:size_map size_chunk 1:// size_int2bs lez_maxr 1:/# mulKz.
  rewrite &(FL_XMSS_TW.SA.WTW.uniq_flatten_map_in) 3:iota_uniq.
  + rewrite -(all_nthP _ _ witness) size_map size_iota => i rngi.
    rewrite (nth_map witness) 1:size_iota 1:// /=.
    rewrite &(map_inj_in_uniq).
    + move => bs bs'; rewrite ?mkseqP => -[j] [+ +] [k] [].
      rewrite ?nth_iota 2:/=; 1:smt(ge1_mmb).
      move=> rngj -> rngk ->.
      by move/(congr1 BytesToBits); rewrite ?BitsToBytesK 1,2:size_int2bs; 1,2: smt(dvdz_mulr).
    rewrite &(map_inj_in_uniq).
    + move=> j k.
      rewrite ?mem_iota ?nth_iota 2:/=; 1:smt(ge1_mmb).
      move => [ge0_j lt28i] [ge0_k lt28i_k].
      by move/(congr1 bs2int); rewrite ?int2bsK 2,4:// 1,2:/#.
    by apply iota_uniq.
  move=> i j; rewrite ?mem_iota /= ?hasP => rngi rngj [y] -[].
  rewrite ?mapP => -[bs] + [bs']; rewrite ?mkseqP => -[] [k] [rngk ->] -> [] [l] [rngl ->].
  move/(congr1 BytesToBits); rewrite ?BitsToBytesK 1,2:size_int2bs; 1,2: smt(dvdz_mulr).
  move=> eqint2bs; have: size (int2bs (8 * j) k) = size (int2bs (8 * i) l) by smt().
  by rewrite 2!size_int2bs 2?lez_maxr 1:/# /#.
rewrite b2i_eq1 mapP; exists (Msg_t.val x).
rewrite Msg_t.valKd /= -flatten_mapP /=.
exists (size (Msg_t.val x)); split.
+ by rewrite mem_iota; smt(size_ge0 Msg_t.valP).
rewrite mapP; exists (BytesToBits (Msg_t.val x)).
rewrite BytesToBitsK /= mkseqP; exists (bs2int (BytesToBits (Msg_t.val x))).
rewrite (: (8 * size (Msg_t.val x)) = size (BytesToBits (Msg_t.val x))).
+ rewrite /BytesToBits (size_flatten_ctt 8) 2:size_map 2://.
  by move=> bs /mapP [x' ->]; rewrite size_w2bits.
by rewrite bs2intK bs2int_ge0 bs2int_le2Xs.
qed.
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
0 <= _sth =>
_sth <= h =>
0 <= _lstart =>
_lstart <= 2 ^ h - 2 ^ _sth =>
2 ^ _sth %| _lstart =>
leaves_from_path (prefix (lpath _lstart) _sth) = range _lstart (_lstart + 2 ^ _sth).
move => *.
rewrite /leaves_from_path /= ifT;1: smt(take_size size_take size_ge0 size_lpath StdOrder.IntOrder.expr_gt0). 
apply (eq_from_nth witness).
+ rewrite size_range size_mkseq;congr;smt(take_size size_take size_ge0 size_lpath StdOrder.IntOrder.expr_gt0).  
move => i. 
rewrite size_mkseq =>?.
have Hs : size (prefix (lpath _lstart) _sth) = h - _sth;1: smt(h_g0 size_lpath take_size size_take size_ge0 size_lpath StdOrder.IntOrder.expr_gt0).
rewrite nth_mkseq;1:smt().
rewrite nth_range;1:smt().
congr; rewrite Hs /=; have ->: (h - (h - _sth)) = _sth by ring.
rewrite /prefix rev_take /=;1: smt(h_g0 size_lpath take_size size_take size_ge0 size_lpath StdOrder.IntOrder.expr_gt0).
have -> : (size (lpath _lstart) - (size (lpath _lstart) - _sth)) = _sth by ring.
rewrite -BS2Int.bs2int_div 1:/# /lpath revK BS2Int.int2bsK /= /#.
qed.

op WOTS_genSK ad ss ps =
  let (a, sk) = iteri len
    (fun i ask=>
       let (ad, sk) = ask in
       let ad = set_chain_addr ad i in
       let sk_i = prf_keygen ss (ps, ad) in
       let sk = put sk i sk_i in
       (ad, sk))
    ((set_key_and_mask (set_hash_addr ad 0) 0), nseq len witness)
  in LenNBytes.insubd sk.

op WOTS_pkgen ss ps ad =
  let sk = WOTS_genSK ad ss ps in
  let (a, pk) = iteri len
    (fun i apk=>
       let (ad, pk) = apk in
       let ad = set_chain_addr ad i in
       let sk_i = nth witness (LenNBytes.val sk) i in
       let pk_i = chain sk_i 0 (w - 1) ps ad in
       let pk = put pk i pk_i in
       (ad, pk))
    (ad, nseq len witness) in
  LenNBytes.insubd pk.

(* The leaf node corresponding to a leaf path
   The semantics of this needs to be computed from wots using
   operators and then proved equivalent to the imperative code. *)
op wots_pk_val(ss ps : Params.nbytes, ad : SA.adrs, lidx : int) : len_nbytes =
   WOTS_pkgen ss ps (ads2adr ad).

op leafnode_from_idx(ss ps : Params.nbytes, ad : adrs, lidx : int) : dgstblock =
 let pk = wots_pk_val ss ps (set_kpidx (set_typeidx ad 0) lidx) lidx in
 bs2block (ltree ps (ads2adr (set_kpidx (set_typeidx ad 1) lidx)) pk).

hoare Eqv_WOTS_genSK ad ss ps:
  WOTS.pseudorandom_genSK:
    arg = (ss, ps, ad)
    ==> res = WOTS_genSK ad ss ps.
proof.
proc.
while (0 <= i <= len
    /\ sk_seed = ss
    /\ seed = ps
    /\   (address, sk)
       = iteri i
           (fun i ask=> let (ad, sk) = ask in
              let ad = set_chain_addr ad i in
              let sk_i = prf_keygen ss (ps, ad) in
              let sk = put sk i sk_i in
              (ad, sk))
           (set_key_and_mask (set_hash_addr ad 0) 0, nseq len witness)).
+ auto=> /> &0 ge0_i _ ih i_lt_len.
  by rewrite iteriS // -ih //= /#.
by auto=> />; rewrite ge0_len iteri0 //= /WOTS_genSK /#.
qed.

hoare Eqv_WOTS_pkgen  (ad : Address.adrs) (ss ps : seed) :
  WOTS.pkGen : arg = (ss, ps, ad) ==> res = WOTS_pkgen ss ps ad.
proof.
proc.
while (0 <= i <= len
    /\ sk_seed = ss
    /\ _seed = ps
    /\ wots_skey = WOTS_genSK ad ss ps
    /\ (address, pk) = iteri i
         (fun i apk=>
            let (ad, pk) = apk in
            let ad = set_chain_addr ad i in
            let sk_i = nth witness (LenNBytes.val wots_skey) i in
            let pk_i = chain sk_i 0 (w - 1) ps ad in
            let pk = put pk i pk_i in
            (ad, pk))
         (ad, nseq len witness)).
+ wp; ecall (chain_eq sk_i 0 (w - 1) _seed address).
  auto=> /> &0 ge0_i _ ih i_lt_len.
  split; [smt(gt0_w)|].
  by rewrite iteriS // -ih //= /#.
ecall (Eqv_WOTS_genSK address sk_seed _seed).
by auto=> />; rewrite ge0_len iteri0 //= /WOTS_pkgen /#.
qed.

phoare Chain_chain_ll: [ Chain.chain: 0 <= s < Params.w ==> true ] =1%r.
proof.
proc; sp; conseq (: 0 <= chain_count <= s ==> _)=> //.
while (0 <= chain_count <= s) (s - chain_count) s 1%r=> //.
+ smt().
+ move=> ih'; sp; conseq ih'.
  by move=> &0 /> /#.
+ by auto=> /> &0 /#.
by split=> [/#|z]; auto=> /> /#.
qed.

lemma Eqv_WOTS_pkgen_ll  :
 islossless WOTS.pkGen.
proof.
(** FIXME: Really? **)
proc; sp.
seq 1: (i = 0)=> //.
+ conseq (: true)=> //.
  call (: true)=> //.
  sp; conseq (: size sk = Params.len /\ 0 <= i <= Params.len ==> _).
  + by move=> &0 />; rewrite ge0_len size_nseq; smt(ge0_len).
  while (0 <= i <= Params.len) (Params.len - i) Params.len 1%r=> //.
  + smt(ge0_len).
  + move=> ih; sp; conseq ih.
    by move=> &0 />; smt(size_put).
  + by auto=> /> &0 /#.
  by split=> [/#|z]; auto=> /> /#.
+ conseq (: 0 <= i <= Params.len ==> _)=> //.
  + smt(ge0_len).
  while (0 <= i <= Params.len) (Params.len - i) Params.len 1%r=> //.
  + smt(ge0_len).
  + move=> ih.
    seq -1: (0 <= i <= Params.len)=> //.
    + wp; call Chain_chain_ll.
      by wp; auto=> />; smt(w_vals).
    by hoare; wp; conseq (: true)=> //; 1:smt().
  + wp; conseq (: true)=> //.
    + smt().
    call Chain_chain_ll.
    by wp; auto=> />; smt(w_vals).
  split=> [/#|z].
  wp; call (: 0 <= s < Params.w ==> true).
  + by conseq Chain_chain_ll.
  by auto=> />; smt(w_vals).
+ by hoare; conseq (: true)=> />.
qed.

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
                   (h - size p) ((head witness ls) %/ 2 ^ ((h - size p))))
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
case (t = 0).
- move=> ->> HH /=; have Hl: lidxo = 0 by move: lt; rewrite expr0 /#.
  move: HH;  rewrite Hl /stack_increment /= ifF 1:/# /= !size_cat /=.
  rewrite /hw /= /lpathst /= !count_rev BS2Int.int2bs0 /= BS2Int.int2bs1 //= !nseq0 /= /pred1 /=.
  move => HH He;elim He => He; smt(take0).
move => gt0t.
 move: lt hinc => ^[ge0_lidx _]; case/(hwincSE_lpathst lidxo t tr).
- move => /= [#]; move : ge0_lidx => +Hlidxo;rewrite Hlidxo => ? H1 H2; rewrite H1 H2 => ??Hcases;elim Hcases.
  + rewrite /stack_increment /= ifF  1:/# size_cat /=.  
    by move => H; have ? : (offset = 1 + hw (nseq t false)); smt(@List sfl_size).
  + rewrite /stack_increment /= ifF  1:/# size_cat /= => [#].
    rewrite !size_take;1:   smt(@List sfl_size).
    rewrite !sfl_size ;1..4:   smt(@List sfl_size).
    have ? : 1 <= offset <= t+1 by smt(hw_nseq).
    rewrite H1 !hw_nseq 1..2:/# /=.
    move => H H0;have ? : offset = 1; last by smt(). 
    move : H0.
    case (offset - 1 < t) => ?; last first.
    + rewrite ifT 1:/#. 
      rewrite take_oversize;1: smt(sfl_size @List).
      rewrite nth_cat ifF;1: smt(sfl_size @List).
      rewrite nth_cat ifT;1: smt(sfl_size @List).
      have -> /= :  (t - size (stack_from_leaf start (2 ^ t - 1) t ss ps ad)) = 0 by smt( @List sfl_size). 
      rewrite /stack_from_leaf /paths_from_leaf /= ifF 1:/# H1. 
      rewrite /extract_path pmap_map /= /range /=. 
      rewrite eq_in_filter_predT. 
      + move => l; rewrite mapP =>He;elim He =>x;rewrite mem_iota /= => [#]??;smt(@List).
      rewrite (nth_map witness) /=;1: smt( @List sfl_size). 
      rewrite (nth_map witness) /=;1: smt( @List sfl_size). 
      rewrite (nth_map witness) /=;1: smt( @List sfl_size). 
      smt( @List sfl_size). 
    + rewrite ifF 1:/#. 
      rewrite nth_cat ifF;1: smt(sfl_size @List).
      rewrite nth_cat ifT;1: smt(sfl_size @List).
      pose ll :=  (h - ((nth witness (stack_from_leaf start (2 ^ t - 1) t ss ps ad) (offset - 1)).`2 + 1)).
      have -> /= : (offset - 1 - size (take (offset - 1) (stack_from_leaf start (2 ^ t - 1) t ss ps ad))) = 0 by   smt(sfl_size @List).
      rewrite (nth_take witness);1,2:smt().
      rewrite /stack_from_leaf /paths_from_leaf /= ifF 1:/# H1. 
      rewrite /extract_path pmap_map /= /range /=. 
      rewrite eq_in_filter_predT. 
      + move => l; rewrite mapP =>He;elim He =>x;rewrite mem_iota /= => [#]??;smt(@List).
      rewrite (nth_map witness) /=;1: smt( @List sfl_size). 
      rewrite (nth_map witness) /=;1: smt( @List sfl_size). 
      rewrite (nth_map witness) /=;1: smt( @List sfl_size). 
      rewrite (nth_map witness) /=;1: smt( @List sfl_size). 
      rewrite (nth_map witness) /=;1: smt( @List sfl_size). 
      rewrite (nth_map witness) /=;1: smt( @List sfl_size). 
      smt( @List sfl_size). 

(pose k':= argmax _ _) => [# /=] ? + ^hdec - -> ?.
have ?: 0 < k' by smt().
have := int2bs_incSE t lidxo _ _ _; ~-1: by move=> //#.
rewrite -/k' /= => [#] ?? /= => hhd eqE1 eqE2 hoff.
pose si := stack_increment _ _ _ _ _ _ _.
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
move=> 4? l *; have [] := hwincSE_lpathst lidxo t // //.
- move=> [#] ->> /= eq1 eq2 @/stack_increment /=.
  rewrite eq1 eq2 /= !hw_nseq ~-1://# /= take0 cat0s.
  rewrite !sfl_size ~-1:/# eq1 hw_nseq ~-1://# /=.
  have ->>: l = 0.
  - have: l < hw (lpathst (2 ^ t - 1 + 1) t) by smt().
    by rewrite /= eq2 /= hw_nseq /= /#.
  case: (t = 0) => [->>|nz_t] /=.
  - rewrite !stack_from_leaf0 ~-1://# /=.
    rewrite /stack_from_leaf paths_from_leaf_root /= cats0.
    by rewrite /prefix /= take_size.
  - rewrite !ifF ~-1:/# /= /stack_from_leaf paths_from_leaf_root /= cats0; split.
    - rewrite /paths_from_leaf eq1 ifF 1:/# /=.
      rewrite range_ltn 1:/# /= nseqS_minus 1:/# /extract_path /=.
      rewrite /prefix size_lpath ~-1:/# ifF 1:/#; congr.
      rewrite /lpath !b2i0_eq ~-1:/# /=.
      have ->:
          take (h - t) (rev (BS2Int.int2bs h (start + (2 ^ t - 1))))
        = rev (drop t (BS2Int.int2bs h (start + (2 ^ t - 1)))).
      - by rewrite rev_drop ?BS2Int.size_int2bs 1:/# ler_maxr 1:/#.
      have ->:
          take (h - t) (rev (BS2Int.int2bs h start))
        = rev (drop t (BS2Int.int2bs h start)).
      - by rewrite rev_drop ?BS2Int.size_int2bs 1:/# ler_maxr 1:/#.
      congr; rewrite (_ : h = h - t + t) 1:#ring.
      rewrite -[t]ger0_norm 1:/# -!BS2Int.int2bs_divr_pow2.
      rewrite !ger0_norm 1:/#; have/dvdzP: 2 ^ t %| start by done.
      case=> q ->>; rewrite divzMDl ?expf_eq0 // mulzK ?expf_eq0 //.
      by rewrite pdiv_small 1:/# /=.
    - rewrite /paths_from_leaf ifF 1:/# range_ltn 1:/# /=.
      by rewrite eq1 nseqS_minus 1:/# /extract_path.

move=> [#] lt; (pose k := argmax _ _) => /= eqhw.
rewrite /stack_increment /= eqhw; have: 0 <= k by apply: ge0_argmax.

rewrite lez_eqVlt => -[^eq0k <- /=|].
- rewrite iftrue 1:/#; have: 0 <= l < hw (lpathst (lidxo + 1) t) by done.
  rewrite eqhw -eq0k /= ltzS [l <= _](lez_eqVlt).
  case=> ge0_l; case=> [->>|ltl]; last first.
  - rewrite nth_cat sfl_size ~-1:/# ltl /=.
    rewrite /stack_from_leaf /= !(nth_map witness) ?pfl_size ~-1://# /=.
    by rewrite hwinc_pathsprev //#.
  - rewrite nth_cat sfl_size ~-1:/# ltzz /= /stack_from_leaf.
    rewrite !(nth_map witness) ?pfl_size ~-1:/# /=.
    have [-> /=] := hwinc_leaflast lidxo t _ _ _; ~-1: smt().
    move=> ?; congr.
    rewrite /prefix. 
    rewrite -(cat_take_drop (size (lpath start) - t) (lpath (start + lidxo)) ); congr.
    + apply (eq_from_nth false);1:by smt(size_lpath size_take).
      move=> i *; rewrite !nth_take; ~-1: smt(size_lpath size_take).
      rewrite /lpath !nth_rev; ~-1:smt(size_rev size_lpath size_take).
      rewrite !b2i0_eq ~-1:/# !BS2Int.size_int2bs /= ler_maxr ~-1:/#.
      rewrite /BS2Int.int2bs !nth_mkseq => /=; ~-1: smt(size_lpath size_take).
      do 4! congr.
      have ?: t <= h - (i + 1) <= h by smt(size_lpath size_take).
      have ->: 2 ^ (h - (i + 1)) = 2^t * 2^(h - (i + 1) - t).
      - by  rewrite -exprD_nneg /#.
      by rewrite !divz_mulp ?expr_gt0 /#.
    rewrite /lpath size_rev BS2Int.size_int2bs b2i0_eq ~-1:/# ler_maxr 1:/#.
    have := hwinc_leaflast lidxo t _ _ _; ~-1:smt().
    have -> [H1 H2]: (hw (lpathst (lidxo + 1) t) - 1) = (hw (lpathst lidxo t)) by smt().
    rewrite -{1}(BS2Int.int2bsK t lidxo) 1,2:/# in H2.
    have -> :
         (nth witness (paths_from_leaf (lidxo + 1) t) (hw (lpathst lidxo t)))
       = rev (BS2Int.int2bs t lidxo)
      by smt(size_rev BS2Int.size_int2bs rev_inj revK BS2Int.inj_bs2int_eqsize).
    apply (eq_from_nth false); 1: by smt(size_drop BS2Int.size_int2bs size_rev).
    move => i ib.
    rewrite nth_drop 1,2:/# !nth_rev; ~-1: smt(size_drop BS2Int.size_int2bs size_rev).
    rewrite !BS2Int.size_int2bs /BS2Int.int2bs !nth_mkseq => /=;
      ~-1: smt(size_lpath size_take size_drop BS2Int.size_int2bs size_rev).
    rewrite !ler_maxr ~-1:/#.
    do 2! congr.
    have /=:= modz_pow_div 2 (t-i) (t - i - 1) (start + lidxo) _ _;
      ~-1: smt(size_drop size_rev BS2Int.size_int2bs).
    rewrite (_ : t - i - (t - i - 1) = 1) 1:#ring.
    have -> : (start + lidxo) %% 2 ^ (t-i)  = lidxo %% 2^(t-i); last first.
    + have /= -> := modz_pow_div 2 (t-i) (t - i - 1) (lidxo) _ _;
        ~-1: smt(size_drop size_rev BS2Int.size_int2bs).
      by rewrite (_ : t - i - (t - i - 1) = 1) 1:#ring /#.
    have := modz_mod_pow2 (start + lidxo) t (t-i). 
    have := modz_mod_pow2 (lidxo) t (t-i). 
    have -> : min (`|t|) (`|t - i|)  = t-i.
    - by rewrite !ger0_norm;smt(size_drop size_rev BS2Int.size_int2bs).
    by move => <- <-; (do 2! congr); smt().

have := int2bs_incSE t lidxo _ _ _; ~-1:smt().
rewrite -/k /= => [# lt_kt all1 has0 eqE eqES].

move=> ge0_k; rewrite ifF 1:/# sfl_size ~-1:/# -eqhw ifF ~-1:/#.
have ?: 0 <= hw (BS2Int.int2bs t lidxo) - k.
- rewrite -(ler_add2r 1) /= addrAC; move: eqhw.
  rewrite /lpathst !b2i0_eq ~-1:/# /= !hw_rev => <-.
  rewrite -ltzS (ltr_add2r 1 0) ltr_neqAle ge0_hw /= /hw.
  apply/negP => /eq_sym /count_eq0 /=.
  by rewrite eqES has_cat.

rewrite /lpathst hw_rev b2i0_eq ~-1:/# /= hwincSE ~-1:/# -/k.
rewrite [_ - 1]addrAC /= nth_cat size_take_condle ~-1://.
rewrite sfl_size ~-1:/# /lpathst hw_rev b2i0_eq ~-1:/# /=.
rewrite [hw _ - k <= _](_ : _ = true) 1:/# /=.

pose r := hw (drop (k + 1) (BS2Int.int2bs t lidxo)).

have eq1: paths_from_leaf lidxo t =
      pmap (extract_path (lpathst lidxo t)) (range 0 (t - k))
   ++ map (oget \o extract_path (lpathst lidxo t)) (range (t - k) t).
- rewrite /paths_from_leaf ifF ~-1:/# (range_cat (t - k)) ~-1:/#.
  rewrite pmap_cat; congr; rewrite pmap_map filter_map -map_comp.
  rewrite eq_in_filter_predT // => i /mem_range rgi @/preim @/predC1.
  rewrite /extract_path ifT // /lpathst b2i0_eq ~-1:/# /=.
  rewrite nth_rev BS2Int.size_int2bs ?ler_maxr ~-1://#.
  by rewrite eqE nth_cat size_nseq ifT 1:/# nth_nseq //#.

have eq2: paths_from_leaf (lidxo + 1) t =
      pmap (extract_path (lpathst lidxo t)) (range 0 (t - (k + 1)))
   ++ [oget (extract_path (lpathst (lidxo + 1) t) (t - (k + 1)))].
- rewrite /paths_from_leaf ifF ~-1:/# (range_cat (t - (k + 1))) ~-1:/#.
  have hsz: size (rev (drop (k + 1) (BS2Int.int2bs t lidxo))) = t - (k + 1).
  - rewrite size_rev; move/(congr1 List.size): (eqE).
    rewrite BS2Int.size_int2bs ler_maxr 1:/#.
    by rewrite size_cat size_nseq /= /#.
  rewrite pmap_cat; congr.
  - rewrite /lpathst !b2i0_eq ~-1:/# /= eqE eqES !pmap_map; do 2! congr.
    apply: eq_in_map => i /mem_range rgi @/extract_path.
    rewrite !rev_cat !rev_cons -!cats1 -!catA.
    do 2! (rewrite nth_cat [if i < _ then _ else _]ifT 1:/#); congr.
    by rewrite !take_catl /#.
  - rewrite (range_cat (t - k)) ~-1:/# pmap_cat.
    have ->/=: range (t - (k + 1)) (t - k) = [t - (k + 1)] by smt(rangeS).
    rewrite pmap_map eq_in_filter_pred0 ?cats0.
    - move=> p /mapP [i] [] /mem_range rgi ->>.
      rewrite /lpathst b2i0_eq 1:/# /= eqES /extract_path ifF //.
      rewrite nth_rev size_cat /= size_nseq -size_rev hsz ~-1:/#.
      rewrite ler_maxr 1:/# (_ : _ - _ = t - (i + 1)) 1:#ring.
      by rewrite nth_cat ifT ?size_nseq 1:/# nth_nseq //#.
    rewrite ifF // /extract_path ifT //.
    rewrite /lpathst b2i0_eq 1:/# /= nth_rev.
    - by rewrite BS2Int.size_int2bs /#.
    rewrite BS2Int.size_int2bs ler_maxr 1:/#.
    rewrite (_ : t - _ = k) 1:#ring eqES.
    by rewrite nth_cat size_nseq ler_maxr 1:/# ltzz.

case _: (l < _) => /= [ltl|/lerNgt gel].
- rewrite nth_take ~-1:///stack_from_leaf.
  rewrite !(nth_map witness) ?pfl_size ~-1://# /=.
  suff ->:
      nth witness (paths_from_leaf lidxo t) l
    = nth witness (paths_from_leaf (lidxo + 1) t) l
  by done.

  rewrite eq1 eq2 !nth_cat !pfl_r_size_min ~-1:/# !ifT.
  - rewrite /lpathst b2i0_eq 1:/# /= {1}(_ : t = size (BS2Int.int2bs t lidxo)).
    - by rewrite BS2Int.size_int2bs /#.
    rewrite -rev_drop ?BS2Int.size_int2bs 1:/# hw_rev.
    rewrite eqE drop_cat size_nseq ler_maxr 1:/# /=.
    by move: ltl; rewrite {1}eqE hw_cat /= hw_nseq /= /#.
  - rewrite /lpathst b2i0_eq 1:/# /= {1}(_ : t = size (BS2Int.int2bs t lidxo)).
    - by rewrite BS2Int.size_int2bs /#.
    rewrite -rev_drop ?BS2Int.size_int2bs 1:/# hw_rev.
    rewrite eqE drop_cat size_nseq ler_maxr 1:/# /=.
    by move: ltl; rewrite {1}eqE hw_cat /= hw_nseq /= /#.
  rewrite (range_cat (t - (k + 1)) 0 (t - k)) ~-1:/#.
  rewrite pmap_cat nth_cat ifT //.
  rewrite pfl_r_size_min 1:/# /lpathst b2i0_eq 1:/# /=.
  rewrite {1}(_ : t = size (BS2Int.int2bs t lidxo)).
  - by rewrite ?BS2Int.size_int2bs //#.
  rewrite -rev_drop ?BS2Int.size_int2bs 1:/# hw_rev.
  by move: ltl; rewrite {1}eqE hw_cat /= hw_nseq /= /#.

- rewrite subr_eq0; case _: (l = _) => /= [->>|]; last first.
  - move=> nel; move: nel gel; rewrite ler_eqVlt eq_sym => -> /= gtl.
    rewrite nth_default // sfl_size ~-1:/# eqhw.
    by rewrite /lpathst hw_rev b2i0_eq 1:/# /= /#.
apply/eq_sym; rewrite {1}/stack_from_leaf eq2.
rewrite map_cat nth_cat size_map pfl_r_size_min ~-1:/#.
rewrite /lpathst !b2i0_eq ~-1:/# /=.
have := BS2Int.size_int2bs t lidxo; rewrite ler_maxr 1:/# => {2}<-.
rewrite -rev_drop ?BS2Int.size_int2bs ~-1://# hw_rev.
rewrite {1}eqE hw_cat /= hw_nseq /= ~-1://# addrAC /=.
have := BS2Int.size_int2bs t lidxo; rewrite ler_maxr 1:/# => {2}<-.
rewrite -rev_drop ?BS2Int.size_int2bs ~-1://# hw_rev.
rewrite {1}eqE hw_cat /= hw_nseq /= ~-1://# ifT 1:#ring.
pose x := oget _; congr; first congr.
- rewrite /lpath !b2i0_eq ~-1:/# /=.
  have /dvdzP[q ->>]: 2 ^ t %| start by done.
  rewrite (BS2Int.int2bs_cat t _ (_ + _)%Int) ~-1:/#.
  have ->: (q * 2 ^ t + lidxo) %/ 2 ^ t = q.
  - by rewrite divzMDl ?expf_eq0 // pdiv_small 1:/#.
  rewrite -(BS2Int.int2bs_mod _ (_ + _)%Int) modzMDl pmod_small ~-1:/#.
  rewrite rev_cat /stack_from_leaf take_catr; last congr.
  - rewrite eq1 map_cat nth_cat ifF.
    - rewrite size_map pfl_r_size_min ~-1:/# /lpathst b2i0_eq 1:/# /=.
      have {2}->: t = size (BS2Int.int2bs t lidxo).
      - by rewrite BS2Int.size_int2bs /#.
      rewrite -rev_drop ?BS2Int.size_int2bs 1:/# hw_rev.
      rewrite {1}eqE hw_cat /= hw_nseq /= ~-1:/# addrAC /=.
      by rewrite {2}eqE drop_catr ?size_nseq 1:/# ler_maxr 1:/#.
    rewrite size_rev BS2Int.size_int2bs ler_maxr 1:/#.
    rewrite ler_add2l ler_opp2 size_map pfl_r_size_min ~-1:/#.
    rewrite {2}/lpathst b2i0_eq 1:/# /=.
    rewrite (_ : take _ _ = rev (drop k (BS2Int.int2bs t lidxo))).
    - by rewrite rev_drop ?BS2Int.size_int2bs /#.
    rewrite hw_rev {1}eqE hw_cat hw_nseq ~-1:/# /=.
    rewrite {2}eqE drop_catr ?size_nseq ~-1:/# ler_maxr 1:/# /=.
    rewrite (_ : k + _ - k - _ = 0) 1:#ring.
    rewrite range_ltn 1:/# /= /extract_path /(\o) ifT /=.
    - rewrite /lpathst b2i0_eq 1:/# /= nth_rev ?BS2Int.size_int2bs 1:/#.
      rewrite ler_maxr 1:/# (_ : t - _ = k - 1) 1:#ring.
      by rewrite eqE nth_cat ifT ?size_nseq 1:/# nth_nseq /#.
    rewrite size_rcons; smt(size_ge0).
  - rewrite /prefix size_rev BS2Int.size_int2bs ler_maxr 1:/#.
    rewrite {1}(_ : h = size (BS2Int.int2bs h (q * 2 ^ t))).
    - by rewrite BS2Int.size_int2bs /#.
    rewrite -rev_drop ?BS2Int.size_int2bs 1:/#; congr.
    rewrite -[t]ger0_norm 1:/# {1}(_ : h = (h - `|t|) + `|t|) 1:#ring.
    rewrite -BS2Int.int2bs_divr_pow2 ger0_norm 1:/#.
    by rewrite mulzK // expf_eq0.
  - rewrite size_rev BS2Int.size_int2bs ler_maxr 1:/#.
    rewrite eq1 map_cat nth_cat ifF.
    - rewrite size_map pfl_r_size_min ~-1:/# /lpathst b2i0_eq 1:/# /=.
      have {2}->: t = size (BS2Int.int2bs t lidxo).
      - by rewrite BS2Int.size_int2bs /#.
      rewrite -rev_drop ?BS2Int.size_int2bs 1:/# hw_rev.
      rewrite {1}eqE hw_cat /= hw_nseq /= ~-1:/# addrAC /=.
      by rewrite {2}eqE drop_catr ?size_nseq 1:/# ler_maxr 1:/#.
    rewrite size_map pfl_r_size_min 1:/#.
    rewrite (_ : take (t - k) _ = rev (drop k (BS2Int.int2bs t lidxo))).
    - by rewrite rev_drop ?BS2Int.size_int2bs /#.
    rewrite hw_rev {1}eqE hw_cat hw_nseq ~-1:/# /=.
    rewrite {2}eqE drop_catr ?size_nseq ~-1:/# ler_maxr 1:/# /=.
    rewrite (_ : k + _ - k - _ = 0) 1:#ring.
    rewrite range_ltn 1:/# /= /extract_path /(\o) ifT /=.
    - rewrite /lpathst b2i0_eq 1:/# /= nth_rev ?BS2Int.size_int2bs 1:/#.
      rewrite ler_maxr 1:/# (_ : t - _ = k - 1) 1:#ring.
      by rewrite eqE nth_cat ifT ?size_nseq 1:/# nth_nseq /#.
    rewrite size_rcons size_take_condle 1:/# ifT.
    - by rewrite /lpathst size_rev b2i0_eq 1:/# /= BS2Int.size_int2bs /#.
    rewrite (_ : h - _ - _ = t - k) 1:#ring.
    rewrite (_ : take _ _ = rev (drop k (BS2Int.int2bs t lidxo))).
    - by rewrite rev_drop ?BS2Int.size_int2bs /#.
    rewrite eqE drop_cat size_nseq ler_maxr 1:/# /=.
    rewrite /x /extract_path ifT /=.
    - rewrite nth_rev ?BS2Int.size_int2bs 1:/# ler_maxr 1:/#.
      rewrite (_ : t - _ = k) 1:#ring eqES nth_cat.
      by rewrite size_nseq ler_maxr 1:/#.
    rewrite rev_cons rev_drop ?BS2Int.size_int2bs 1:/# ler_maxr 1:/#; congr.
    rewrite {1}(_ : t = size (BS2Int.int2bs t (lidxo + 1))).
    - by rewrite BS2Int.size_int2bs /#.
    rewrite {3}(_ : t = size (BS2Int.int2bs t lidxo)).
    - by rewrite BS2Int.size_int2bs /#.
   rewrite -!rev_drop ?BS2Int.size_int2bs ~-1:/#; congr.
   rewrite eqE eqES !drop_cat !size_nseq !ler_maxr ~-1:/#.
   by rewrite !ifF ~-1:/# addrAC.
- rewrite /stack_from_leaf eq1 map_cat nth_cat ifF.
  - rewrite size_map pfl_r_size_min 1:/# /lpathst b2i0_eq 1:/# /=.
    rewrite {2}(_ : t = size (BS2Int.int2bs t lidxo)).
    - by rewrite BS2Int.size_int2bs /#.
    rewrite -rev_drop ?BS2Int.size_int2bs 1:/# hw_rev.
    rewrite {1}eqE hw_cat /= hw_nseq /= ~-1://# addrAC /=.
    by rewrite {2}eqE drop_cat size_nseq ler_maxr ~-1:/#.
  rewrite size_map pfl_r_size_min ~-1:/# /lpathst b2i0_eq ~-1:/# /=.
  rewrite (_ : take (t - k) _ = rev (drop k (BS2Int.int2bs t lidxo))).
  - by rewrite rev_drop ?BS2Int.size_int2bs /#.
  rewrite hw_rev {2}eqE hw_cat /= hw_nseq 1:/# /=.
  rewrite {3}eqE drop_cat size_nseq ler_maxr 1:/# /=.
  rewrite [k + _ - k]addrAC /= range_ltn 1:/# /=.
  rewrite /(\o) /extract_path ifT /=.
  - rewrite nth_rev ?BS2Int.size_int2bs 1:/# ler_maxr 1:/#.
    rewrite (_ : t - _ = k - 1) 1:#ring eqE.
    by rewrite nth_cat ifT ?size_nseq 1:/# nth_nseq /#.
  rewrite size_rcons opprD -addrA /= /x /extract_path ifT /=.
  - rewrite nth_rev ?BS2Int.size_int2bs 1:/# ler_maxr 1:/#.
    rewrite (_ : t - _ = k) 1:#ring eqES nth_cat ifF ?size_nseq 1:/#.
    by rewrite ler_maxr 1:/#.
  rewrite size_rcons size_take 1:/# size_rev BS2Int.size_int2bs ler_maxr 1:/#.
  rewrite ifT 1:/# size_take 1:/# size_rev  BS2Int.size_int2bs ler_maxr 1:/#.
  by rewrite ifT 1:/#; ring.
qed.

lemma si_size_in_loop start lidxo t ss ps ad offset :
    0 <= t <= h
 => 0 <= start <= 2^h - 2^t
 => 2^t %| start
 => 0 <= lidxo < 2^t
 => hw (lpathst (lidxo + 1) t) <= hw (lpathst lidxo t)
 => hw (lpathst (lidxo + 1) t) <= offset <= hw (lpathst lidxo t) + 1
 => 2 <= offset
 => (nth witness (stack_increment start lidxo t ss ps ad offset) (offset - 1)).`2 = 
    (nth witness (stack_increment start lidxo t ss ps ad offset) (offset - 2)).`2
 =>    size ((stack_increment start lidxo t ss ps ad offset)) = offset
    /\ size (stack_from_leaf start (lidxo + 1) t ss ps ad) < offset.
proof.
move=> 7? eqnth; rewrite -andaE; split=> [|<-].
- rewrite /stack_increment /= ltrNge ifF //.
  by rewrite size_cat /= size_take_condle 1:/# ifT // sfl_size //#.
have ? := h_g0; (have := hwincSE_lpathst lidxo t _ _; ~-1:smt()); case.
- move => [#] Hli Hlp Hlp1.
  + rewrite /stack_increment /= ifF  1:/# size_cat /=.  
    rewrite !size_take ~-1:/# !sfl_size ~-1:/#.
    have ?: 1 <= offset <= t+1 by smt(hw_nseq).
    rewrite Hlp Hlp1 !hw_nseq 1:/# /=.
    by rewrite hw_nseq ~-1:/# /= /#.
(pose k':= argmax _ _) => [# /=] *.
have ?: 0 < k' by smt(). have := int2bs_incSE t lidxo _ _ _; ~-1:smt().
rewrite -/k' /= => [#] 2?? /= eqE1 eqE2.
pose si := stack_increment start lidxo t ss ps ad offset.
pose oldstack := stack_from_leaf start lidxo t ss ps ad.
pose level :=
  if   offset = size oldstack + 1
  then 0
  else (nth witness oldstack (offset - 1)).`2 + 1.
pose carrypath := take (h - level) (lpath (start + lidxo)).
have siE : si =
  take (offset - 1) oldstack ++ [(node_from_path carrypath ss ps ad, level)].
- by rewrite /si /stack_increment /= iffalse //#.
have szod: size oldstack = hw (lpathst lidxo t).
- by rewrite /oldstack sfl_size ~-1:/#.
have ltk': k' <= hw (lpathst lidxo t).
- rewrite /lpathst hw_rev b2i0_eq 1:/# /= eqE1.
  by rewrite hw_cat hw_nseq 1:/# /=; smt(ge0_hw).
have size_tk_od: size (take (offset - 1) oldstack) = offset - 1.
- by rewrite /oldstack size_take_condle -1:sfl_size -1:iftrue //#.
rewrite siE size_cat /= size_tk_od /=.
rewrite sfl_size ~-1:/#; apply: contraLR eqnth => /lezNgt leoff.
rewrite -/si {1}siE nth_cat size_tk_od /= /level iffalse 1:/#.
have offE: offset = hw (lpathst lidxo t) + 1 - k' by smt().
have ->: offset = hw (lpathst (lidxo + 1) t) by smt().
rewrite siE nth_cat iftrue 1:size_tk_od 1:/# nth_take ~-1:/#.
rewrite /oldstack /stack_from_leaf.
rewrite !(nth_map witness) /= 1?pfl_size ~-1:/#.
rewrite /paths_from_leaf !iffalse ~-1:/#.
rewrite -addrA; apply/negP => /Ring.IntID.addrI.
rewrite -{3}[1](opprK) -opprD => /Ring.IntID.oppr_inj => /=.
pose s := pmap _ _; rewrite /lpathst b2i0_eq ~-1:/# /=.
rewrite eqE2 hw_rev /= hw_cat /= hw_nseq ~-1:/# /= [-1 + _]addrC.
have htk: take (t - k') (lpathst lidxo t) = rev (drop k' (BS2Int.int2bs t lidxo)).
- have {1}->: t = size (BS2Int.int2bs t lidxo).
  - by rewrite BS2Int.size_int2bs /#.
  rewrite /lpathst b2i0_eq 1:/# /=.
  by rewrite -rev_drop ?BS2Int.size_int2bs 1:/#.
pose i := hw _; have -> {i}: i = hw (drop k' (BS2Int.int2bs t lidxo)).
- by rewrite eqE1 drop_cat size_nseq ifF ~-1:/# ler_maxr 1:/# drop0.
rewrite (_ : size _ = t - k' + 1) /=.
- rewrite /s (range_cat (t - k')) ~-1:/# pmap_cat nth_cat ifF.
  - rewrite pfl_r_size_min ~-1:/# htk hw_rev /i.
    by rewrite eqE1 !drop_cat size_nseq ler_maxr 1:/# !ifF ~-1:/#.
  rewrite pfl_r_size_min ~-1:/# htk hw_rev range_ltn ~-1:/# /=.
  have: extract_path (lpathst lidxo t) (t - k') <> None.
  - rewrite /extract_path ifT // /lpathst b2i0_eq 1:/# /=.
    rewrite nth_rev ?BS2Int.size_int2bs ~-1:/# /=.
    rewrite ler_maxr 1:/# [t - _](_ : _ = k' - 1) 1:#ring.
    by rewrite eqE1 nth_cat ifT ?size_nseq ~-1:/# nth_nseq /#.
  rewrite -if_neg => ^ + -> /= - @/extract_path.
  case: (nth _ _ _) => //=; rewrite size_rcons.
  rewrite size_take_condle ~-1:/# /lpathst b2i0_eq 1:/# /=.
  by rewrite size_rev BS2Int.size_int2bs ler_maxr 1:/# ifT 1:/#.
rewrite eq_sym /s (range_cat (t - k')) ~-1:/# pmap_cat nth_cat ifT.
- by rewrite pfl_r_size_min ~-1:/# htk hw_rev /#.
rewrite {1}(_ : t - k' = t - (k' + 1) + 1) 1:#ring rangeSr ~-1:/#.
rewrite -cats1 pmap_cat nth_cat ifT.
- rewrite pfl_r_size_min ~-1:/# /lpathst b2i0_eq 1:/# /=.
  have {2}->: t = size (BS2Int.int2bs t lidxo) by rewrite BS2Int.size_int2bs /#.
  rewrite -rev_drop ?BS2Int.size_int2bs ~-1:/# hw_rev.
  rewrite eqE1 !drop_cat ?size_nseq ler_maxr ~-1:/# /=.
  by rewrite !ifF ~-1:/# (_ : k' + 1 - _ - _ = 0) 1:#ring drop0 /#.
pose i := hw _ - 1; pose s' := pmap _ _; have lti: i < size s'.
- rewrite /i /s' pfl_r_size_min ~-1:/# /lpathst b2i0_eq 1:/# /=.
  have {2}->: t = size (BS2Int.int2bs t lidxo) by rewrite BS2Int.size_int2bs /#. 
  rewrite -rev_drop ?BS2Int.size_int2bs ~-1:/# hw_rev.
  by rewrite {1}eqE1 !drop_cat ?size_nseq ler_maxr ~-1:/# /= /#.
have gt0_i: 0 <= i.
- rewrite /i; move: offE; rewrite /lpathst b2i0_eq /= 1:/# hw_rev.
  rewrite {1}eqE1 hw_cat hw_nseq /= ~-1:/#.
  rewrite [_ - k']addrC !addrA /= => offE.
  rewrite eqE1 drop_cat size_nseq ler_maxr 1:/# /=.
  have: 2 <= offset by done.
  by rewrite offE -ler_subl_addr /= /#.
have: nth witness s' i \in s' by apply/mem_nth; smt(ge0_hw).
case/pmapP => j [] /mem_range rgj @/extract_path.
case (nth false (lpathst lidxo t) j) => // _.
move/someI=> ->; rewrite size_rcons size_take_condle ~-1:/#.
suff ->: size (lpathst lidxo t) = t by rewrite ifT /#.
rewrite /lpathst size_rev b2i0_eq /= ~-1:/#.
by rewrite BS2Int.size_int2bs /#.
qed.

(* entering the inner loop for a leaf tree means that
   we are still hashing values at height < h-1: when
   we exit the loop for leaf 2^h - 1 we have produced a
   hash at level h *)
lemma si_heights_in_loop_bnd start lidxo t ss ps ad offset k :
     0 <= t <= h
  => 0 <= start <= 2^h - 2^t
  => 2^t %| start
  => 0 <= lidxo < 2^t
  => hw (lpathst (lidxo + 1) t) <= hw (lpathst lidxo t)
  => hw (lpathst (lidxo + 1) t) <= offset <= hw (lpathst lidxo t) + 1
  => 2 <= offset
  => (nth witness (stack_increment start lidxo t ss ps ad offset) (offset - 1)).`2 = 
     (nth witness (stack_increment start lidxo t ss ps ad offset) (offset - 2)).`2
  => 0 <= k < offset
  => 0 <= (nth witness (stack_increment start lidxo t ss ps ad offset) k).`2 < h.
proof.
move=> *; have := si_size_in_loop start lidxo t ss ps ad offset _ _ _ _ _ _ _ _; ~-1:smt().
case=> *; pose s := stack_increment _ _ _ _ _ _ _.
have ?: forall x, x \in stack_from_leaf start lidxo t ss ps ad => 0 <= x.`2 < t.
- move=> x; case/mapP => bs [] @/paths_from_leaf; rewrite ifF ~-1:/# => + -> /=.
  rewrite pmap_map => /mapP[bso]; rewrite mem_filter /predC1 /=.
  case: bso => //= ? [+ <<-] - /mapP[] i [] /mem_range ?.
  rewrite /extract_path; case _: (nth _ _ _) => //= ? ->.
  split; last by smt(size_rcons size_ge0).
  rewrite size_rcons opprD addrA addrAC subr_ge0.
  rewrite ler_subr_addl addrC -ltzE size_take_condle ~-1:/#.
  rewrite /lpathst size_rev b2i0_eq ~-1:/# /=.
  by rewrite BS2Int.size_int2bs /#.
have: nth witness s k \in s by apply: mem_nth; smt().
move: (nth _ _ _) => [??]; rewrite /s /stack_increment /= => {s}.
case _: (hw _ < hw _) => /= ?.
- (rewrite mem_cat; case => /=; last (case=> _ ->> /=; apply: h_g0)); smt(h_g0).
rewrite mem_cat /=; case; first by move/mem_take; smt().
case=> _ ->>; case _: (offset = _) => /= [?|]; first by apply: h_g0.
pose s := stack_from_leaf _ _ _ _ _ _; pose x := nth _ _ _.
case: (t = 0) => [->>|nz_t].
- have: 0 <= lidxo < 2^0 by done.
  by rewrite expr0; smt(stack_from_leaf0).
rewrite /s sfl_size ~-1:/# => hsz; have: x \in drop 1 s.
- have ->: x = nth witness (drop 1 s) (offset - 2).
  - by rewrite nth_drop ~-1:/# addrCA /=.
  apply: mem_nth; split=> [|_]; first by smt().
  rewrite size_drop // /s sfl_size ~-1:/#.
  by rewrite ler_maxr; smt(ge0_hw).
rewrite /s /stack_from_leaf -map_drop /paths_from_leaf ifF 1:/#.
rewrite pmap_map -map_drop -map_comp /= => /mapP @/(\o) [].
move=> + [+ ->] - [|bso]; first by move=> /mem_drop /mem_filter @/predC1.
move=> hmem; have: Some bso \in map (extract_path (lpathst lidxo t)) (range 1 t).
- move: hmem; rewrite (range_cat 1 0 t) ~-1:/#.
  rewrite map_cat filter_cat rangeS /= {1}/extract_path.
  case: (nth _ _ _) => @{1}/predC1 /=.
  - by rewrite drop0 => /mem_filter [].
  - by move=> /mem_drop /mem_filter [].
case/mapP=> [i] [] /mem_range rgi @/extract_path.
case: (nth _ _ _) => //= ->; rewrite size_rcons.
rewrite opprD !addrA /= size_take_condle ~-1:/#.
rewrite /lpathst size_rev b2i0_eq 1:/# /=.
by rewrite BS2Int.size_int2bs /#.
qed.

lemma si_reduced_node start lidxo t ss ps ad offset :
     0 <= t <= h
  => 0 <= start <= 2^h - 2^t
  => 2^t %| start
  => 0 <= lidxo < 2^t
  => hw (lpathst (lidxo + 1) t) <= hw (lpathst lidxo t)
  => hw (lpathst (lidxo + 1) t) <= offset <= hw (lpathst lidxo t) + 1
  => 2 <= offset
  => (nth witness (stack_increment start lidxo t ss ps ad offset) (offset - 1)).`2 =
     (nth witness (stack_increment start lidxo t ss ps ad offset) (offset - 2)).`2
  =>
    let si     = (stack_increment start lidxo t ss ps ad offset) in
    let si1    = (stack_increment start lidxo t ss ps ad (offset - 1)) in
    let si_oB1 = nth witness si (offset - 1) in
    let si_oB2 = nth witness si (offset - 2) in

    (nth witness si1 (offset - 2)).`1 =
      trh
        ps
        (set_thtbidx
          (set_typeidx (adr2ads zero_address) trhtype)
          (si_oB1.`2 + 1) ((start + lidxo) %/ 2 ^ (si_oB1.`2 + 1)))
        ((DigestBlock.val si_oB2.`1) ++ (DigestBlock.val si_oB1.`1)).
proof.
move=> 8? si si1 si_oB1 si_oB2.
pose s := stack_from_leaf start lidxo t ss ps ad.
have szs: size s = hw (lpathst lidxo t) by rewrite /s sfl_size ~-1:/#.
have sz_tk: forall i, 0 < i <= offset => size (take (offset - i) s) = offset - i.
- by move=> i *; rewrite size_take_condle ~-1:/# szs ifT //#.

have gt0_t: 0 < t.
- (suff: t <> 0 by smt()); first apply/negP => ->>.
  have: offset <= hw (lpathst lidxo 0) + 1 by smt().
  rewrite /lpathst b2i0_eq /= 1:ltr_eqF //.
  by have [_ ->]: 0 <= lidxo < 2 ^ 0 by done. (* FIXME *)
  by rewrite hw_rev int2bs0s /= /#.

pose lvl := (nth witness s (offset - 2)).`2.

have rg_lvl: 0 <= lvl < t.
- have: lvl \in unzip2 s by apply/(map_f snd)/mem_nth; smt().
  case/mapP=> -[??] /= [] @/s @/stack_from_leaf.
  case/mapP=> /= bs [] + [] _ ->> ->.
  rewrite /paths_from_leaf ifF 1:/# pmap_map.
  case/mapP=> bso; rewrite mem_filter => -[] @/predC1.
  case: bso => /= [//|] ? + <<- - /mapP[] i [/mem_range rgi].
  rewrite /extract_path; case: (nth _ _ _) => //= ->.
  rewrite size_rcons size_take_condle 1:/#.
  rewrite /lpathst size_rev b2i0_eq 1:/# /=.
  by rewrite BS2Int.size_int2bs /#.

pose nps := (take (h - (lvl + 1)) (lpath (start + lidxo))).
pose e := node_from_path nps ss ps ad.

have sz_nps: size nps = h - (lvl + 1).
- rewrite /nps size_take_condle 1:/# ifT //.
  rewrite /lpath b2i0_eq 1:/# /= size_rev.
  by rewrite BS2Int.size_int2bs /#.

have eE: e =
  let ls = leaves_from_path nps in
  let nls = map (leafnode_from_idx ss ps ad) ls in
  let subtree = list2tree nls in
  val_bt_trh
    subtree ps (set_typeidx ad trhtype)
    (h - size nps) (head witness ls %/ 2 ^ (h - size nps)).
- by rewrite /e /node_from_path /= sz_nps /#.

have si1_oB2E: nth witness si1 (offset - 2) = (e, lvl + 1).
- rewrite /si1 /stack_increment /= -if_neg ltrNge /= ifT //.
  rewrite -/s szs ifF 1:/# nth_cat ifF 1:/#.
  by rewrite sz_tk ~-1:/# /=.

have iB2E:
    nth witness (stack_increment start lidxo t ss ps ad offset) (offset - 2)
  = nth witness (stack_from_leaf start lidxo t ss ps ad) (offset - 2).
- rewrite /stack_increment /= -if_neg ltrNge /= ifT 1://.
  by rewrite nth_cat sz_tk ~-1:/# ifT 1:/# nth_take ~-1:/#.

have hBnpsE: h - size nps = lvl + 1 by rewrite sz_nps #ring.

pose lfp_nps b n := mkseq ((+) (bs2int (rev nps) * 2 ^ (lvl + 1) + b)) (2^n).
have lfp_npsE: leaves_from_path nps = lfp_nps 0 (lvl + 1).
- by rewrite /leaves_from_path ifT 1:/# /= /lfp_nps hBnpsE.
have sz_lfp_nps: forall b n, size (lfp_nps b n) = 2^n.
- by move=> *; rewrite size_mkseq; smt(expr_ge0).
have lfp_npsS: forall n b, 0 <= n =>
  lfp_nps b (n + 1) = lfp_nps b n ++ lfp_nps (b + 2^n) n.
- move=> n b ?; rewrite /lfp_nps [2^(n+1)]exprS 1:/#.
  rewrite (_ : 2 * _ = 2^n + 2^n) 1:#ring.
  rewrite mkseq_add ?expr_ge0 ~-1:// /=.
  by congr; apply: eq_map => ? //#.
have hd_lfp_npsE: forall b n, head witness (lfp_nps b n) =
  bs2int (rev nps) * 2 ^ (lvl + 1) + b.
- by move=> b n; rewrite -nth0_head nth_mkseq ?expr_gt0 ~-1:/#.

rewrite si1_oB2E /= eE /= hBnpsE lfp_npsE {1}lfp_npsS 1:/# /=.
rewrite hd_lfp_npsE /= mulzK ?expf_eq0 ~-1://.
rewrite map_cat (list2treeS lvl) 1:/# 1?size_map ~-1:/# /=.

have si_oB1_fstE: si_oB1.`2 = lvl.
- admit.

congr.
- congr.
  - admit.
  - by rewrite si_oB1_fstE.
  rewrite si_oB1_fstE /nps rev_take ?size_lpath_lt ~-1:/#.
  rewrite opprD addrA /= /lpath revK b2i0_eq 1:/# /=.
  by rewrite -bs2int_div ~-1:/# int2bsK ~-1:/#.

pose k' := argmax (fun i => take i (BS2Int.int2bs t lidxo)) (all idfun).
pose k := min t k'.

have lpEth: lpath lidxo = nseq (h - t) false ++ lpathst lidxo t.
- rewrite /lpath /lpathst !b2i0_eq ~-1:/# /= (int2bs_cat t h) ~-1:/#.
  have ->: lidxo %/ 2^t = 0 by smt().
  by rewrite int2bs0 rev_cat rev_nseq.

have: exists xxx,
     xxx = take (t - (k + 1)) (lpathst lidxo t)
  /\ xxx = take (t - (k + 1)) (lpathst (lidxo + 1) t).
- admit.

case=> xxx [xxxE xxxSE].

have lpE: lpathst lidxo t = xxx ++ false :: nseq k true  by admit.
have lpSE: lpathst (lidxo + 1) t = xxx  ++ true :: nseq k false by admit.

have ?: hw (lpathst (lidxo + 1) t) = hw (lpathst lidxo t) + 1 - k.
- by rewrite lpE lpSE !hw_cat /= !hw_nseq ?(b2i0, b2i1); smt(ge0_argmax).

have ?: 0 < k <= t.
- split=> [|_]; last by rewrite /k minrl.

  admit.


have ?: forall i, 0 < i < k => (nth witness s (hw (lpathst lidxo t) + 1 + i)).`2 = i.
- move=> i rgi; rewrite /s /stack_from_leaf /paths_from_leaf.
  rewrite ifF 1:/# (range_cat (t - k)) ~-1:/# pmap_cat map_cat nth_cat ifF.
  - rewrite size_map pfl_r_size_min ~-1:/# /lpathst.
    rewrite b2i0_eq 1:/# /= hw_rev {2}(_ : t = size (int2bs t lidxo)).  
    - by rewrite BS2Int.size_int2bs /#.
    rewrite -rev_drop ?BS2Int.size_int2bs ~-1:/#.
    rewrite hw_rev -{1}[int2bs _ _](cat_take_drop k) hw_cat.
    admit.
  admit.

have ?: last false (lpathst lidxo t).
- by rewrite lpE last_cat /= last_nseq 1:/#.

congr; congr.

- rewrite /si_oB2 /si /stack_increment /= -if_neg ltrNge /= ifT 1:/#.
  rewrite nth_cat sz_tk 1:/# ifT 1:/# nth_take ~-1:/# -/s.
  admit.

- rewrite /si_oB1 /si /stack_increment /= -if_neg ltrNge /= ifT 1:/#.
  rewrite nth_cat sz_tk 1:/# ifF 1:/# /= -/s.
  rewrite szs; case _: (offset = _) => /=.
  - move=> offE; rewrite take_oversize.
    - by rewrite size_lpath_lt ~-1:/# //.
    rewrite /node_from_path ifT 1:size_lpath_lt ~-1:/#.
    pose bt := list2tree _; pose lf := leafnode_from_idx _ _ _ _.
    suff ->: bt = Leaf lf by done.
    have lvlE: lvl = 0.
    - rewrite /lvl offE /= -szs nth_last /s /stack_from_leaf.
      rewrite /paths_from_leaf ifF 1:/# pmap_map.
      rewrite (range_cat (t - 1)) ~-1:/# -map_comp /(\o).
      rewrite map_cat filter_cat (rangeS (t - 1)) /=.
      rewrite /extract_path (_ : nth false _ _ = true) /=.
      - by rewrite -{2}[t](size_lpathst_lt lidxo) ~-1:/# nth_last /#.
      rewrite /predC1 /= map_cat /= last_cat /=.
      rewrite size_rcons size_take_condle ~-1:/#.
      by rewrite size_lpathst_lt /#.
    rewrite /bt /lfp_nps lvlE expr0 /= mkseq1 /= list2tree1 /lf /nps.
    do 2! congr; rewrite lvlE /=.
    rewrite {2}/lpath revK b2i0_eq 1:/# /= int2bsK ~-1:/#.
    rewrite /lpath rev_take.
    - by rewrite size_rev b2i0_eq 1:/# /= size_int2bs /#.
    rewrite size_rev b2i0_eq 1:/# /= size_int2bs ler_maxr ~-1:/#.
    rewrite (_ : h - (h - 1) = 1) 1:#ring revK int2bs_cons /= ~-1:/#.
    rewrite drop0 int2bsK 1:/#.
    - by split => [/#|_]; rewrite ltz_divLR // -exprSr /#.
    suff <-: (start + lidxo) %% 2 = 1 by smt().
    
    admit.

  - move=> ?.
    have -> /=: (nth witness s (offset - 1)).`2 = lvl - 1.
    - rewrite /s /stack_from_leaf. admit.
    have ?: 0 < lvl by admit.
    rewrite /node_from_path ifF.
    - by rewrite size_take_condle 1:/# size_lpath_lt /#.
    rewrite ifT /=; first by rewrite size_take_condle ?size_lpath_lt /#.
    rewrite size_take_condle 1:/# size_lpath_lt 1:/# ifT 1:/#.
    rewrite (_ : h - (h - lvl) = lvl) 1:#ring; congr; first do 2! congr.
    - admit.

    - admit.


admitted.


module WOTS_Encode = {
  proc encode(m : W8.t list) : int list = {
    var msg, csum, csum_32, len_2_bytes, csum_bytes, csum_base_w;

    (* Convert message to base w *)
    msg <@ Top.BaseW.BaseW.base_w(m, len1);

    (* Compute checksum *)
    csum <@ WOTS.checksum(msg);
    csum_32 <- W32.of_int csum;

    (* Convert checksum to base w *)
    csum_32 <- csum_32 `<<` W8.of_int ( 8 - ( ( len2 * log2_w) ) %% 8 );
    len_2_bytes <- ceil( ( len2 * log2_w )%r / 8%r );

    (* msg = msg || base_w(toByte(csum_32, len_2_bytes), w, len_2); *)
    csum_bytes <- toByte csum_32 len_2_bytes;
    csum_base_w <@ Top.BaseW.BaseW.base_w(csum_bytes, len2);
    msg <- msg ++ csum_base_w;

    return msg;
  }
}.

lemma fllg2w :
  floor (log2 w%r) = log2_w.
proof. by rewrite -log2w_eq from_int_floor. qed.

lemma basew_valh _ml l:
  hoare[Top.BaseW.BaseW.base_w : arg = (_ml, l) /\ l <= (8 %/ log2_w) * size _ml /\ 0 <= l
         ==>
         res
         =
         map BS2Int.bs2int
             (mkseq (fun i => take log2_w (drop (8 - (1 + (i %% (8 %/ log2_w))) * log2_w) (W8.w2bits _ml.[i %/ (8 %/ log2_w)])))
                    l)
       ].
proof.
proc.
while (0 <= consumed <= outlen
    /\ out = consumed
    /\ size base_w = outlen
    /\ (_in = if consumed = 0 then 0 else (1 + (consumed - 1) %/ (8 %/ log2_w)))
    /\ (total = if consumed = 0 then W8.zero else nth witness X (_in - 1))
    /\ (consumed %% (8 %/ log2_w) = 0 <=> bits = 0)
    /\ (   consumed %% (8 %/ log2_w) <> 0
        <=> bits
         = 8 - (consumed %% (8 %/ log2_w)) * log2_w)
    /\ (forall i,
             0 <= i < consumed
          => nth 0 base_w i
           = to_uint ((nth witness X (i %/ (8 %/ log2_w)) `>>`
                       W8.of_int ((8 - (1 + (i %% (8 %/ log2_w))) * log2_w))) `&` W8.of_int (w - 1)))).
+ auto=> /> &0 ge0_consumed _.
  move=> bits0 bits_neq0 ih consumed_lt_outlen.
  split=> [eq0_bits | neq0_bits]; split => [/#||/#|].
  + rewrite size_put /=.
    split; 1: case (consumed{0} = 0) => eq0_cons.
    + by rewrite eq0_cons /=.
    + move/iffRL: bits0 => /(_ eq0_bits).
      by case (logw_vals) => -> /=; smt(@IntDiv).
    split; 1: by rewrite (: consumed{0} + 1 <> 0) 1:/#.
    split; 1: split.
    + move/iffRL: bits0 => /(_ eq0_bits).
      rewrite -modzDm => -> /=; rewrite modz_mod pmod_small //=.
      by case (logw_vals) => ->.
    + by rewrite fllg2w; case (logw_vals) => -> /=.
    split; 1: split; 2: smt(fllg2w logw_vals).
    + move/iffRL: bits0 => /(_ eq0_bits).
      rewrite -modzDm => -> /=.
      by rewrite modz_mod pmod_small //=; [ case (logw_vals) => -> | rewrite fllg2w].
    move=> i ge0_i ltcons1_i; rewrite nth_put 1:/#.
    case (i = consumed{0}) => [eqcons_i | neqcons_i].
    + rewrite eqcons_i /= -?log2w_eq from_int_floor /=.
      case (consumed{0} = 0) => [-> // | neq0_cons].
      move/iffRL: (bits0) => /(_ eq0_bits) => -> /=.
      have -> /#: (consumed{0} - 1) %/ (8 %/ log2_w) = consumed{0} %/ (8 %/ log2_w) - 1.
      by rewrite divzDl 1:/# divNz 1:// /=; 1: case (logw_vals) => ->.
    by rewrite ifF 2:ih /#.
  split.
  + by rewrite size_put /=.
  split; 1: case (consumed{0} = 0) => eq0_cons.
  + by move: bits0; smt(mod0z).
  + rewrite ifF 1:/#; congr.
    move/iffLR /contra: bits0 => /(_ neq0_bits) modneq0.
    rewrite {1}(edivzP consumed{0} (8 %/ log2_w)) -addzA.
    rewrite divzMDl; 1:smt(val_log2w).
    rewrite (pdiv_small (consumed{0} %% (8 %/ log2_w) - 1)) //.
    smt(val_log2w modz_cmp).
  have neq0_cons : consumed{0} <> 0 by smt(mod0z).
  rewrite neq0_cons /= ifF 1:/# /=.
  have -> /=: bits{0} = 8 - consumed{0} %% (8 %/ log2_w) * log2_w by smt().
  rewrite fllg2w; split.
  + rewrite -addzA -Ring.IntID.opprD /= -(mulzDl _ 1).
    case: ((consumed{0} + 1) %% (8 %/ log2_w) = 0)=> />.
    + rewrite -/(_ %| _) dvdzP=> - [] q.
      rewrite eq_sym -Domain.subr_eq=> <-.
      by rewrite modzMDl modNz //=; smt(logw_vals).
    move=> cns1_mod; suff rngcns: 1 <= consumed{0} %% (8 %/ log2_w) < (8 %/ log2_w) - 1.
    + smt(logw_vals).
    split => [|_]; 1: smt(modn_ge0).
    move: (cns1_mod); rewrite -modzDm /= (pmod_small 1); 1: smt(logw_vals).
    move=> cns1_modmod; suff /#: (consumed{0} %% (8 %/ log2_w) + 1) < 8 %/ log2_w.
    move: cns1_modmod; apply contraLR => /= /lezNgt.
    by elim => [| <-]; [ smt(ltz_pmod logw_vals) | rewrite modzz ].
  split.
  + rewrite -modzDm (pmod_small 1); 1:smt(logw_vals).
    split => [csneq |].
    + suff /#:
        (consumed{0} %% (8 %/ log2_w) + 1) %% (8 %/ log2_w)
        =
        consumed{0} %% (8 %/ log2_w) + 1.
      rewrite (pmod_small (_ + 1)); split => [|_]; 1: smt(modn_ge0).
      move: csneq; apply contraLR => /= /lezNgt.
      by elim => [| <-]; [ smt(ltz_pmod logw_vals) | rewrite modzz ].
    apply contraLR => /=.
    rewrite -{2}(modz_mod consumed{0}).
    rewrite {2}(: consumed{0} %% (8 %/ log2_w) = consumed{0} %% (8 %/ log2_w) + 1 - 1) 1://.
    rewrite -(modzDm _ (- 1)) => -> /=; rewrite modz_mod.
    by rewrite modNz 1:// /=; smt(logw_vals).
  move => i ge0_i ltcons1_i.
  rewrite nth_put 1:/#.
  case (i = consumed{0}) => [eqcons_i | neqcons_i].
  + rewrite eqcons_i /=.
    congr; congr; congr; 2:smt().
    congr.
    rewrite {1}(edivzP (consumed{0}) (8 %/ log2_w)).
    rewrite -addzA divzMDl.
    + smt(val_log2w).
    rewrite (pdiv_small (consumed{0} %% (8%/ log2_w) - 1)) //.
    smt(val_log2w modz_cmp).
  by rewrite ih /#.
auto=> /> szml ge0_l; split.
+ by rewrite size_nseq /#.
move=> bw _ c /lezNgt l_ge_c _ c_ge_l sbw_l _ _.
have ->> {l_ge_c c_ge_l}: c = l by smt().
move=> inv.
apply: (eq_from_nth 0).
+ by rewrite sbw_l size_map size_mkseq lez_maxr.
move=> i; rewrite sbw_l => i_bnd.
rewrite (nth_map witness 0) 1:size_mkseq 1:lez_maxr 1,2://.
rewrite nth_mkseq 1:// /= inv 1://.
rewrite /to_uint /(`>>`) /bs2int size_take 2:size_drop 3:?size_w2bits 3:lez_maxr; 1..3: smt(logw_vals).
(* have geql2w : log2_w <= 8 - log2_w * i %% (8 %/ log2_w) by smt(logw_vals). *)
have geql2w : log2_w <= 8 - (8 - (1 + i %% (8 %/ log2_w)) * log2_w) by smt(logw_vals).
pose ifte := if _ then _ else _; rewrite (: ifte = log2_w) 1:/#.
rewrite (StdBigop.Bigint.BIA.big_cat_int log2_w 0 8); 1,2:smt(logw_vals).
rewrite (StdBigop.Bigint.BIA.big1_seq _ _ (range log2_w 8)) 2:/=.
+ move=> j -[_ /mem_range rngj] /=.
  rewrite (: ! (W8.of_int (w - 1)).[j]) /= 2://.
  rewrite /w (: log2_w = max 0 log2_w) 2:W8.masklsbE; 1,2: smt(logw_vals).
apply StdBigop.Bigint.BIA.eq_big_int => j rngj /=; congr; congr.
rewrite (: 0 <= j < 8) 2:/= 2:(: (W8.of_int (w - 1)).[j]) /=; 1:smt(logw_vals).
+ rewrite /w (: log2_w = max 0 log2_w) 2:W8.masklsbE; 1,2: smt(logw_vals).
rewrite nth_take 1,2:/# nth_drop 2:/#; 1: smt(logw_vals).
rewrite /w2bits nth_mkseq 2:/=; 1:smt(logw_vals).
rewrite (nth_change_dfl witness W8.zero).
+ smt(@IntDiv).
by congr; smt(logw_vals).
qed.

lemma basew_val _ml l:
  phoare[Top.BaseW.BaseW.base_w : arg = (_ml, l) /\ l <= (8 %/ log2_w) * size _ml /\ 0 <= l
         ==>
         res = map
                 BS2Int.bs2int
                 (mkseq (fun i => take log2_w
                                    (drop (8 - (1 + (i %% (8 %/ log2_w))) * log2_w)
                                      (W8.w2bits _ml.[i %/ (8 %/ log2_w)]))) l) ] = 1%r.
proof.
conseq (: 0 <= outlen ==> true) (basew_valh _ml l)=> //.
proc.
while (0 <= consumed <= outlen) (outlen - consumed).
+ by auto=> /> /#.
by auto=> /> /#.
qed.

(* From local conversions to global conversion *)
lemma basew_eq _ml l:
     0 <= l <= (8 %/ log2_w) * size _ml
  => map bs2int (mkseq (fun i=> take log2_w (drop (8 - (1 + (i %% (8 %/ log2_w))) * log2_w)
                                                  (W8.w2bits _ml.[i %/ (8 %/ log2_w)]))) l)
   = map bs2int (mkseq (fun i=> take log2_w (drop ((i %/ (8 %/ log2_w)) * 8 + (8 - (1 + (i %% (8 %/ log2_w))) * log2_w)) (BytesToBits _ml))) l).
proof.
move=> l_bnd; congr; apply: eq_in_mkseq.
move=> i i_bnd /=.
apply: (eq_from_nth witness).
+ rewrite !size_take 1,2:#smt:(logw_vals).
  rewrite !size_drop 1,2:#smt:(logw_vals).
  rewrite /w2bits /BytesToBits /mkseq //=.
  rewrite size_map size_iota /max (size_flatten_ctt 8) /=.
  + by move=> x /mapP [].
  by rewrite size_map; smt(logw_vals).
rewrite !size_take 1:#smt:(logw_vals).
rewrite !size_drop 1:#smt:(logw_vals).
move=> j.
rewrite size_w2bits /= lez_maxr; 1: smt(logw_vals).
have gelg2w : log2_w <= 8 - (8 - (1 + i %% (8 %/ log2_w)) * log2_w) by smt(logw_vals).
pose ifte := if _ then _ else _; have ->: ifte = log2_w by smt(logw_vals).
move=> j_bnd.
rewrite nth_take 1,2:#smt:(logw_vals).
rewrite nth_take 1,2:#smt:(logw_vals).
rewrite nth_drop 1,2:#smt:(logw_vals).
rewrite nth_drop 1,2:#smt:(logw_vals).
rewrite /BytesToBits (BitChunking.nth_flatten witness 8).
+ by rewrite allP=> x /mapP [] />.
rewrite (nth_map witness) 1:/#.
rewrite (nth_change_dfl W8.zero witness) 1:/#.
congr; 1: congr.
+ by rewrite -addrA divzDl 1:dvdz_mull 1:// mulzK 1:// (pdiv_small (_ + j)); 1:smt(logw_vals).
by rewrite -(modzDm _ j) -(modzDm (i %/ (8 %/ log2_w) * 8)) modzMl /= modz_mod ?(pmod_small _ 8); smt(logw_vals).
qed.

lemma WOTSchecksum_len1valh _ml :
  hoare[WOTS.checksum : arg = _ml /\ size _ml = len1
         ==>
         res = StdBigop.Bigint.BIA.big predT (fun (i : int) => w - 1 - i) _ml].
proof.
proc.
while (   #pre
       /\ 0 <= i <= len1
       /\ checksum = StdBigop.Bigint.BIA.big predT (fun (i : int) => w - 1 - i) (take i _ml)).
+ auto => &1 /> *.
  split => [/#|].
  by rewrite (take_nth witness) 1:/# StdBigop.Bigint.BIA.big_rcons ifT 1:// /#.
auto => &1 /> ?.
rewrite ge0_len1 take0 StdBigop.Bigint.BIA.big_nil /= => j.
by move=> *; rewrite take_oversize 1:/#.
qed.

lemma WOTSchecksum_ll : islossless WOTS.checksum.
proof.
proc.
by while (true) (len1 - i); auto => /#.
qed.

lemma WOTSchecksum_len1val _ml :
  phoare[WOTS.checksum : arg = _ml /\ size _ml = len1
         ==>
         res = StdBigop.Bigint.BIA.big predT (fun (i : int) => w - 1 - i) _ml] = 1%r.
proof. by conseq WOTSchecksum_ll (WOTSchecksum_len1valh _ml). qed.

lemma ge0_cln2lg2w :
  0 <= ceil ((len2 * log2_w)%r / 8%r).
proof.
rewrite /i /len2 /len1 /w; case logw_vals => -> /=.
+ rewrite /log2 (: 4%r = 2%r ^ 2); 1:smt(@RField).
  rewrite eqi_log22i 1:// -(fromint_div (8 * n)) 1:dvdz_mulr 1://.
  rewrite (Ring.IntID.mulrC 8) divMr 1:// /=.
  pose flr := floor _.
  rewrite -le_fromint &(StdOrder.RealOrder.ler_trans _ _ _ _ (ceil_ge (((flr + 1) * 2)%r / 8%r))).
  rewrite StdOrder.RealOrder.ler_pdivl_mulr 1:// /= le_fromint mulr_ge0 // addr_ge0 2://.
  rewrite (: 0 = floor 0%r) 1:// 1:from_int_floor 1://.
  rewrite floor_mono StdOrder.RealOrder.ler_pdivl_mulr 1:// /=.
  rewrite log_ge0 1:// fromintM -StdOrder.RealOrder.ler_pdivr_mulr 1://.
  rewrite (StdOrder.RealOrder.ler_trans 1%r) 1:StdOrder.RealOrder.ler_pdivr_mulr 1,2://.
  by rewrite (StdOrder.RealOrder.ler_trans (n * 4)%r) 1:le_fromint 2:ceil_ge; 1:smt(ge1_n).
rewrite /log2 (: 16%r = 2%r ^ (2 + 2)) 1:RField.exprD_nneg 1,2://; 1:smt(@RField).
rewrite /= eqi_log22i 1:// -(fromint_div (8 * n)) 1:dvdz_mulr 1://.
rewrite (Ring.IntID.mulrC 8) divMr 1:// /=.
pose flr := floor _.
rewrite -le_fromint &(StdOrder.RealOrder.ler_trans _ _ _ _ (ceil_ge (((flr + 1) * 4)%r / 8%r))).
rewrite StdOrder.RealOrder.ler_pdivl_mulr 1:// /= le_fromint mulr_ge0 // addr_ge0 2://.
rewrite (: 0 = floor 0%r) 1:// 1:from_int_floor 1://.
rewrite floor_mono StdOrder.RealOrder.ler_pdivl_mulr 1:// /=.
rewrite log_ge0 1:// fromintM -StdOrder.RealOrder.ler_pdivr_mulr 1://.
rewrite (StdOrder.RealOrder.ler_trans 1%r) 1:StdOrder.RealOrder.ler_pdivr_mulr 1,2://.
by rewrite (StdOrder.RealOrder.ler_trans (n * 2)%r) 1:le_fromint 2:ceil_ge; 1:smt(ge1_n).
qed.

(*
  The Jasmin Word library interprets the bytes as little-endian,
  meaning that the lower indices of the list represent least
  significant bits, influencing interpretation of operations such
  as bit-shifting. For example, given a byte
  b_0;b_1;b_2;b_3;b_4;b_5;b_6;b_7, a right shift (`>>>` operator)
  by say 2 results in b_2;b_3;b_4;b_5;b_6;b_7;0;0, so 0 bits are inserted
  on the high end of the list, not the low end.
*)
lemma basew_encoded_int_inner (_ml : W8.t list) l :
  0 <= l
  =>
  (mkseq (fun i => take log2_w
          (drop (8 - (1 + (i %% (8 %/ log2_w))) * log2_w)
           (W8.w2bits _ml.[i %/ (8 %/ log2_w)]))) l)
  =
  (mkseq (fun i =>
          (rev (take log2_w
                (drop (i %% (8 %/ log2_w) * log2_w)
                 (rev (W8.w2bits _ml.[i %/ (8 %/ log2_w)])))))) l).
proof.
move=> ge0_l.
apply (eq_from_nth witness); rewrite ?size_mkseq 1://.
rewrite lez_maxr 1:// => i rng_i.
rewrite ?nth_mkseq 1,2:// /=.
rewrite -{1}(revK (W8.w2bits _)).
rewrite {1}(: 8 = size (rev (w2bits _ml.[i %/ (8 %/ log2_w)]))) 1:size_rev 1:size_w2bits 1://.
rewrite -rev_take 1:size_rev 1:size_w2bits; 1:smt(logw_vals).
apply (eq_from_nth witness).
+ rewrite size_rev ?size_take ?size_rev ?size_take ?size_rev; 1..3:smt(logw_vals).
  by rewrite ?size_drop ?size_rev ?size_w2bits; smt(logw_vals).
move => j.
rewrite ?size_take ?size_rev ?size_take ?size_rev ?size_w2bits; 1,2: smt(logw_vals).
pose ifte0 := if _ then _ else _; rewrite (: ifte0 = log2_w); 1: by smt(logw_vals).
move=> rng_j.
rewrite nth_take ?nth_rev ?size_take ?size_rev ?size_w2bits ?size_drop ?size_rev ?size_w2bits; 1..10: smt(logw_vals).
rewrite ?nth_take; 1..4:smt(logw_vals).
rewrite ?nth_drop ?nth_rev; 1..4:smt(logw_vals).
by congr; rewrite size_w2bits; smt(logw_vals).
qed.


lemma take_drop_flatten_nth_ctt (n : int) (i j : int) (s : 'a list list) :
  0 < n =>
  0 <= i <= n - j %% n =>
  0 <= j =>
  (forall (x : 'a list), x \in s => size x = n) =>
  take i (drop j (flatten s)) = take i (drop (j %% n) (nth [] s (j %/ n))).
proof.
elim: s n i j.
+ move=> n i j rngi _.
  by rewrite flatten_nil.
move=> x s ih n i j gt0_n rng_i ge0_j /= szin.
rewrite flatten_cons.
rewrite drop_cat (: size x = n) 1:/#.
case (j < n) => [ltn_j | /lezNgt gen_j].
+ rewrite ifT 1:pdiv_small 1,2://.
  move: rng_i; rewrite pmod_small 1:// => rng_i.
  rewrite take_cat size_drop 1:/# lez_maxr 1:/#.
  have [-> | eqiszx] //=: i <= size x - j by smt(@IntDiv).
  by rewrite -eqiszx take0 /= cats0 take_oversize 1:size_drop /#.
rewrite ifF; 1: smt(@IntDiv).
rewrite (ih n i (j - n)); 1..4: smt(@IntDiv).
congr; congr; 1: smt(@IntDiv).
congr; rewrite divzDr 1:dvdzN 1:dvdzz divNz; 1,2: smt(@IntDiv).
by rewrite (pdiv_small (n - 1)); 1:smt(@IntDiv).
qed.

lemma basew_encoded_int_exact (_ml : W8.t list) l :
     0 <= l
  => l = (8 %/ log2_w) * size _ml
  =>
  map bs2int
  (mkseq (fun i =>
          (rev (take log2_w
                (drop (i %% (8 %/ log2_w) * log2_w)
                 (rev (W8.w2bits _ml.[i %/ (8 %/ log2_w)])))))) l)
  =
  map BaseW.val (int2lbw l (bs2int (flatten (rev (map W8.w2bits _ml))))).
proof.
move=> ge0_l eq_l.
rewrite ?map_mkseq /(\o).
apply eq_in_mkseq => i rng_i /=.
rewrite BaseW.insubdK.
+ by rewrite ltz_pmod 2:modz_ge0; 1,2: smt(w_vals).
rewrite /w -exprM bs2int_div.
+ rewrite mulr_ge0; smt(logw_vals).
rewrite bs2int_mod; 1:smt(logw_vals).
congr.
rewrite rev_take.
+ rewrite ?size_drop ?size_rev ?size_w2bits; smt(logw_vals).
rewrite size_drop ?size_rev ?size_w2bits 2:lez_maxr; 1,2:smt(logw_vals).
rewrite rev_drop ?size_rev ?size_w2bits; 1:smt(logw_vals).
rewrite revK.
rewrite (take_drop_flatten_nth_ctt 8) 1://; 1,2:smt(logw_vals).
+ by move=> x; rewrite mem_rev => /mapP [y [_ ->]]; rewrite size_w2bits.
rewrite nth_rev 1:size_map.
+ rewrite ltz_divLR 1://; smt(logw_vals).
rewrite (nth_map W8.zero) 1:size_map; 1: smt(logw_vals).
rewrite size_map.
rewrite drop_take /=; 1,2: smt(logw_vals).
have ->: (8 - i %% (8 %/ log2_w) * log2_w - (8 - i %% (8 %/ log2_w) * log2_w - log2_w)) = log2_w by smt().
rewrite eq_l.
congr.
congr.
rewrite ?mulrBr /=. rewrite mulrA.
rewrite -divMr. smt(logw_vals).
rewrite mulKz. smt(logw_vals).
rewrite -modzBm -(modzBm (8 * _)) modzMr /=.
rewrite modzNm modNz 2://. smt(logw_vals).
rewrite (pmod_small (_ - 1) 8). smt(logw_vals).
rewrite (: 8 - 1 - (log2_w - 1) = 8 - log2_w).
by ring.
rewrite mulrC -modzMmr.
have rngim8 : 0 <= i %% 8 < 8 by smt(@IntDiv).
case (i %% 8 = 0) => [eq0 | neq0].
+ have -> /=: (i %% (8 %/ log2_w)) = 0 by smt(logw_vals).
  rewrite eq0 /=; smt(logw_vals).
case (i %% 8 = 1) => [eq1 | neq1].
+ have -> /=: (i %% (8 %/ log2_w)) = 1 by smt(logw_vals).
  rewrite eq1 /=; smt(logw_vals).
case (i %% 8 = 2) => [eq2 | neq2].
+ case (logw_vals) => -> /=.
  + have -> /=: (i %% 4) = 2 by smt().
    smt().
  have -> /=: (i %% 2) = 0 by smt().
  smt().
case (i %% 8 = 3) => [eq3 | neq3].
+ case (logw_vals) => -> /=.
  + have -> /=: (i %% 4) = 3 by smt().
    smt().
  have -> /=: (i %% 2) = 1 by smt().
  smt().
case (i %% 8 = 4) => ?.
+ case (logw_vals) => -> /=.
  + have -> /=: (i %% 4) = 0 by smt().
    smt().
  have -> /=: (i %% 2) = 0 by smt().
  smt().
case (i %% 8 = 5) => ?.
+ case (logw_vals) => -> /=.
  + have -> /=: (i %% 4) = 1 by smt().
    smt().
  have -> /=: (i %% 2) = 1 by smt().
  smt().
case (i %% 8 = 6) => ?.
+ case (logw_vals) => -> /=.
  + have -> /=: (i %% 4) = 2 by smt().
    smt().
  have -> /=: (i %% 2) = 0 by smt().
  smt().
case (i %% 8 = 7) => ?.
+ case (logw_vals) => -> /=.
  + have -> /=: (i %% 4) = 3 by smt().
    smt().
  have -> /=: (i %% 2) = 1 by smt().
  smt().
+ smt().
rewrite ?mulrBr /= mulrA -divMr 2:mulKz; 1,2:smt(logw_vals).
have ->: (8 * size _ml - log2_w - log2_w * i) = 8 * size _ml - (log2_w * (i + 1)) by smt().
rewrite divzDl 1:dvdz_mulr 1:// /= mulKz 1://.
rewrite ?opprD /= ?addrA /=.
rewrite divNz // /=. smt(logw_vals).
rewrite {2}(: 8 = (8 %/ log2_w) * log2_w). smt(logw_vals).
rewrite (Ring.IntID.mulrC _ log2_w).
rewrite divz_mulp; 1,2: smt(logw_vals).
rewrite divzDl 1:dvdz_mulr; 1:smt(logw_vals).
rewrite mulKz. smt(logw_vals).
by rewrite divNz 1:// /=; smt(logw_vals).
qed.

lemma basew_encoded_int_take_div (_ml : W8.t list) l :
     0 < l
  => l < (8 %/ log2_w) * size _ml
  => (8 %/ log2_w) %| l
  =>
  map bs2int
  (mkseq (fun i =>
          (rev (take log2_w
                (drop (i %% (8 %/ log2_w) * log2_w)
                 (rev (W8.w2bits _ml.[i %/ (8 %/ log2_w)])))))) l)
  =
  map BaseW.val (int2lbw l (bs2int (flatten (rev (take (l %/ (8 %/ log2_w)) (map W8.w2bits _ml)))))).
proof.
move=> ge0_l ltmm_l dvdww_l.
have ltm_ldv: l %/ (8 %/ log2_w) < size _ml by smt(ltz_divLR logw_vals).
rewrite ?map_mkseq /(\o).
apply eq_in_mkseq => i rng_i /=.
rewrite BaseW.insubdK.
+ by rewrite ltz_pmod 2:modz_ge0; 1,2: smt(w_vals).
rewrite /w -exprM bs2int_div.
+ rewrite mulr_ge0; smt(logw_vals).
rewrite bs2int_mod; 1:smt(logw_vals).
rewrite rev_take.
+ rewrite ?size_drop ?size_rev ?size_w2bits; smt(logw_vals).
rewrite size_drop ?size_rev ?size_w2bits 2:lez_maxr; 1,2:smt(logw_vals).
rewrite rev_drop ?size_rev ?size_w2bits; 1:smt(logw_vals).
rewrite (take_drop_flatten_nth_ctt 8) 1://; 1,2:smt(logw_vals).
+ by move=> x; rewrite mem_rev => /mem_take /mapP [y [_ ->]]; rewrite size_w2bits.
have ltl1i : log2_w * (l - 1 - i) %/ 8 < l %/ (8 %/ log2_w).
+ rewrite ltz_divRL //. smt(logw_vals). smt(logw_vals).
rewrite revK nth_rev 1:size_take 2:size_map 2:ltm_ldv /=; 1: smt(logw_vals size_map).
+ by rewrite lez_divRL /#.
rewrite size_take 2:size_map 2:ltm_ldv 2:/= 2:nth_take; 1,2,3: smt(logw_vals).
rewrite (nth_map W8.zero).
+ smt().
rewrite drop_take /=; 1,2: smt(logw_vals).
have ->: (8 - i %% (8 %/ log2_w) * log2_w - (8 - i %% (8 %/ log2_w) * log2_w - log2_w)) = log2_w by smt().
congr; congr; congr.
rewrite ?mulrBr -modzDm /= -(modzDm (log2_w * l)).
move/iffLR: (dvdzE 8 (log2_w * l)) => /(_ _).
rewrite (: 8 = log2_w * (8 %/ log2_w)). smt(logw_vals).
rewrite dvdz_mul 1:dvdzz //.
move=> -> /=.
rewrite modNz //. smt(logw_vals).
case (i = 0)=> [-> /=| neq0_i].
smt(logw_vals).
rewrite modNz //. smt(logw_vals).
rewrite -modzBm /= modz_mod (pmod_small (_ - 1)).
smt(logw_vals).
rewrite opprB ?addrA /=. rewrite -(modzBm 8) /= modNz //=. smt(logw_vals).
rewrite -(modzBm _ 1) modz_mod modzBm (pmod_small (_ - 1)). smt(logw_vals).
rewrite opprB addrA /=.
rewrite -modzBm -(modzBm 15) /=.
rewrite -(modzBm _ 1) modz_mod modzBm (pmod_small log2_w).
smt(logw_vals).
move=> {neq0_i}.
rewrite /= opprB addrA /= -modzMmr.
have rngim8 : 0 <= i %% 8 < 8 by smt(@IntDiv).
case (i %% 8 = 0) => [eq0 | neq0].
+ have -> /=: (i %% (8 %/ log2_w)) = 0.
  move/dvdzP: eq0 => [q ->].
  rewrite -dvdzE dvdz_mull. smt(logw_vals).
  rewrite eq0 /=; smt(logw_vals).
case (i %% 8 = 1) => [eq1 | neq1].
+ case (logw_vals) => -> /=.
  + have -> /=: (i %% 4) = 1 by smt().
    smt().
  have -> /=: (i %% 2) = 1 by smt().
  smt().
case (i %% 8 = 2) => [eq2 | neq2].
+ case (logw_vals) => -> /=.
  + have -> /=: (i %% 4) = 2 by smt().
    smt().
  have -> /=: (i %% 2) = 0 by smt().
  smt().
case (i %% 8 = 3) => [eq3 | neq3].
+ case (logw_vals) => -> /=.
  + have -> /=: (i %% 4) = 3 by smt().
    smt().
  have -> /=: (i %% 2) = 1 by smt().
  smt().
case (i %% 8 = 4) => ?.
+ case (logw_vals) => -> /=.
  + have -> /=: (i %% 4) = 0 by smt().
    smt().
  have -> /=: (i %% 2) = 0 by smt().
  smt().
case (i %% 8 = 5) => ?.
+ case (logw_vals) => -> /=.
  + have -> /=: (i %% 4) = 1 by smt().
    smt().
  have -> /=: (i %% 2) = 1 by smt().
  smt().
case (i %% 8 = 6) => ?.
+ case (logw_vals) => -> /=.
  + have -> /=: (i %% 4) = 2 by smt().
    smt().
  have -> /=: (i %% 2) = 0 by smt().
  smt().
case (i %% 8 = 7) => ?.
+ case (logw_vals) => -> /=.
  + have -> /=: (i %% 4) = 3 by smt().
    smt().
  have -> /=: (i %% 2) = 1 by smt().
  smt().
+ smt().
congr; congr.
rewrite {3}(: 8 = (8 %/ log2_w) * log2_w). smt(logw_vals).
rewrite (Ring.IntID.mulrC _ log2_w).
rewrite divz_mulp; 1,2: smt(logw_vals).
rewrite mulKz. smt(logw_vals).
rewrite (: l - 1 - i = (l - i - 1)) 1:/#.
rewrite -divNz. smt(). smt(logw_vals).
rewrite opprB.
rewrite divzDr 1:dvdzN 1:// divNz 1://.
smt(logw_vals).
by rewrite divzDl 1:// divNz 1:// /=; smt(logw_vals).
qed.

lemma basew_encoded_int_drop_gen (_ml : W8.t list) l :
     0 <= l
  => l <= (8 %/ log2_w) * size _ml
  =>
  map bs2int
  (mkseq (fun i =>
          (rev (take log2_w
                (drop (i %% (8 %/ log2_w) * log2_w)
                 (rev (W8.w2bits _ml.[i %/ (8 %/ log2_w)])))))) l)
  =
  map BaseW.val (int2lbw l (bs2int (drop (size _ml * 8 - l * log2_w) (flatten (rev (map W8.w2bits _ml)))))).
proof.
move=> ge0_l ^ lemm_l.
case => [ltmml | eqmml]; last first.
+ have ->: (size _ml * 8 - l * log2_w) = 0.
  + by rewrite eqmml; smt(logw_vals).
  by rewrite drop0 basew_encoded_int_exact.
have ltm_ldv: l %/ (8 %/ log2_w) < size _ml by smt(ltz_divLR logw_vals).
rewrite ?map_mkseq /(\o).
apply eq_in_mkseq => i rng_i /=.
rewrite BaseW.insubdK.
+ by rewrite ltz_pmod 2:modz_ge0; 1,2: smt(w_vals).
rewrite /w -exprM bs2int_div.
+ rewrite mulr_ge0; smt(logw_vals).
rewrite bs2int_mod; 1:smt(logw_vals).
rewrite drop_drop. smt(logw_vals). smt(logw_vals).
rewrite rev_take.
+ rewrite ?size_drop ?size_rev ?size_w2bits; smt(logw_vals).
rewrite size_drop ?size_rev ?size_w2bits 2:lez_maxr; 1,2:smt(logw_vals).
rewrite rev_drop ?size_rev ?size_w2bits; 1:smt(logw_vals).
rewrite (take_drop_flatten_nth_ctt 8) 1://; 1,2:smt(logw_vals).
+ by move=> x; rewrite mem_rev => /mapP [y [_ ->]]; rewrite size_w2bits.
rewrite revK nth_rev size_map; 1: smt(logw_vals size_map).
rewrite (nth_map W8.zero). smt(logw_vals).
rewrite drop_take /=; 1,2: smt(logw_vals).
have ->: (8 - i %% (8 %/ log2_w) * log2_w - (8 - i %% (8 %/ log2_w) * log2_w - log2_w)) = log2_w by smt().
congr; congr; congr.
rewrite ?mulrBr addrA /=.
have ->:
  (log2_w * l - log2_w * 1 - log2_w * i + size _ml * 8 - l * log2_w)
  =
  8 * size _ml - (i + 1) * log2_w.
smt().
rewrite -modzBm modzMr /=.
rewrite -modzMml -modzDml.
have rngim8 : 0 <= i %% 8 < 8 by smt(@IntDiv).
case (i %% 8 = 0) => [eq0 | neq0].
+ have -> /=: (i %% (8 %/ log2_w)) = 0.
  move/dvdzP: eq0 => [q ->].
  rewrite -dvdzE dvdz_mull. smt(logw_vals).
  rewrite eq0 /=; smt(logw_vals).
case (i %% 8 = 1) => [eq1 | neq1].
+ case (logw_vals) => -> /=.
  + have -> /=: (i %% 4) = 1 by smt().
    smt().
  have -> /=: (i %% 2) = 1 by smt().
  smt().
case (i %% 8 = 2) => [eq2 | neq2].
+ case (logw_vals) => -> /=.
  + have -> /=: (i %% 4) = 2 by smt().
    smt().
  have -> /=: (i %% 2) = 0 by smt().
  smt().
case (i %% 8 = 3) => [eq3 | neq3].
+ case (logw_vals) => -> /=.
  + have -> /=: (i %% 4) = 3 by smt().
    smt().
  have -> /=: (i %% 2) = 1 by smt().
  smt().
case (i %% 8 = 4) => ?.
+ case (logw_vals) => -> /=.
  + have -> /=: (i %% 4) = 0 by smt().
    smt().
  have -> /=: (i %% 2) = 0 by smt().
  smt().
case (i %% 8 = 5) => ?.
+ case (logw_vals) => -> /=.
  + have -> /=: (i %% 4) = 1 by smt().
    smt().
  have -> /=: (i %% 2) = 1 by smt().
  smt().
case (i %% 8 = 6) => ?.
+ case (logw_vals) => -> /=.
  + have -> /=: (i %% 4) = 2 by smt().
    smt().
  have -> /=: (i %% 2) = 0 by smt().
  smt().
case (i %% 8 = 7) => ?.
+ case (logw_vals) => -> /=.
  + have -> /=: (i %% 4) = 3 by smt().
    smt().
  have -> /=: (i %% 2) = 1 by smt().
  smt().
+ smt().
congr; congr.
rewrite ?mulrBr addrA.
have ->:
  (log2_w * l - log2_w * 1 - log2_w * i + size _ml * 8 - l * log2_w)
  =
  8 * size _ml - (i + 1) * log2_w.
+ smt().
rewrite divzDl 1:dvdz_mulr 1:// mulKz 1://.
rewrite {2}(: 8 = log2_w * (8 %/ log2_w)). smt(logw_vals).
rewrite divz_mulp; 1,2: smt(logw_vals).
rewrite (: - (i + 1) * log2_w = (- (i + 1)) * log2_w) 1:/#.
rewrite mulzK; 1: smt(logw_vals).
rewrite divNz 1:/#. smt(logw_vals).
simplify. smt().
qed.

lemma basew_val_int2lbw_len1 _ml l:
  phoare[Top.BaseW.BaseW.base_w : arg = (_ml, l) /\ l = (8 %/ log2_w) * size _ml /\ 0 <= l
         ==>
         res
         =
         map BaseW.val (int2lbw l (bs2int (flatten (rev (map W8.w2bits _ml))))) ] = 1%r.
proof.
conseq (basew_val _ml l) => /> *.
by rewrite ?basew_encoded_int_inner 1,2:// ?basew_encoded_int_exact 1://.
qed.

lemma basew_val_int2lbw_len1h _ml l:
  hoare[Top.BaseW.BaseW.base_w : arg = (_ml, l) /\ l = (8 %/ log2_w) * size _ml /\ 0 <= l
         ==>
         res
         =
         map BaseW.val (int2lbw l (bs2int (flatten (rev (map W8.w2bits _ml))))) ].
proof.
conseq (basew_val _ml l) => /> *.
by rewrite ?basew_encoded_int_inner 1,2:// ?basew_encoded_int_exact 1://.
qed.

lemma basew_val_int2lbw_len2 _ml l:
  phoare[Top.BaseW.BaseW.base_w : arg = (_ml, l) /\ l <= (8 %/ log2_w) * size _ml /\ 0 <= l
         ==>
         res
         =
         map BaseW.val (int2lbw l (bs2int (drop (size _ml * 8 - l * log2_w) (flatten (rev (map W8.w2bits _ml)))))) ] = 1%r.
proof.
conseq (basew_val _ml l) => /> *.
by rewrite ?basew_encoded_int_inner 1,2:// ?basew_encoded_int_drop_gen.
qed.

lemma basew_val_int2lbw_len2h _ml l:
  hoare[Top.BaseW.BaseW.base_w : arg = (_ml, l) /\ l <= (8 %/ log2_w) * size _ml /\ 0 <= l
         ==>
         res
         =
         map BaseW.val (int2lbw l (bs2int (drop (size _ml * 8 - l * log2_w) (flatten (rev (map W8.w2bits _ml)))))) ].
proof.
conseq (basew_val _ml l) => /> *.
by rewrite ?basew_encoded_int_inner 1,2:// ?basew_encoded_int_drop_gen.
qed.

lemma len2_ge8lw_rel :
  len2 <= 8 %/ log2_w * ceil ((len2 * log2_w)%r / 8%r).
proof.
case (8 %/ log2_w %| len2) => dvdln2.
+ rewrite mulrC -lez_divLR 2://; 1: smt(logw_vals).
  rewrite -le_fromint (RealOrder.ler_trans ((len2 * log2_w)%r / 8%r)).
  + by rewrite fromint_div // fromintM fromint_div /=; smt(logw_vals).
  smt(ceil_ge).
rewrite lez_eqVlt; right; rewrite mulrC -ltz_divLR.
+ smt(logw_vals).
rewrite -lt_fromint (RealOrder.ltr_le_trans ((len2 * log2_w)%r / 8%r)).
+ move: (edivzP len2 (8 %/ log2_w)) => [deflen2 _].
  rewrite {2}deflen2 mulrDl.
  have ->:
    len2 %/ (8 %/ log2_w) * (8 %/ log2_w) * log2_w
    =
    len2 %/ (8 %/ log2_w) * 8.
    by smt(logw_vals).
rewrite ?fromintD ?fromintM RField.mulrDl /= RField.mulrK 1://.
suff /#:
  0%r < (len2 %% (8 %/ log2_w))%r * log2_w%r / 8%r.
rewrite RealOrder.divr_gt0 1:RealOrder.mulr_gt0 3://; 2: smt(logw_vals).
rewrite lt_fromint; move: dvdln2 (modz_ge0 len2 (8 %/ log2_w) _); 1: smt(logw_vals).
by rewrite dvdzE lez_eqVlt eq_sym => ->.
apply ceil_ge.
qed.

lemma from_int_ceil_addl x r:
  ceil (x%r + r) = x + ceil r.
proof. smt(@Real). qed.

lemma len1P:
  len1 = 8 * n %/ log2_w.
proof.
rewrite /len1 {1}(edivzP (8 * n) (log2_w)) fromintD RField.mulrDl.
rewrite log2_wP -fromint_div 1:/(%|) 1:modzMl // mulzK.
+ by case: val_log2w=> [|[]] ->.
rewrite from_int_ceil_addl.
have -> //=: 8 * n %% log2_w = 0.
+ smt(val_log2w).
by rewrite from_int_ceil.
qed.

lemma logV x y:
     0%r < y
  => log x (inv y) = -log x y.
proof. by move=> gt0_y; rewrite /log lnV // RField.mulNr. qed.

lemma logb_log b1 b2 x:
     0%r < b1
  => b1 <> 1%r
  => log b1 x / log b1 b2 = log b2 x.
proof.
move=> ge0_b1 b1_neq1; rewrite /log RField.invf_div RField.mulrA -(RField.mulrA _ (inv (ln b1))).
by rewrite RField.mulVf // ln_eq0.
qed.

lemma Sfloor_ceil (x : real):
  !isint x <=> floor x + 1 = ceil x.
proof. by rewrite -cBf_eq1P /#. qed.

lemma isint_logP (b x : real):
     1%r < b
  => 1%r <= x
  => (isint (log b x) <=> exists (n : int), 0 <= n /\ x = b ^ n).
proof.
move=> gt1_b ge1_x.
rewrite /isint; apply: exists_iff=> /= n; split; last first.
+ by move=> [] ge0_n ->; rewrite -rpow_nat 1,2:/# logK /#.
move=> nP; rewrite andaP.
+ by rewrite -le_fromint -nP log_ge0 1,2:/#.
move: nP=> + ge0_n - /(congr1 (fun (x : real)=> b ^ x))=> /=.
by rewrite rpowK 1..3:/# rpow_nat //#.
qed.

lemma len1P':
  len1 = (8 %/ log2_w) * n.
proof. smt(len1P val_log2w). qed.

lemma len2bits_lt_32:
     n < 2 ^ (30 - 2 * log2_w)
  => len2 * log2_w < 32.
proof.
move=> n_bound.
rewrite /len2 /log2 fromintM logM.
+ smt(g2_len1).
+ smt(w_vals).
rewrite RField.mulrDl len1P' fromintM logM.
+ smt(val_log2w).
+ smt(ge4_n).
rewrite RField.mulrDl RField.addrAC -RField.mulrDl -logM.
+ smt(val_log2w).
+ smt(w_vals).
rewrite addzC -from_int_floor_addl RField.addrA -(RField.mulrV (log 2%r w%r)).
+ by rewrite -/(log2 _) -log2w_eq; smt(val_log2w).
rewrite -RField.mulrDl -logM.
+ smt(w_vals).
+ smt(val_log2w w_vals).
have bounded_error: log 2%r (w%r * (8 %/ log2_w)%r * (w - 1)%r) < (if log2_w = 2 then 6 else 9)%r.
+ rewrite -(RealExp.logK 2%r (if log2_w = 2 then 6 else 9)%r) 1,2:#smt:(w_vals).
  rewrite rpow_nat 1:/# // RField.fromintXn 1:/#.
  rewrite log_mono_ltr // 1:#smt:(w_vals val_log2w).
  + by rewrite lt_fromint expr_gt0 //.
  by rewrite /w; case: (w_vals)=> [/val_w_log2|/val_w_log4] -> //.
rewrite -lt_fromint.
move: n_bound; rewrite -lt_fromint -(RealExp.log_mono_ltr 2%r) //.
+ smt(ge4_n).
+ smt(expr_gt0).
rewrite -RField.fromintXn 1:#smt:(val_log2w).
rewrite -rpow_nat 1:#smt:(val_log2w) //.
rewrite logK // -!/(log2 _) -log2w_eq=> n_bound.
apply: (RealOrder.ltr_le_trans ((2%r + (32 - 2 * log2_w)%r / log2_w%r) * log2_w%r)); last first.
+ smt().
rewrite RField.mulrDl -(RField.mulrA _ (inv log2_w%r)) (RField.mulrC (inv log2_w%r)) RField.mulrV /=.
+ smt(val_log2w).
rewrite -!fromintM -!fromintD lt_fromint //=.
case: (w_vals).
+ move=> /val_w_log2 log2_wP; move: n_bound bounded_error; rewrite /log2 /w log2_wP /=.
  smt(@Real).
+ move=> /val_w_log4 log2_wP; move: n_bound bounded_error; rewrite /log2 /w log2_wP /=.
  smt(@Real).
qed.

lemma logX (b x y):
     0%r < b
  => b <> 1%r
  => 0%r < x
  => log b (x ^ y) = y * log b x.
proof.
move=> gt0_b b_neq1 gt0_xXy; apply: (inj_rexpr b)=> //.
by rewrite rpowK // 1:rpow_gt0 // RField.mulrC rpowM // rpowK.
qed.

lemma log2_wXlen2_div8_le4:
     n < 2 ^ (30 - 2 * log2_w)
  => ceil ((len2 * log2_w)%r / 8%r) <= 4.
proof.
move=> n_lt_2X32.
suff: (len2 * log2_w)%r / 8%r <= 4%r.
+ smt(@Real).
rewrite fromintM -RField.mulrA RField.mulrC -RealOrder.ler_pdivl_mull.
+ by apply: RealOrder.mulr_gt0; [1:smt(val_log2w)|2:rewrite RealOrder.invr_gt0 //].
rewrite RField.invf_div RField.mulrAC /=.
smt(val_log2w len2bits_lt_32).
qed.

lemma nondiv_ceil:
     !8 %| len2 * log2_w
  => ceil ((len2 * log2_w)%r / 8%r) * 8 = (len2 * log2_w %/ 8) * 8 + 8.
proof.
rewrite /(%|)=> mod_nz; rewrite {1}(edivzP (len2 * log2_w) 8).
rewrite fromintD fromintM RField.mulrDl -RField.mulrA RField.mulrV //=.
by rewrite from_int_ceil_addl; smt(@Real).
qed.

(** FD: is this acceptable in practice? **)
(** TODO: Move this somewhere sensible once refined to final value **)
axiom n_lt_2X32: n < 2 ^ (30 - 2 * log2_w).
axiom divisibility_condition: !8 %| len2 * log2_w.

lemma WOTSEncodeP _ml :
  phoare[WOTS_Encode.encode : arg = _ml /\ len1 = (8 %/ log2_w) * size _ml
         ==>
         res
         =
         map BaseW.val (encode_int Params.len1 (BS2Int.bs2int (flatten (rev (map W8.w2bits _ml)))) Params.len2) ]= 1%r.
proof.
proc.
(* Treat the base W encoded message and the base W encoded checksum as separate lists of base W digits *)
wp; conseq (: msg = map BaseW.val (int2lbw len1 (bs2int (flatten (rev (map W8.w2bits _ml)))))
           /\ csum_base_w = map BaseW.val (checksum len1 (bs2int (flatten (rev (map W8.w2bits _ml)))) len2))
           (: _ ==> size msg = len1)=> //.
+ move=> &0 _ cs ms; rewrite map_cat //=; split=> />.
  + move=> + sms_len1; apply: eqseq_cat.
    + by rewrite size_map size_int2lbw 1:ge0_len1 1:bs2int_ge0.
+ seq 1: (size msg = len1); 2:by conseq (: true).
  inline *; wp; while (size base_w = outlen).
  + by auto=> /> &0 _; rewrite !size_put.
  by auto; rewrite size_nseq #smt:(ge0_len1).
seq 1 : (   #pre
         /\ msg
            =
            map BaseW.val (int2lbw len1 (bs2int (flatten (rev (map W8.w2bits _ml)))))) => //; last first.
+ hoare => /=.
  call(basew_val_int2lbw_len1h _ml len1).
  by auto=> />; smt(ge0_len1).
+ call (basew_val_int2lbw_len1 _ml len1).
  by skip => /> eql1; rewrite ge0_len1.
(* We try to keep things intelligible by separating the mathematical
   aspects of the checksum from representation-related issues *)
conseq (: csum_base_w = map BaseW.val (checksum len1 (bw2int (map BaseW.insubd msg)) len2)).
+ auto=> /> smlP; apply: andaP=> [|->] //.
  rewrite -map_comp (eq_map (BaseW.insubd \o BaseW.val) idfun) 2:map_id.
  + by move=> x @/(\o); rewrite /BaseW.insubd BaseW.valK.
  rewrite int2lbwK 1:ge0_len1 1:bs2int_ge0 //=.
  have ->: w ^ len1 = 2 ^ size (flatten (rev (map W8.w2bits _ml))); last first.
  + exact: bs2int_le2Xs.
  rewrite (size_flatten_ctt 8).
  + by move=> x; rewrite mem_rev mapP=> - [] x0 [] _ ->; rewrite W8.size_w2bits.
  rewrite size_rev size_map smlP -eq_fromint -!RField.fromintXn 1..3:#smt:(size_ge0 val_log2w).
  rewrite -RField.exprM !RField.fromintXn 1,2:#smt:(size_ge0 val_log2w) eq_fromint.
  by congr; smt(val_log2w).
seq 1 : (   len1 = size msg
         /\ all (fun x=> 0 <= x < w) msg
         /\ csum = StdBigop.Bigint.BIA.big predT (fun (i : int) => w - 1 - i) msg) => //; last first.
+ hoare => /=.
  exlim msg => msgt; call (WOTSchecksum_len1valh msgt).
  auto => &1 /> ltszm_len1.
  rewrite size_map size_mkseq; split=> [|_]; 1:smt(ge0_len1).
  split; 1:smt(ge0_len1).
  rewrite all_map (List.eq_all _ predT) 2:all_predT.
  by move=> x @/predT @/preim /=; exact:BaseW.valP.
+ exlim msg => msgt; call (WOTSchecksum_len1val msgt).
  auto=> &1 />; rewrite size_map size_mkseq=> _.
  split=> [|_]; 1:smt(ge0_len1).
  split; 1:smt(ge0_len1).
  rewrite all_map (List.eq_all _ predT) 2:all_predT.
  by move=> x @/predT @/preim /=; exact:BaseW.valP.
sp; exlim csum, csum_bytes=> cs csb.
call (: arg = (csb, len2)
     /\ bs2int (drop (size csb * 8 - len2 * log2_w) (flatten (rev (map W8.w2bits arg.`1)))) = cs
     /\ len2 <= 8 %/ log2_w * size arg.`1
     ==> res = map BaseW.val (int2lbw len2 cs)).
+ by conseq (basew_val_int2lbw_len2 csb len2)=> />; smt(ge0_len2).
auto=> /> &0 sz_msgP msg_elemsP; split=> [|_ _]; last first.
+ congr; rewrite /checksum /=.
  have ->: len1 = size (map BaseW.insubd msg{0}).
  + by rewrite size_map.
  rewrite bw2intK /= StdBigop.Bigint.BIA.big_map /(\o) /predT -/predT.
  congr; apply: StdBigop.Bigint.BIA.eq_big_seq.
  move: msg_elemsP=> /List.allP msg_elemsP w /msg_elemsP /= w_bnd.
  by rewrite BaseW.insubdK.
split; last first.
+ by rewrite /toByte size_rev size_mkseq; smt(ge0_cln2lg2w len2_ge8lw_rel).
(* And now for the main event *)
pose csum := StdBigop.Bigint.BIA.big predT (fun i=> w - 1 - i) msg{0}.
have csum_bnd: 0 <= csum < w ^ len2.
+ rewrite /len2 /log2 logb_log //.
  split=> [|].
  + rewrite /csum; apply: StdBigop.Bigint.sumr_ge0_seq.
    by move=> a; move: msg_elemsP=> /List.allP msg_elemsP /msg_elemsP /#.
  rewrite ler_eqVlt; case=> [<-|gt0_csum].
  + by apply: expr_gt0; smt(w_vals).
  rewrite -lt_fromint -(log_mono_ltr w%r) 1,2:#smt:(w_vals).
  + by rewrite lt_fromint; apply: expr_gt0; smt(w_vals).
  rewrite -(RField.fromintXn w).
  + have: 0%r <= log w%r (len1 * (w - 1))%r by smt(log_ge0 w_vals ge1_len1).
    smt(@Real).
  rewrite -rpow_nat.
  + have: 0%r <= log w%r (len1 * (w - 1))%r by smt(log_ge0 w_vals ge1_len1).
    smt(@Real).
  + smt(w_vals).
  rewrite logK 1,2:#smt:(w_vals).
  apply: (RealOrder.ler_lt_trans (log w%r (len1 * (w - 1))%r)).
  + apply: log_mono; 1..3:smt(w_vals ge1_len1).
    move: (StdBigop.Bigint.ler_sum_seq predT (fun i=> w - 1 -i) (fun i=> w - 1) msg{0} _).
    + by move=> a; move: msg_elemsP=> /List.allP msg_elemsP /msg_elemsP /#.
    by rewrite StdBigop.Bigint.BIA.sumr_const count_predT -sz_msgP intmulz le_fromint mulzC.
  smt(@Real).
rewrite /(`<<`) shlMP; 1:by rewrite to_uint_small /#.
rewrite to_uint_small 1:/#.
rewrite {1}/toByte size_rev size_mkseq lez_maxr 1:ge0_cln2lg2w -bs2int_div.
+ by rewrite subz_ge0 (edivzP (len2 * log2_w) 8); smt(@Real @IntDiv).
rewrite -map_rev /toByte revK map_mkseq /(\o) /=.
pose WW := W32.of_int _.
rewrite (eq_in_mkseq _ (fun i=> WW.[i * 8 + 0] :: WW.[i * 8 + 1]
                             :: WW.[i * 8 + 2] :: WW.[i * 8 + 3]
                             :: WW.[i * 8 + 4] :: WW.[i * 8 + 5]
                             :: WW.[i * 8 + 6] :: WW.[i * 8 + 7] :: [])).
+ move=> i i_bnd @/w2bits @/unpack8 @/(\bits8) /=.
  rewrite /mkseq -iotaredE /=.
  rewrite !initE /=.
  by have -> //: 0 <= i < 4 by smt(log2_wXlen2_div8_le4 n_lt_2X32).
have ->: flatten (mkseq (fun i=> WW.[i * 8 + 0] :: WW.[i * 8 + 1]
                              :: WW.[i * 8 + 2] :: WW.[i * 8 + 3]
                              :: WW.[i * 8 + 4] :: WW.[i * 8 + 5]
                              :: WW.[i * 8 + 6] :: WW.[i * 8 + 7] :: [])
                        (ceil ((len2 * log2_w)%r / 8%r)))
      = mkseq (fun i=> WW.[i]) (8 * ceil ((len2 * log2_w)%r / 8%r)).
+ apply: (eq_from_nth witness).
  + rewrite size_mkseq (size_flatten_ctt 8) 2:size_mkseq 2:/#.
    by move=> bs @/mkseq /mapP.
  rewrite (size_flatten_ctt 8) 2:size_mkseq.
  + by move=> bs @/mkseq /mapP.
  move=> i i_bnd; rewrite nth_mkseq 1:/# /=.
  rewrite (BitChunking.nth_flatten witness 8).
  + by rewrite allP=> x @/mkseq /mapP.
  by rewrite nth_mkseq /#.
rewrite /WW.
have le32_8c : (8 * ceil ((len2 * log2_w)%r / 8%r)) <= 32.
+ smt(log2_wXlen2_div8_le4 n_lt_2X32).
rewrite (eq_in_mkseq _ (fun i=> (csum * 2 ^ (8 - len2 * log2_w %% 8)) %/ 2 ^ i %% 2 <> 0)).
+ move=> i i_bound /=; rewrite W32.of_intwE.
  have -> /=: 0 <= i < 32 by smt(ge0_cln2lg2w).
  rewrite /W32.int_bit (pmod_small _ W32.modulus)=> //.
  split=> [|_].
  + by rewrite mulr_ge0 1:/# expr_ge0.
  case: (csum = 0)=> [-> //|csum_neq_0].
  rewrite -lt_fromint -(log_mono_ltr 2%r) //.
  + by rewrite lt_fromint mulr_gt0 1:/# expr_gt0.
  rewrite -RField.fromintXn // -rpow_nat // logK //.
  rewrite fromintM -RField.fromintXn 1:/# -rpow_nat 1:/# //.
  rewrite logM 1:/# 1:rpow_gt0 // logK //.
  apply: (RealOrder.ltr_le_trans (len2 * log2_w + (8 - len2 * log2_w %% 8))%r).
  + rewrite !fromintD RealOrder.ltr_add2r.
    rewrite fromintM -log2_wP /log2 -logX // 1:#smt:(w_vals).
    rewrite rpow_nat 1:ge0_len2 1:#smt:(w_vals) RField.fromintXn 1:ge0_len2.
    by apply: log_mono_ltr=> //#.
  move: (len2bits_lt_32 n_lt_2X32).
  rewrite {1 2}(edivzP (len2 * log2_w) 8) le_fromint.
  have -> /#: len2 * log2_w %/ 8 * 8 + len2 * log2_w %% 8 + (8 - len2 * log2_w %% 8)
         = len2 * log2_w %/ 8 * 8 + 8.
  by ring.
rewrite -/(int2bs _ _) int2bsK.
+ by apply: mulr_ge0=> //; exact: ge0_cln2lg2w.
+ rewrite (mulzC 8) nondiv_ceil 1:divisibility_condition //.
  split=> [|_].
  + by rewrite mulr_ge0 1:/# expr_ge0.
  case: (csum = 0)=> [-> //=|csum_neq_0].
  + exact: expr_gt0.
  rewrite -lt_fromint -(log_mono_ltr 2%r) //.
  + by rewrite lt_fromint mulr_gt0 1:/# expr_gt0.
  + by rewrite lt_fromint expr_gt0 //.
  rewrite fromintM logM 1:/# 1:lt_fromint 1:expr_gt0 //.
  rewrite -RField.fromintXn // 1:/# -rpow_nat // 1:/# logK //.
  rewrite -RField.fromintXn 1:#smt:(ge0_len2 val_log2w) -rpow_nat 1:#smt:(ge0_len2 val_log2w) //.
  rewrite logK //.
  apply: (RealOrder.ltr_le_trans (len2 * log2_w + (8 - len2 * log2_w %% 8))%r); last by smt().
  rewrite !fromintD RealOrder.ltr_add2r.
  rewrite fromintM -log2_wP /log2 -logX // 1:#smt:(w_vals).
  rewrite rpow_nat 1:ge0_len2 1:#smt:(w_vals) RField.fromintXn 1:ge0_len2.
  by apply: log_mono_ltr=> //#.
rewrite nondiv_ceil 1:divisibility_condition //.
have->: len2 * log2_w %/ 8 * 8 + 8 - len2 * log2_w
      = 8 - len2 * log2_w %% 8.
+ by rewrite {2}(edivzP (len2 * log2_w) 8); ring.
by rewrite mulzK; smt(expr_gt0).
qed.

lemma chfltn_id pkw:
  chunk n (BitsToBytes (flatten (map DigestBlock.val (DBLL.val pkw))))
  =
  map BitsToBytes (map DigestBlock.val (DBLL.val pkw)).
proof.
rewrite /BitsToBytes map_mkseq /(\o) /= (size_flatten_ctt (8 * n)).
+ by move=> y /mapP [t] ->; rewrite DigestBlock.valP.
rewrite size_map DBLL.valP mulrC mulrCA mulKz 1:// -/(chunk 8).
rewrite &(eq_from_nth witness).
+ rewrite size_chunk 2:size_mkseq 2:lez_maxr 3:mulzK; 1..3:smt(gt2_len ge4_n).
  by rewrite ?size_map DBLL.valP.
rewrite size_chunk 2:size_mkseq 2:lez_maxr 3:mulzK; 1..3:smt(gt2_len ge4_n).
move => i rngi.
rewrite /chunk size_mkseq lez_maxr 2:mulzK; 1,2:smt(gt2_len ge4_n).
rewrite nth_mkseq /= 1:// (nth_map witness) /= 1:size_map 1:DBLL.valP 1://.
rewrite map_mkseq /(\o) /= (nth_map witness) 2:DigestBlock.valP 2:mulKz 1:DBLL.valP 1,2://.
rewrite &(eq_from_nth witness) ?size_take ?size_drop ?size_mkseq; 1..5:smt(gt2_len ge1_n).
move=> j; pose ifn := if _ then _ else _; rewrite (: ifn = n); 1:smt(gt2_len ge4_n).
move=> rngj; rewrite nth_mkseq 1:// /= nth_take 3:nth_drop; 1..4:smt(ge1_n).
rewrite nth_mkseq 2:/=; 1: smt(ge1_n); congr.
rewrite mulrDr mulrA addrC -drop_drop; 1,2: smt(ge1_n).
rewrite drop_flatten_ctt; 1: by move => bs /mapP -[x [_ ->]]; 1: rewrite DigestBlock.valP.
rewrite (drop_nth witness i) /= 1:size_map 1:DBLL.valP 1://.
rewrite flatten_cons /= (nth_map witness) 1:DBLL.valP 1:// drop_cat.
rewrite DigestBlock.valP ifT 1:/# take_cat size_drop 1:/# DigestBlock.valP.
case (j = n - 1) => [-> | neqn1_j]; 2: by rewrite ifT 1:/#.
rewrite ifF 1:/# /= take_le0 1:/# cats0.
by rewrite take_oversize 2:// 1:size_drop 2:DigestBlock.valP; 1,2:smt(ge1_n).
qed.

lemma gen_skWOTS_WOTS_genSK ss s ad:
  valid_xidxvalslpch (adr2idxs ad) =>
  (forall i, 0 <= i < 3 => ad.[i] = W32.zero) =>
    DBLL.val (gen_skWOTS ss s (adr2ads ad))
  = map bs2block (LenNBytes.val (WOTS_genSK ad ss s)).
proof.
move=> valadch valid012.
rewrite /gen_skWOTS /= DBLL.insubdK.
+ move: ge0_len; pose l := len; elim: l=> />.
  + by rewrite iter0.
  by move=> l ge0_l ih; rewrite iterS //= size_rcons //= ih.
(* Deal with size (iter _ _) = i invariant *)
have ->: iter len (fun skWOTS=> rcons skWOTS (DigestBlock.insubd (BytesToBits (NBytes.val (prf_keygen ss (s, idxs2adr (HAX.Adrs.val (set_hidx (set_chidx (adr2ads ad) (size skWOTS)) 0 )))))))) []
       = iteri len (fun i skWOTS=> rcons skWOTS (DigestBlock.insubd (BytesToBits (NBytes.val (prf_keygen ss (s, idxs2adr (HAX.Adrs.val (set_hidx (set_chidx (adr2ads ad) i) 0)))))))) [].
+ move: ge0_len; pose l := len; elim: l=> />.
  + by rewrite iter0 // iteri0.
  move=> l ge0_l ih; rewrite iterS // iteriS //= ih.
  do! congr.
  move: ge0_l; pose l' := l; elim: l'=> />.
  + by rewrite iteri0.
  by move=> l' ge0_l' ih'; rewrite iteriS //= size_rcons ih'.
(* Deal with address construction *)
(* Now for the nasty bit *)
rewrite /WOTS_genSK.
have ->: iteri len (fun i ask=>
           let (ad, sk) = ask in
           let ad = set_chain_addr ad i in
           let sk_i = prf_keygen ss (s, ad) in
           let sk = put sk i sk_i in
           (ad, sk))
               (set_key_and_mask (set_hash_addr ad 0) 0, nseq len witness)
       = (let ad = set_key_and_mask (set_hash_addr ad 0) 0 in
          if len = 0 then ad else set_chain_addr ad (len - 1)
         , (map block2bs (iteri len (fun i skWOTS=>
             let sk = rcons skWOTS (DigestBlock.insubd (BytesToBits (NBytes.val (prf_keygen ss (s, idxs2adr (HAX.Adrs.val (set_hidx (set_chidx (adr2ads ad) i) 0))))))) in
             sk) [])) ++ nseq (len - len) witness).
+ pose {-2 6}l := len.
  have: l <= len by done.
  have: 0 <= l by exact: ge0_len.
  elim: l.
  + by rewrite !iteri0 //=.
  move=> l ge0_l ih l_le_len; rewrite !iteriS //=.
  have -> /=: l + 1 <> 0 by smt().
  rewrite ih //= 1:/#.
  have ->: set_chain_addr (if l = 0
                           then set_key_and_mask (set_hash_addr ad 0) 0
                           else set_chain_addr (set_key_and_mask (set_hash_addr ad 0) 0) (l - 1))
                          l
        = set_chain_addr (set_key_and_mask (set_hash_addr ad 0) 0) l.
  + rewrite /set_hash_addr /set_chain_addr /set_key_and_mask ?setE &(ext_eq) /= => i rngi.
    rewrite ?initE rngi /=.
    case (i = 5) => [// | nf /=].
    case (l = 0) => lval //.
    rewrite ?initE rngi /= nf /=.
    case (i = 7) => [// | nfr /=].
    rewrite ?initE rngi /= nfr /=.
    case (i = 6) => [// | nfs /=].
    by rewrite ?initE rngi /= nfs /=.
  rewrite put_cat size_map.
  pose xs := iteri l _ _.
  have -> //=: size xs = l.
  + rewrite /xs; move: ge0_l; pose l' := l; elim: l'.
    + by rewrite iteri0.
    by move=> l' ge0_l' ih'; rewrite iteriS //= size_rcons ih'.
  rewrite map_rcons cat_rcons.
  congr.
  have ->: nseq (len - l) witness<:Params.nbytes> = witness :: (nseq (len - (l + 1)) witness).
  + by rewrite (nseqS (len - l - 1)) /#.
  rewrite put_cons0; congr.
  rewrite /block2bs DigestBlock.insubdK.
  + rewrite /BytesToBits size_flatten /sumz !foldr_map //=.
    have ->: forall (xs : W8.t list), foldr (fun _ z=> 8 + z) 0 xs = 8 * size xs.
    + by elim=> /> xs0 -> /#.
    by rewrite NBytes.valP.
  rewrite BytesToBitsK /NBytes.insubd NBytes.valK //=.
  do !congr.
  move: valadch => @/valid_xidxvalslpch validxs.
  rewrite /set_hash_addr /set_chain_addr /set_key_and_mask ?setE /=.
  rewrite  /adr2ads /set_chidx /set_idx (HAX.Adrs.insubdK (adr2idxs _)).
  + rewrite /adr2idxs /valid_adrsidxs 1:size_rev.
    rewrite size_map size_sub 1:// /= /valid_xidxvalslp /valid_xidxvalslpch; left.
    by move: validxs; rewrite /adr2idxs ?nth_rev ?size_rev ?size_map ?size_iota.
  rewrite /set_hidx /set_idx (HAX.Adrs.insubdK (put _ 1 l)) /adr2idxs /valid_adrsidxs 1:size_put 1:size_rev.
  + rewrite size_map size_sub 1:// /= /valid_xidxvalslp /valid_xidxvalslpch; left.
    move: validxs; rewrite ?nth_put ?nth_rev ?size_rev ?size_put ?size_map ?size_iota //= => [#] -> _ -> -> /=.
    by smt(expr_ge0 ge0_h).
  rewrite HAX.Adrs.insubdK /valid_adrsidxs 1:?size_put 1:size_rev.
  + rewrite size_map size_sub 1:// /= /valid_xidxvalslp /valid_xidxvalslpch; left.
    move: validxs; rewrite /adr2idxs ?nth_put ?nth_rev ?size_put ?size_rev ?size_map ?size_iota 1..12:// /=.
    by move => [#] _ _ -> -> /=; smt(expr_ge0 ge0_h w_vals).
  rewrite /idxs2adr; apply ext_eq => j rngj /=.
  rewrite ?initE rngj /=.
  case (3 <= j <= 6) => subrngi; last first.
  + rewrite ifF 1:/# initE rngj /=.
    case (j = 7) => //= ?.
    by rewrite initE rngj /= ifF /#.
  rewrite ?nth_put ?nth_rev ?(nth_map witness) ?size_put ?size_rev ?size_map ?size_iota 1,2:// 1..3:/#.
  case (j = 5) => [// eq5_j | neq5j].
  case (j = 6) => [// //| neq6j].
  rewrite ifF 1:/# ifF 1:/#.
  by rewrite initE rngj /= ifF 1:/# initE rngj /= ifF 1:/# nth_iota /#.
move=> //=; rewrite LenNBytes.insubdK.
+ rewrite size_cat size_map size_nseq /max /=.
  move: ge0_len; pose l := len; elim: l=> />.
  + by rewrite iteri0.
  + by move=> l ge0_l ih; rewrite iteriS // size_rcons ih.
rewrite nseq0 cats0 -map_comp (eq_map _ idfun).
+ move=> x @/(\o) @/bs2block @/block2bs.
  rewrite NBytes.insubdK.
  + by rewrite /BitsToBytes size_map size_chunk //; smt(DigestBlock.valP).
  rewrite BitsToBytesK; 1:smt(DigestBlock.valP).
  by rewrite /DigestBlock.insubd DigestBlock.valK.
by rewrite map_id.
qed.

equiv genSK_eq:
  WOTS_TW_ES.gen_skWOTS ~ WOTS.pseudorandom_genSK:
       ss{1} = sk_seed{2} /\ ps{1} = seed{2} /\ ad{1} = adr2ads address{2}
    /\ valid_xidxvalslpch (adr2idxs address{2})
    /\ (forall i, 0 <= i < 3 => address{2}.[i] = W32.zero)
    ==> DBLL.val res{1} = map bs2block (LenNBytes.val res{2}).
proof.
proc *.
exlim ss{1}, ps{1}, ad{1}=> ss0 ps0 ad0.
call {1} (: ss = ss0 /\ ps = ps0 /\ ad = ad0 ==> res = gen_skWOTS ss0 ps0 ad0).
+ conseq (: true ==> true: =1%r) (skWOTS_eq ss0 ps0 ad0)=> //.
  proc; while (size skWOTS <= len) (len - size skWOTS); auto=> />.
  + by move=> &0 _; rewrite size_rcons /#.
  smt(ge0_len).
exlim sk_seed{2}, seed{2}, address{2}=> sk_seed0 seed0 address0.
call {2} (: arg = (sk_seed0, seed0, address0) ==> res = WOTS_genSK address0 sk_seed0 seed0).
+ conseq (: true ==> true: =1%r) (Eqv_WOTS_genSK address0 sk_seed0 seed0)=> //.
  proc; while (i <= len) (len - i); auto=> /> => [/#|].
  smt(ge0_len).
by auto=> |>; exact: gen_skWOTS_WOTS_genSK.
qed.

equiv pkFromSig_eq:
  WOTS_TW_ES.pkWOTS_from_sigWOTS ~ WOTS.pkFromSig:
     DigestBlock.val m{1} = BytesToBits (NBytes.val M{2})
  /\ map DigestBlock.val (DBLL.val sig{1}) = map (BytesToBits \o NBytes.val) (LenNBytes.val sig{2})
  /\ ps{1} = _seed{2}
  (* /\ ad{1} = adr2ads address{2} *)
  /\ ads2adr ad{1} = address{2}
  /\ valid_xidxvalslpch (HAX.Adrs.val ad{1})
  ==> map DigestBlock.val (DBLL.val res{1}) = map (BytesToBits \o NBytes.val) (LenNBytes.val res{2}).
proof.
proc.
seq 1 9: (map BaseW.val (EmsgWOTS.val em){1} = msg{2}
       /\ tmp_pk{2} = nseq len witness
       /\ map DigestBlock.val (DBLL.val sig{1}) = map (BytesToBits \o NBytes.val) (LenNBytes.val sig{2})
       /\ ps{1} = _seed{2}
       (* /\ ad{1} = adr2ads address{2} *)
       /\ ads2adr ad{1} = address{2}
       /\ valid_xidxvalslpch (HAX.Adrs.val ad{1})).
+ outline{2} [2 .. 9] by { msg <@ WOTS_Encode.encode(NBytes.val M); }.
  ecall{2} (WOTSEncodeP (NBytes.val M{2})).
  auto => &1 &2 /> eqm ?.
  rewrite -/EmsgWOTS.ofemsgWOTS EmsgWOTS.ofemsgWOTSK.
  + by rewrite /encode_int size_cat /checksum /int2lbw /= ?size_mkseq; smt(ge1_len1 ge1_len2).
  rewrite eqm /BytesToBits flattenK 1://; 1: move=> x /mapP [y [_ ->]]; 1: by rewrite size_w2bits.
  move=> * /=; rewrite /len1 NBytes.valP -log2w_eq -fromint_div; 1: smt(logw_vals).
  by rewrite from_int_ceil mulrC divMr; smt(logw_vals).
while (map BaseW.val (EmsgWOTS.val em){1} = msg{2}
    /\ map DigestBlock.val (DBLL.val sig{1}) = map (BytesToBits \o NBytes.val) (LenNBytes.val sig{2})
    /\ ps{1} = _seed{2}
    /\ (address{2} = if i{2} = 0 then ads2adr ad{1} else set_chain_addr (ads2adr ad{1}) (i - 1){2})
    /\ valid_xidxvalslpch (HAX.Adrs.val ad{1})
    /\ size pkWOTS{1} = i{2}
    /\ size tmp_pk{2} = len
    /\ 0 <= i{2} <= len
    /\ (forall j, 0 <= j < size pkWOTS{1} =>
        DigestBlock.val (nth witness pkWOTS{1} j) = BytesToBits (NBytes.val (nth witness tmp_pk{2} j)))).
+ wp; sp.
  exlim sig_i{2}, msg_i{2}, (w - 1 - msg_i){2}, _seed{2}, address{2}=> x i s _s ad.
  call {2} (: arg = (x, i, s, _s, ad) /\ 0 <= s ==> res = chain x i s _s ad).
  + conseq (: 0 <= s{!hr} ==> true) (chain_eq x i s _s ad)=> //.
    by proc; while (chain_count <= s{!hr}) (s{!hr} - chain_count); auto=> /#.
  auto=> |> &1 &2 eq_sig val_ad size_pk ge0_size size_le_len inv pkWOTS_lt_len; split=> [|_].
  + rewrite (nth_map witness).
    + by rewrite size_ge0 EmsgWOTS.valP.
    smt(BaseW.valP).
  split.
  + split.
    + case: (size pkWOTS{1} = 0)=> [->|] //.
      have -> /=: size pkWOTS{1} + 1 <> 0 by smt(size_ge0).
      by rewrite /set_chain_addr /ads2adr /idxs2adr; smt(@Array8). (* Nasty, but WTF is this library design? *)
    rewrite size_rcons size_put size_pk /=; split; 1:smt().
    move=> j ge0_j j_lt_len.
    move: eq_sig=> /(congr1 (fun x=> nth witness x (size pkWOTS{1}))) /=.
    rewrite (nth_map witness).
    + by rewrite size_ge0 DBLL.valP.
    rewrite (nth_map witness).
    + by rewrite size_ge0 LenNBytes.valP.
    rewrite (nth_map witness).
    + by rewrite size_ge0 EmsgWOTS.valP.
    move=> @/(\o) /= ->.
    rewrite nth_rcons nth_put 1:#smt:(size_ge0).
    case: (j < size pkWOTS{1})=> [/#|].
    case: (j = size pkWOTS{1})=> [->> /=|/#].
    rewrite chain_ch.
    rewrite /cf /ch /f //= /EmsgWOTS."_.[_]" /EmsgWOTS.ofemsgWOTS.
    rewrite size_ge0 /= pkWOTS_lt_len //=.
    (* Simplify address *)
    have ->: set_chain_addr (if size pkWOTS{1} = 0
                             then ads2adr ad{!1}
                             else set_chain_addr (ads2adr ad{!1}) (size pkWOTS{1} - 1))
                            (size pkWOTS{1})
           = set_chain_addr (ads2adr ad{!1}) (size pkWOTS{1}).
    + by rewrite /set_chain_addr !(fun_if, if_arg).
    (** Each of these arguments (nested!) should be extracted out as
        a proof interface on the datatypes **)
    pose chl := (w - 1 - BaseW.val (nth witness (EmsgWOTS.val em){1} (size pkWOTS){1})).
    have ge0_chl: 0 <= chl by smt(BaseW.valP).
    have lew_chl: BaseW.val (nth witness (EmsgWOTS.val em{1}) (size pkWOTS{1})) + chl <= w - 1 by smt(BaseW.valP).
    (* Eliminate outer cast *)
    rewrite DigestBlock.insubdK.
    + elim: chl ge0_chl lew_chl => [lew1|].
      + rewrite iteri0 // size_flatten /sumz foldr_map foldr_map /=.
        pose xs:= NBytes.val (nth witness (LenNBytes.val sig{2}) (size pkWOTS{1})).
        have <-: size xs = n.
        + by rewrite NBytes.valP.
        by elim: xs=> // => _x xs //= -> /#.
      by move=> chl ge0_chl lew_chl ih; rewrite iteriS //= DigestBlock.valP.
    (* Eliminate inner cast --- WAAAAAAAAAAAAH!!! *)
    have ->: (fun cc x0 => DigestBlock.val (DigestBlock.insubd (BytesToBits (NBytes.val (f ps{1} (idxs2adr (HAX.Adrs.val (set_hidx (set_chidx ad{!1} (size pkWOTS{1})) (BaseW.val (nth witness (EmsgWOTS.val em{1}) (size pkWOTS{1})) + cc)))) (NBytes.insubd (BitsToBytes x0)))))))
           = (fun cc x0 => BytesToBits (NBytes.val (f ps{1} (idxs2adr (HAX.Adrs.val (set_hidx (set_chidx ad{!1} (size pkWOTS{1})) (BaseW.val (nth witness (EmsgWOTS.val em{1}) (size pkWOTS{1})) + cc)))) (NBytes.insubd (BitsToBytes x0))))).
    + apply: fun_ext=> cc; apply: fun_ext=> x0.
      rewrite DigestBlock.insubdK // size_flatten /sumz foldr_map foldr_map /=.
      pose xs:= NBytes.val (f ps{1} (idxs2adr (HAX.Adrs.val (set_hidx (set_chidx ad{!1} (size pkWOTS{1})) (BaseW.val (nth witness (EmsgWOTS.val em{1}) (size pkWOTS{1})) + cc)))) (NBytes.insubd (BitsToBytes x0))).
      have <-: size xs = n.
      + by rewrite NBytes.valP.
      by elim: xs=> // => _x xs //= -> /#.
    elim: chl ge0_chl lew_chl.
    + by rewrite !iteri0.
    move=> chl ge0_chl ih lew1_chl; rewrite !iteriS //=.
    congr; congr; congr.
    + rewrite /set_hash_addr /set_chain_addr ?setE /=.
      rewrite /set_chidx /set_hidx /set_idx (HAX.Adrs.insubdK (put _ 1 _)).
      + rewrite /valid_adrsidxs /valid_xidxvalslp size_put; split; 1:smt(HAX.Adrs.valP).
        left; move: val_ad; rewrite /valid_xidxvalslpch ?nth_put 5:/=; 1..4:smt(HAX.Adrs.valP).
        by move=> [#] -> _ -> -> /=; smt(w_vals size_ge0).
      rewrite (HAX.Adrs.insubdK).
      + rewrite /valid_adrsidxs /valid_xidxvalslp ?size_put; split; 1:smt(HAX.Adrs.valP).
        left; move: val_ad; rewrite /valid_xidxvalslpch ?nth_put ?size_put 9:/=; 1..8:smt(HAX.Adrs.valP).
        move=> [#] _ _ -> -> /=; split; 2: smt(w_vals size_ge0).
        by rewrite /valid_hidx; smt(w_vals BaseW.valP size_ge0).
      rewrite /ads2adr /idxs2adr; apply ext_eq => j rngj /=.
      rewrite ?initE rngj /=.
      case (3 <= j <= 6) => subrngj; last first.
      + by do ? (rewrite ifF 1:/# initE rngj /= ?subrngj /=).
      rewrite ?nth_put ?size_put; 1,2:smt(HAX.Adrs.valP).
      case (j = 6) => [// /#| neq6j].
      rewrite ifF 1:/# initE rngj /=.
      case (j = 5) => [// /#| neq5j].
      by rewrite initE rngj /= subrngj /= ifF 1:/#.
    by rewrite ih 1:/# BytesToBitsK /NBytes.insubd NBytes.valK.
  by rewrite size_rcons.
auto=> |> &1 &2 eq_sig tes.
split; 1: by rewrite size_nseq; smt(ge0_len).
move=> pkL pkR len_le_size _ sizeP _ size_le_len eq_nth.
apply: (eq_from_nth witness).
+ by rewrite !size_map; smt(DBLL.valP LenNBytes.valP).
move=> j; rewrite DBLL.insubdK 1:/# size_map=> j_bnd.
rewrite !(nth_map witness) //; 1:smt(LenNBytes.valP).
by rewrite LenNBytes.insubdK 1:/# eq_nth.
qed.

(* TODO: check usage; would it be better phrased as an equivalence? *)
phoare leaves_correct _ps _ss  _ad :
 [ FL_XMSS_TW_ES.leaves_from_sspsad :
      arg = (_ss, _ps, _ad)
  ==>
   res =
  map
    (leafnode_from_idx _ss _ps _ad) (range 0 (2 ^ h)) ] = 1%r.
proof.
conseq (: true ==> true: =1%r) (: arg = (_ss, _ps, _ad) ==> res = map (leafnode_from_idx _ss _ps _ad) (range 0 (2 ^ h)))=> //; last first.
+ proc; while (size leafl <= l) (l - size leafl); auto; 2:smt(ge1_d).
  auto=> />; conseq (: true ==> true); auto.
  + by auto=> /> &0 _ + pks; rewrite size_rcons /#.
  call (: true ==> true).
  + proc; while (size pkWOTS <= len) (len - size pkWOTS); auto; 2:smt(ge0_len).
    by auto=> /> &0; rewrite size_rcons /#.
  call (: true ==> true)=> //.
  proc; while (size skWOTS <= len) (len - size skWOTS); auto; 2:smt(ge0_len).
  by auto=> /> &0; rewrite size_rcons /#.
proc; while (size leafl <= l
          /\ ad = _ad
          /\ leafl = map (leafnode_from_idx ss ps _ad) (range 0 (size leafl))).
+ wp; ecall (pkWOTS_from_skWOTS_eq skWOTS ps (set_kpidx (set_typeidx ad 0) (size leafl))).
  ecall (skWOTS_eq ss ps (set_kpidx (set_typeidx ad 0) (size leafl))).
  auto=> /> &0 _ ih size_lt_l; rewrite size_rcons; split=> [/#|].
  rewrite /range /= iotaSr 1:size_ge0 map_rcons -ih.
  congr.
  rewrite /leafnode_from_idx /pkco.
  have -> //=: 8 * n * len <> 8 * n by smt(ge1_n gt2_len).
  have -> //=: 8 * n * len <> 8 * n * 2 by smt(ge1_n gt2_len).
  rewrite /bs2block; do !congr.
  + by rewrite /ads2adr.
  have ->: (gen_skWOTS ss ps (set_kpidx (set_typeidx _ad 0) (size leafl))){0}
         = (DBLL.insubd (DBLL.val (gen_skWOTS ss ps (adr2ads (ads2adr (set_kpidx (set_typeidx _ad 0) (size leafl))))))){0}.
  + rewrite /DBLL.insubd DBLL.valK /=.
    do !congr.
    rewrite ads2adrK 2:// -(all_nthP _ _ witness) => i.
    move: (HAX.Adrs.valP (set_kpidx (set_typeidx _ad 0) (size leafl{0}))) => @/valid_adrsidxs [-> t rng_i].
    rewrite mem_range /set_kpidx /set_typeidx /set_idx (HAX.Adrs.insubdK (put _ 3 0)).
    + rewrite /valid_adrsidxs ?size_put; split; 1: smt(HAX.Adrs.valP).
      rewrite /valid_xidxvalslp /valid_xidxvalslpch; left.
      by rewrite ?nth_put ?size_put; smt(HAX.Adrs.valP w_vals ge2_len expr_gt0).
    rewrite HAX.Adrs.insubdK.
    + rewrite /valid_adrsidxs ?size_put; split; 1: smt(HAX.Adrs.valP).
      rewrite /valid_xidxvalslp /valid_xidxvalslpch; left.
      by rewrite ?nth_put ?size_put; smt(HAX.Adrs.valP gt_exprsbde w_vals ge2_len expr_gt0 ge0_h h_max size_ge0 pow2_32).
    rewrite ?nth_put ?size_put; 1..5: smt(HAX.Adrs.valP).
    by smt(gt_exprsbde ge0_h h_max size_ge0 pow2_32).
  rewrite gen_skWOTS_WOTS_genSK.
  + rewrite /ads2adr idxs2adrK; 1:smt(HAX.Adrs.valP).
    rewrite -(all_nthP _ _ witness) => i.
    move: (HAX.Adrs.valP (set_kpidx (set_typeidx _ad 0) (size leafl{0}))) => @/valid_adrsidxs [-> t rng_i].
    rewrite mem_range /set_kpidx /set_typeidx /set_idx (HAX.Adrs.insubdK (put _ 3 0)).
    + rewrite /valid_adrsidxs ?size_put; split; 1: smt(HAX.Adrs.valP).
      rewrite /valid_xidxvalslp /valid_xidxvalslpch; left.
      by rewrite ?nth_put ?size_put; smt(HAX.Adrs.valP w_vals ge2_len expr_gt0).
    rewrite HAX.Adrs.insubdK.
    + rewrite /valid_adrsidxs ?size_put; split; 1: smt(HAX.Adrs.valP).
      rewrite /valid_xidxvalslp /valid_xidxvalslpch; left.
      by rewrite ?nth_put ?size_put; smt(HAX.Adrs.valP gt_exprsbde w_vals ge2_len expr_gt0 ge0_h h_max size_ge0 pow2_32).
    rewrite ?nth_put ?size_put; 1..5: smt(HAX.Adrs.valP).
    by smt(gt_exprsbde ge0_h h_max size_ge0 pow2_32).
  + rewrite /set_kpidx /set_typeidx /set_idx (HAX.Adrs.insubdK (put _ 3 0)).
    + rewrite /valid_adrsidxs ?size_put; split; 1: smt(HAX.Adrs.valP).
      rewrite /valid_xidxvalslp /valid_xidxvalslpch; left.
      by rewrite ?nth_put ?size_put; smt(HAX.Adrs.valP w_vals ge2_len expr_gt0).
    rewrite HAX.Adrs.insubdK.
    + rewrite /valid_adrsidxs ?size_put; split; 1: smt(HAX.Adrs.valP).
      rewrite /valid_xidxvalslp /valid_xidxvalslpch; left.
      by rewrite ?nth_put ?size_put; smt(HAX.Adrs.valP gt_exprsbde w_vals ge2_len expr_gt0 ge0_h h_max size_ge0 pow2_32).
    by rewrite /valid_xidxvalslpch ?nth_put ?size_put; smt(HAX.Adrs.valP gt_exprsbde w_vals ge2_len expr_gt0 ge0_h h_max size_ge0 pow2_32).
  + move=> i rngi; rewrite /set_kpidx /set_typeidx /set_idx (HAX.Adrs.insubdK (put _ 3 0)).
    + rewrite /valid_adrsidxs ?size_put; split; 1: smt(HAX.Adrs.valP).
      rewrite /valid_xidxvalslp /valid_xidxvalslpch; left.
      by rewrite ?nth_put ?size_put; smt(HAX.Adrs.valP w_vals ge2_len expr_gt0).
    by rewrite /ads2adr /idxs2adr ?initE /#.
  rewrite /wots_pk_val /WOTS_pkgen /= //=.
  pose sks := LenNBytes.val (WOTS_genSK _ _ _).
  have ->: iteri len (fun i apk=>
                        let (ad, pk) = apk in
                        (set_chain_addr ad i, put pk i (chain (nth witness sks i) 0 (w - 1) ps{0} (set_chain_addr ad i))))
                 (ads2adr (set_kpidx (set_typeidx _ad 0) (size leafl{0})), nseq len witness)
         = (if len = 0
            then ads2adr (set_kpidx (set_typeidx _ad 0) (size leafl{0})) else set_chain_addr (ads2adr (set_kpidx (set_typeidx _ad 0) (size leafl{0}))) (len - 1)
          , (map NBytes.insubd (chunk n (BitsToBytes (flatten (map DigestBlock.val (DBLL.val (pkWOTS_from_skWOTS (DBLL.insubd (map bs2block sks)) ps{0} (set_kpidx (set_typeidx _ad 0) (size leafl{0})))))))))).
  (** FD --- Death and Misery *)
  + rewrite chfltn_id.
    rewrite /pkWOTS_from_skWOTS /= DBLL.insubdK.
    + move: ge0_len; pose l := len; elim: l.
      + by rewrite iter0.
      by move=> l ge0_l ih'; rewrite iterS // size_rcons ih'.
    rewrite DBLL.insubdK.
    + by rewrite size_map LenNBytes.valP.
    rewrite -map_comp -map_comp.
    have womp: map (NBytes.insubd \o BitsToBytes \o DigestBlock.val) (iter len (fun pkWOTS=> rcons pkWOTS (cf ps{0} (set_chidx (set_kpidx (set_typeidx _ad 0) (size leafl{0})) (size pkWOTS)) 0 (w - 1) (DigestBlock.val (nth witness (map bs2block sks) (size pkWOTS))))) [])
                       = iter len (fun pkWOTS=> rcons pkWOTS ((NBytes.insubd \o BitsToBytes \o DigestBlock.val) (cf ps{0} (set_chidx (set_kpidx (set_typeidx _ad 0) (size leafl{0})) (size pkWOTS)) 0 (w - 1) (DigestBlock.val (nth witness (map bs2block sks) (size pkWOTS)))))) [].
    + move: ge0_len; pose l := len; elim: l.
      + by rewrite !iter0.
      move=> l ge0_l ih'; rewrite !iterS //= map_rcons //= ih' //=.
      congr.
      pose xs := iter l _ _.
      have ->: size xs = l.
      + rewrite /xs; move: ge0_l; pose l' := l; elim: l'.
        + by rewrite iter0.
        by move=> l' ge0_l' ih''; rewrite iterS // size_rcons ih''.
      pose ys := iter l _ _.
      have -> //: size ys = l.
      rewrite /ys; move: ge0_l; pose l' := l; elim: l'.
      + by rewrite iter0.
      by move=> l' ge0_l' ih''; rewrite iterS // size_rcons ih''.
    rewrite womp /= /iter.
    pose fn1 := (fun (i : int) (apk : Address.adrs * nbytes list) =>
     let (ad0, pk) = apk in
     (set_chain_addr ad0 i, put pk i (chain (nth witness sks i) 0 (w - 1) ps{0} (set_chain_addr ad0 i)))).
    pose fn2 := (fun (_ : int) (pkWOTS0 : nbytes list) =>
      rcons pkWOTS0
        ((\o) (NBytes.insubd \o BitsToBytes) DigestBlock.val
           (cf ps{0} (set_chidx (set_kpidx (set_typeidx _ad 0) (size leafl{0})) (size pkWOTS0)) 0 (
              w - 1) (DigestBlock.val (nth witness (map bs2block sks) (size pkWOTS0)))))).
    pose adrt := (ads2adr (set_kpidx (set_typeidx _ad 0) (size leafl{0}))).
    suff :
      forall i, 0 <= i => i <= len =>
        iteri i fn1 (adrt, nseq len witness) = (if i = 0 then adrt else set_chain_addr adrt (i - 1), (iteri i fn2 []) ++ nseq (len - i) witness).
    + move=> /(_ len _ _) //=; 1: smt(ge0_len).
      by rewrite nseq0 cats0.
    elim; 1: by rewrite /= ?iteri0 // nseq0.
    move=> i ge0_i ihi lelen_i1.
    rewrite ifF 1:/# /= ?iteriS 1,2:// ihi 1:/#.
    have eqi_sz: i = size (iteri i fn2 []).
    + suff /#: forall j, 0 <= j => size (iteri j fn2 []) = j.
      elim; 1: by rewrite iteri0.
      by move => j ge0_j ihj; rewrite iteriS 1:// /fn2 size_rcons -/fn2 /#.
    rewrite /fn1 /=; split; 1: by case (i = 0).
    rewrite put_cat -eqi_sz /= {2}/fn2.
    rewrite cat_rcons (: len - i = len - i - 1 + 1) 1:// nseqS 1:/# put_cons0.
    congr; congr => [| /#].
    suff: forall j, 0 <= j => j <= w - 1 =>
      chain (nth witness sks i) 0 j ps{0} (set_chain_addr (if i = 0 then adrt else set_chain_addr adrt (i - 1)) i) =
(\o) (NBytes.insubd \o BitsToBytes) DigestBlock.val
  (cf ps{0} (set_chidx (set_kpidx (set_typeidx _ad 0) (size leafl{0})) (size (iteri i fn2 [])))
   0 j (DigestBlock.val (nth witness (map bs2block sks) (size (iteri i fn2 []))))).
    + smt(w_vals).
    elim => [_ |].
    + rewrite chain_ch /ch /cf iteri0 1:// 1:iteri0 1://.
      rewrite /= /(\o) DigestBlock.valKd.
      rewrite (nth_map witness); 1: smt(LenNBytes.valP).
      rewrite DigestBlock.insubdK.
      + by rewrite (size_flatten_ctt 8) 2:size_map 2:NBytes.valP 2:// => x /mapP [xx [_ ->]]; rewrite size_w2bits.
      by rewrite BytesToBitsK NBytes.valKd -eqi_sz.
    move=> j ge0_j + lew1_j1.
    move=> /(_ _); 1: smt().
    rewrite ?chain_ch /ch /cf ?iteriS 1,2:// /=.
    move => -> @/(\o).
    rewrite DigestBlock.valKd /f /= DigestBlock.insubdK.
    case (j = 0) => eq0j.
    + rewrite eq0j; 1: by rewrite iteri0 2:DigestBlock.valP.
      by rewrite (: j = j - 1 + 1) 1:// iteriS 1:/# /= DigestBlock.valP.
    rewrite DigestBlock.insubdK.
    + by rewrite (size_flatten_ctt 8) 2:size_map 2:NBytes.valP 2:// => x /mapP [xx [_ ->]]; rewrite size_w2bits.
    rewrite BytesToBitsK NBytes.valKd; congr.
    rewrite /set_kpidx /set_typeidx /set_idx (HAX.Adrs.insubdK (put _ 3 0)).
    + rewrite /valid_adrsidxs ?size_put; split; 1: smt(HAX.Adrs.valP).
      rewrite /valid_xidxvalslp /valid_xidxvalslpch; left.
      by rewrite ?nth_put ?size_put; smt(HAX.Adrs.valP w_vals ge2_len expr_gt0).
    rewrite /set_chidx /set_idx (HAX.Adrs.insubdK (put _ 2 _)).
    + rewrite /valid_adrsidxs ?size_put; split; 1: smt(HAX.Adrs.valP).
      rewrite /valid_xidxvalslp /valid_xidxvalslpch; left.
      by rewrite ?nth_put ?size_put; smt(HAX.Adrs.valP gt_exprsbde w_vals ge2_len expr_gt0 ge0_h h_max size_ge0 pow2_32).
    rewrite /set_hidx /set_idx -eqi_sz (HAX.Adrs.insubdK (put _ 1 i)).
    + rewrite /valid_adrsidxs ?size_put; split; 1: smt(HAX.Adrs.valP).
      rewrite /valid_xidxvalslp /valid_xidxvalslpch; left.
      by rewrite ?nth_put ?size_put; smt(HAX.Adrs.valP gt_exprsbde w_vals ge2_len expr_gt0 ge0_h h_max size_ge0 pow2_32).
    rewrite HAX.Adrs.insubdK.
    + rewrite /valid_adrsidxs ?size_put; split; 1: smt(HAX.Adrs.valP).
      rewrite /valid_xidxvalslp /valid_xidxvalslpch; left.
      by rewrite ?nth_put ?size_put; smt(HAX.Adrs.valP gt_exprsbde w_vals ge2_len expr_gt0 ge0_h h_max size_ge0 pow2_32).
    rewrite /idxs2adr /set_hash_addr /set_chain_addr ?setE; apply ext_eq => k rngk.
    rewrite ?initE rngk /=.
    rewrite /adrt /set_kpidx /set_typeidx /set_idx (HAX.Adrs.insubdK (put _ 3 0)).
    + rewrite /valid_adrsidxs ?size_put; split; 1: smt(HAX.Adrs.valP).
      rewrite /valid_xidxvalslp /valid_xidxvalslpch; left.
      by rewrite ?nth_put ?size_put; smt(HAX.Adrs.valP w_vals ge2_len expr_gt0).
    rewrite /ads2adr (HAX.Adrs.insubdK).
    + rewrite /valid_adrsidxs ?size_put; split; 1: smt(HAX.Adrs.valP).
      rewrite /valid_xidxvalslp /valid_xidxvalslpch; left.
      by rewrite ?nth_put ?size_put; smt(HAX.Adrs.valP gt_exprsbde w_vals ge2_len expr_gt0 ge0_h h_max size_ge0 pow2_32).
    rewrite /idxs2adr.
    case (3 <= k <= 6) => subrngk; last first.
    + rewrite ifF 1:/# initE rngk /= ifF 1:/#.
      case (i = 0) => eqi0; 1: by rewrite ?initE rngk /= subrngk.
      by rewrite initE rngk /= ifF 1:/# initE rngk /= subrngk /=.
    rewrite ?nth_put ?size_put; 1..7: smt(HAX.Adrs.valP).
    case (k = 6) => [//| neq6k].
    rewrite ?initE rngk /=.
    case (k = 5) => [//| neq5k].
    rewrite eq_sym ifF 1:/# ifF 1:/#.
    case (i = 0) => eqi0.
    + by rewrite initE rngk /= subrngk /= ?nth_put ?size_put; 1..6: smt(HAX.Adrs.valP).
    rewrite ?initE rngk /= eq_sym ifF 1:// ?initE rngk /= subrngk /=.
    by rewrite ?nth_put ?size_put; smt(HAX.Adrs.valP).
  by move=> @/pkWOTS_from_skWOTS //=.
by auto=> />; rewrite range_geq //=; smt(ge1_d).
qed.

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
proof. by rewrite valid_xadrsidxs_adrsidxs zeroxadiP. qed.

phoare tree_hash_correct _ps _ss _lstart _sth :
  [ TreeHash.treehash :
      arg = (_ps,_ss,_lstart,_sth, zero_address)
  /\ 0 <= _sth <= h /\ 0 <= _lstart <= 2^h - 2^_sth  /\ 2^_sth %| _lstart
 ==>
  DigestBlock.insubd (BytesToBits (NBytes.val res)) =
    val_bt_trh (list2tree (map (leafnode_from_idx _ss _ps (adr2ads zero_address))
     (range _lstart (_lstart + 2^_sth)))) _ps (set_typeidx (adr2ads zero_address) trhtype) _sth
     (* (_lstart %/ 2^(_sth + 1))  ] = 1%r. *)
     (_lstart %/ 2 ^ _sth)  ] = 1%r.
proof.
conseq (: _ ==> true) (: _ ==> _);1,2:smt(); last first.
+ proc.
  wp;while (true) (2^t - i).
  + move => *; wp; while (true) (to_uint offset).
    + move => *;inline *; auto => &hr;rewrite uleE /= => *.
      rewrite W64.to_uintB => /=;1: by rewrite uleE /= /#.
      by smt().
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
       congr;congr; apply lfp_st; smt(take_size size_take size_ge0 size_lpath StdOrder.IntOrder.expr_gt0).
       rewrite lfp_st;1..5: smt().
       rewrite   /range iotaS_minus;smt(StdOrder.IntOrder.expr_gt0).
    case (_sth = 0) => H0.
    +  rewrite /prefix ifT;1:smt(take_size size_take size_ge0 size_lpath StdOrder.IntOrder.expr_gt0 h_g0).
       have -> /= : (range _lstart (_lstart + 2 ^ _sth)) = [_lstart] by rewrite H0 /= rangeS.
        rewrite H0 list2tree1 /=.
        suff /#: BS2Int.bs2int (rev (take (size (lpath _lstart)) (lpath _lstart))) = _lstart.
        rewrite take_size /lpath revK BS2Int.int2bsK;smt(h_g0 StdOrder.IntOrder.expr_gt0).
    rewrite /prefix ifF;1:by smt(take_size size_take size_ge0 size_lpath StdOrder.IntOrder.expr_gt0 h_g0).
    rewrite ifT /=;1:by smt(take_size size_take size_ge0 size_lpath StdOrder.IntOrder.expr_gt0 h_g0).
    congr.
    + congr; congr;apply lfp_st;1..5:smt().
    +  by smt(take_size size_take size_ge0 size_lpath StdOrder.IntOrder.expr_gt0).

    rewrite lfp_st;1..5:smt().
    rewrite /range iotaS_minus /=;1: smt(StdOrder.IntOrder.expr_gt0).
    congr;congr;rewrite size_lpath 1:/# ifF;1: smt(StdOrder.IntOrder.expr_gt0). 
    smt(size_take size_lpath).
seq 6 : (#pre /\
   bs2block node = leafnode_from_idx _ss _ps (adr2ads zero_address) (_lstart + i)).
+ seq 3 : (#pre /\   pk = wots_pk_val _ss _ps (set_kpidx (set_typeidx (adr2ads zero_address) 0) (_lstart + i)) (_lstart + i)).
  + conseq />;1: smt().
    ecall (Eqv_WOTS_pkgen address sk_seed pub_seed).
    auto => /> &1 &2 ?????????????; split; 1:smt(get_setE).
    rewrite /wots_pk_val; congr.
    rewrite zeroadsE /set_typeidx /set_kpidx HAX.Adrs.insubdK 1:zeroadiP /set_idx.
    rewrite /put /= ifT 2:HAX.Adrs.insubdK 2:zeroadiP /=; 1: smt(HAX.Adrs.valP).
    apply: tP=> i i_bnd.
    rewrite /ads2adr /idxs2adr initE i_bnd /=.
    rewrite /set_ots_addr /set_type.
    rewrite HAX.Adrs.val_insubd /valid_adrsidxs //=.
    rewrite /valid_xidxvalslp /valid_xidxvalslpch /valid_xidxvalslppkco /valid_xidxvalslptrh.
    rewrite /valid_hidx /valid_chidx /valid_kpidx //=.
    have -> /=: 0 < w - 1 by smt(w_vals).
    have -> /=: 0 < len by smt(gt2_len).
    have -> /=: 0 <= _lstart + i{!1} < l by smt().
    by rewrite !fun_if; smt(get_setE).
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

+ auto => /> &hr ?????????????Ho Hs; rewrite uleE /= => H.
  rewrite !to_uintB /=;1..2,4: by rewrite uleE /=; smt().
  + by rewrite uleE /= to_uintB /=; rewrite ?uleE /=; smt().

  move => H1;rewrite H1.
  move : (Hs (to_uint offset{hr} - 1) _);1: smt(sfl_size).
  move : (Hs (to_uint offset{hr} - 2) _);1: smt(sfl_size).
  move => [# Hs21 Hs22] [# Hs11 Hs12].

have ? :  hw (lpathst (i{hr} + 1) _sth) <= hw (lpathst i{hr} _sth) by
  have /= := hwinc_noentry _lstart i{hr} _sth _ss _ps (adr2ads zero_address) (to_uint offset{hr}) _; by smt(sfl_size).

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
  + have /= := si_reduced_node _lstart i{hr} _sth _ss _ps (adr2ads zero_address) (to_uint offset{hr}) _ _ _ _ _ _ _ _;1..8:smt().
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
  proc o(xm : threen_bytes * msg_t) : nbytes  = {
    var x : threen_bytes;
    var m : msg_t;
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
    idx <- Index.insubd (BS2Int.bs2int (take h (BytesToBits (rev (nth witness xs 2)))));

    cm <@ O.o(mk, (root, idx, m));

    return NBytes.insubd (BitsToBytes (DigestBlock.val cm));
  }
}.

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
ecall {1} (leaves_correct ps0{1} ss0{1} ad{1}) => /=.
ecall {2} (tree_hash_correct pub_seed{2} sk_seed{2} 0 h).
auto => /> &2; do split.
+ rewrite /set_layer_addr /zero_address /= tP => *;  smt(Array8.get_setE Array8.initiE).
+ smt(h_g0).

move=> ??? rr ->.
suff @/adc ->: XAddress.val (XAddress.insubd (HAX.Adrs.insubd (adr2idxs zero_address))) = adr2ads zero_address.
+ by smt(NBytes.valK).
by rewrite XAddress.insubdK /valid_xadrs; smt(HAX.Adrs.valP take_size).
qed.


(* Signature type is abused with two index copies because I need this to simulate
   the actual operation of the implementation *)

op sigrel(asig : sigXMSSTW, sig : sig_t) =
   asig.`1 = sig.`r /\
   Index.val asig.`2.`1 = to_uint sig.`sig_idx /\
   asig.`2.`2 = DBLL.insubd
     (map (fun (b : nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (LenNBytes.val sig.`r_sig.`1)) /\
   (rev (DBHL.val asig.`2.`3) =
     (map (fun (b : nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (AuthPath.val sig.`r_sig.`2))).

lemma szcnsh bt bs i ps ad hi bi:
     0 <= i
  => height bt = i
  => size bs = i
  => fully_balanced bt
  => size (cons_ap_trh_gen bt bs ps ad hi bi) = i.
proof.
elim: bt bs i ps ad hi bi.
smt(height_eq0 size_eq0 size_ge0).
move=> l r ihl ihr.
case.
smt(height_eq0 size_eq0 size_ge0).
move=> b bs i ps ad hi bi ge0_i /= eqi_hei1 eqi_sz1 [#] eqhei fbl fbr.
case (i = 0) => [eq0 | neq0].
smt(height_eq0 size_eq0 size_ge0).
case b => bV.
rewrite (ihr bs (i - 1)) // /#.
rewrite (ihl bs (i - 1))  // /#.
qed.

lemma list2tree_takedrop (s : 'a list) (bs : bool list) (e : int) :
  0 <= e =>
  size s = 2 ^ e =>
  size bs <= e =>
  oget (sub_bt (list2tree s) bs)
  =
  list2tree (take (2 ^ (e - size bs)) (drop (bs2int (rev bs) * 2 ^ (e - size bs)) s)).
proof.
elim: bs e s => /= [e s ge0_e eqsz gtszbs_e | b bs ih].
+ by rewrite subbt_empty oget_some bs2int_nil /= drop0 -eqsz take_size.
move=> e + ge0_e; elim: e ge0_e.
+ smt(size_ge0).
move=> e ge0_e ih2 s szs szbs_e.
have szdp2e: size (drop (2 ^ e) s) = 2 ^ e.
+ by rewrite size_drop 1:expr_ge0 1:// szs exprD_nneg 1,2://; smt(expr_ge0).
have sztk2e: size (take (2 ^ e) s) = 2 ^ e.
+ by rewrite size_take 1:expr_ge0 1:// szs exprD_nneg 1,2:// 1:expr1 ltr_pmulr 1:expr_gt0.
rewrite -(cat_take_drop (2 ^ e)) (list2treeS e) // /=.
rewrite rev_cons bs2int_rcons /= (: e + 1 - (1 + size bs) = e - size bs) 1:/# mulrDl /=.
have exprd2e:  2 ^ size (rev bs) * 2 ^ (e - size bs) = 2 ^ e.
+ by rewrite size_rev -exprD_nneg 1:size_ge0 /#.
have ltszs2e : 2 ^ e < size s.
+ by rewrite szs exprD_nneg 1,2:// 1:expr1 ltr_pmulr 1:expr_gt0.
case: b => bv /=.
+ rewrite (ih e (drop (2 ^ e) s)) 1,2:// 1:/#.
  rewrite drop_cat size_take 1:expr_ge0 1:// ltszs2e.
  by rewrite ifF 1:-lezNgt; smt(bs2int_ge0 expr_ge0).
rewrite (ih e (take (2 ^ e) s)) 1:// 2:/# 1://.
rewrite drop_cat ifT 1:sztk2e.
+ rewrite {2}(: e = size bs + (e - size bs)) 1:/# (Ring.IntID.exprD_nneg _ (size bs)) 1:// 1:/#.
  by rewrite ltr_pmul2r 1:expr_gt0 1:// -size_rev bs2int_le2Xs.
rewrite take_cat size_drop; 1: smt(bs2int_ge0 expr_ge0).
+ rewrite lez_maxr size_take 1,3:expr_ge0 1,3:// 1,2:ltszs2e /=.
  rewrite subr_ge0 {2}(: e = size bs + (e - size bs)) 1:/# (Ring.IntID.exprD_nneg _ (size bs)) 1:// 1:/#.
  by rewrite ler_pmul2r 1:expr_gt0 1:// -size_rev; smt(bs2int_le2Xs).
suff/lez_eqVlt [eq | -> //] /=: 2 ^ (e - size bs) <= 2 ^ e - bs2int (rev bs) * 2 ^ (e - size bs).
+ rewrite ifF 1:eq 1:/# (take_le0 _ (drop _ s)) 1:/# cats0.
  rewrite take_oversize 1:size_drop 3://; 1:smt(bs2int_ge0 expr_ge0).
  + rewrite lez_maxr 1:size_take 1:expr_ge0 1:// 1:ltszs2e /= 1:-eq 1:expr_ge0 1://.
    by rewrite size_take 1:expr_ge0 1:// 1:ltszs2e /= -eq.
rewrite ler_subr_addr (ler_trans (2 ^ (e - size bs) + (2 ^ (size bs) - 1) * (2 ^ (e - size bs)))).
+ rewrite lez_add2l ler_pmul 1:bs2int_ge0 1:expr_ge0 1:// -size_rev; smt(bs2int_le2Xs).
by rewrite mulrDl /= -exprD_nneg 1:size_ge0 /#.
qed.

lemma list2tree_takedrop_range (bs : bool list) (e : int) :
  0 <= e =>
  size bs <= e =>
  oget (sub_bt (list2tree (range 0 (2 ^ e))) bs)
  =
  list2tree (take (2 ^ (e - size bs)) (drop (bs2int (rev bs) * 2 ^ (e - size bs)) (range 0 (2 ^ e)))).
proof.
move => ge0_e lte_szbs.
rewrite (list2tree_takedrop (range 0 (2 ^ e)) bs e ge0_e _ lte_szbs) 2://.
by rewrite size_range; smt(expr_ge0).
qed.

lemma list2tree_takedrop_range_idx (idx : int) (e i : int) :
  0 <= i <= e =>
  0 <= idx < 2 ^ e =>
  oget (sub_bt (list2tree (range 0 (2 ^ e))) (take i (rev (int2bs e idx))))
  =
  list2tree (take (2 ^ (e - i)) (drop (bs2int (drop (e - i) (int2bs e idx)) * 2 ^ (e - i)) (range 0 (2 ^ e)))).
proof.
move => [ge0_i lee_i] rng_idx.
rewrite (list2tree_takedrop (range 0 (2 ^ e)) (take i (rev (int2bs e idx))) e) 1:/# 3://.
+ by rewrite size_range; smt(expr_ge0).
+ by rewrite size_take 1:// size_rev size_int2bs 1:/#.
rewrite size_take 1:// size_rev size_int2bs.
do ? congr => [/#||/#].
rewrite rev_take 1:size_rev 1:size_int2bs 1:/#.
by rewrite revK size_rev size_int2bs /#.
qed.

lemma list2tree_takedrop_range_idx_map (idx : int) (e i : int) (f : int -> 'a) :
  0 <= i <= e =>
  0 <= idx < 2 ^ e =>
  oget (sub_bt (list2tree (map f (range 0 (2 ^ e)))) (take i (rev (int2bs e idx))))
  =
  list2tree (take (2 ^ (e - i)) (drop (bs2int (drop (e - i) (int2bs e idx)) * 2 ^ (e - i)) (map f (range 0 (2 ^ e))))).
proof.
move => [ge0_i lee_i] rng_idx.
rewrite (list2tree_takedrop (map f (range 0 (2 ^ e))) (take i (rev (int2bs e idx))) e) 1:/# 3://.
+ by rewrite size_map size_range; smt(expr_ge0).
+ by rewrite size_take 1:// size_rev size_int2bs 1:/#.
rewrite size_take 1:// size_rev size_int2bs.
do ? congr => [/#||/#].
rewrite rev_take 1:size_rev 1:size_int2bs 1:/#.
by rewrite revK size_rev size_int2bs /#.
qed.

lemma bnd_uint_bs idx j :
     0 <= to_uint idx < 2 ^ h
  => 0 <= j < h
  => to_uint ((idx `>>` W8.of_int j) `^` W32.one) * 2 ^ j
     <=
     2 ^ h - 2 ^ j.
proof.
move => ??.
rewrite /(`>>`) /= modz_small /=;1:smt(h_max).
have /= ?: 0 <= 2^h < 2^32  by split;[ smt(StdOrder.IntOrder.expr_ge0) | move => *;apply gt_exprsbde;smt(h_max h_g0 leq_div)].
have /= ? : 0 <= 2^j < 2^h  by split;[ smt(StdOrder.IntOrder.expr_ge0) | move => *;apply gt_exprsbde;smt(h_max h_g0 leq_div)].
have -> : (idx `>>>` j) `^` W32.one = if (idx `>>>` j).[0] then
   (idx `>>>` j) - W32.one else (idx `>>>` j) + W32.one.
+ case ((idx `>>>` j).[0]) => Hbit; have := Hbit;rewrite get_to_uint /= to_uint_shr 1:/# => Hbitt.
  + have {2}->/= : (idx `>>>` j) = W32.of_int (to_uint (idx `>>>` j) %/ 2 * 2) + W32.one by smt(@W32 @IntDiv).
    apply W32.wordP => i ib; rewrite xorwE.
    + case(i = 0).
      + move => ->;rewrite Hbit /= !of_intwE /= /int_bit /=; smt(@IntDiv).
    move => ?.
    have -> : W32.one.[i] = false by rewrite of_intwE /=; smt(@IntDiv).
  pose xx := (idx `>>>` j).[i]. simplify.
  rewrite !of_intwE /= /int_bit /= ib /=(modz_small _ 4294967296);1: smt( @W32 pow2_32).
  have -> : to_uint (idx `>>>` j) %/ 2 * 2 %/ 2 ^ i = to_uint (idx `>>>` j)  %/ 2 ^ i; last by  smt(@W32).  
  have [# + _] /=:= divmod_mul (2^(i-1)) (2) (to_uint (idx `>>>` j) %/ 2) 0 _ _;1,2:smt(StdOrder.IntOrder.expr_gt0).
  rewrite -exprSr 1:/# /= => ->;rewrite -divz_mulp;1,2:smt(StdOrder.IntOrder.expr_gt0).
  smt(Ring.IntID.exprSr).
  + have {2}->/= : (idx `>>>` j) = W32.of_int (to_uint (idx `>>>` j) %/ 2 * 2) by smt(@W32 @IntDiv).
    apply W32.wordP => i ib; rewrite xorwE.
    + case(i = 0).
      + move => ->;rewrite Hbit /= !of_intwE /= /int_bit /=; smt(@IntDiv).
    move => ?.
    have -> : W32.one.[i] = false.
    + rewrite of_intwE /= ib /int_bit neqF /= pdiv_small; split => // _.
      by rewrite -(Ring.IntID.expr0 2); smt(gt_exprsbde expr_gt0).
  pose xx := (idx `>>>` j).[i]. simplify.
  rewrite !of_intwE /= /int_bit /= ib /=(modz_small _ 4294967296);1: smt( @W32 pow2_32).
  have -> :( to_uint (idx `>>>` j) %/ 2 * 2 + 1) %/ 2 ^ i = to_uint (idx `>>>` j)  %/ 2 ^ i; last by  smt(@W32).
  have [# + _] /=:= divmod_mul (2^(i-1)) (2) (to_uint (idx `>>>` j) %/ 2) 1 _ _;1,2:smt(StdOrder.IntOrder.expr_gt0).
  rewrite -exprSr 1:/# /= => ->;rewrite -divz_mulp;1,2:smt(StdOrder.IntOrder.expr_gt0).
  smt(Ring.IntID.exprSr).
case ((idx `>>>` j).[0]);rewrite get_to_uint /= to_uint_shr 1:/# => Hbit.
+ by rewrite to_uintB ? uleE /= to_uint_shr 1:/#; smt( StdOrder.IntOrder.expr_gt0).
rewrite to_uintD_small /= to_uint_shr 1,3:/#;1: by smt( h_max h_g0 leq_div).
have ? : 2*2^j <= 2^h by rewrite -Ring.IntID.exprS; smt(h_g0 ler_weexpn2l).
rewrite mulrDl /= divzE.
have <- : (to_uint idx + 2 ^ j + 2^j <= 2^ h + to_uint idx %% 2 ^ j) <=> 
 (to_uint idx - to_uint idx %% 2 ^ j + 2 ^ j <= 2 ^ h - 2 ^ j)   by smt() .
have -> := (divz_eq (to_uint idx + 2 ^ j + 2 ^ j) (2^j)).
have -> : (to_uint idx + 2 ^ j + 2 ^ j) %% 2 ^ j = to_uint idx %% 2 ^ j by smt().
have -> : ((to_uint idx + 2 ^ j + 2 ^ j) %/ 2 ^ j * 2 ^ j + to_uint idx %% 2 ^ j <= 2 ^ h + to_uint idx %% 2 ^ j) <=> ((to_uint idx + 2 ^ j) + 2 ^ j) %/ 2 ^ j * 2 ^ j  <= 2 ^ h  by smt().
rewrite divzDr;1: smt(le_dvd_pow).
rewrite mulrDl /=.
have -> : 2 ^ j %/ 2 ^ j * 2 ^ j  = 2^j by smt().
pose x:= (to_uint idx + 2 ^ j).
have ? : 0 <= x < 2^h.
+ split => *; 1: by smt(W32.to_uint_cmp).
  rewrite /x (divz_eq (to_uint idx) (2^j)).
  have -> : to_uint idx %/ 2 ^ j * 2 ^ j = to_uint idx %/ 2 ^ j %/ 2 * 2  * 2 ^ j by smt().
  have -> :  to_uint idx %/ 2 ^ j %/ 2 * 2 * 2 ^ j = to_uint idx %/ 2 ^ (j+1) * 2 ^ (j+1).
  + by rewrite !exprS 1:/#  (Ring.IntID.mulrC 2 (2^j)) divzMr /#.
  have ? : to_uint idx %/ 2 ^ (j + 1) * 2 ^ (j + 1)  <= 2^h %/ 2 ^ (j + 1) * 2 ^ (j + 1) by smt().
  have ? : to_uint idx %% 2 ^ j  < 2^j by smt(modz_cmp StdOrder.IntOrder.expr_gt0).
  have ? : (2^h -1 )%/ 2 ^ (j + 1) * 2 ^ (j + 1) + 2^ j + (2^j-1) = 2^h - 1.
   have Hs := modz_pow_split (j+1) j (2^h - 1) 2 _;1:smt().
   rewrite {2} Hs;congr;last by have := powm1_mod h j;smt().
   congr.
   have -> :  (2 ^ h - 1) %% 2 ^ (j + 1) = 2^(j+1) - 1 by have := powm1_mod h (j+1);smt().
   have ? := powm1_mod (j+1) (j) _;1:smt().
   have -> : 2 ^ (j + 1) - 1 = (2^j - 1) + 1*2^j by rewrite exprS 1:/#;ring.
   rewrite divzDr => /=;1:by smt(le_dvd_pow).
   have -> /= : (2 ^ j - 1) %/ 2 ^ j = 0 by smt(divz_small StdOrder.IntOrder.expr_gt0).
   have -> : 2 ^ j %/ 2 ^ j= 1; by smt (StdOrder.IntOrder.expr_gt0).
  apply (ler_lt_trans ((2 ^ h - 1) %/ 2 ^ (j + 1) * 2 ^ (j + 1) + 2 ^ j + (2 ^ j - 1))); last by smt().  
  smt(@StdOrder.IntOrder @IntDiv).
have ? : (x %/ 2 ^ j * 2 ^ j) %% 2^j = 0 by smt(@IntDiv).
have ? : (x %/ 2 ^ j * 2 ^ j) < 2^h by smt(@IntDiv).
case  (x %/ 2 ^ j * 2 ^ j = (2^h-1) %/ 2 ^ j * 2 ^ j); last by smt(@IntDiv).  
by have := powm1_mod h j _; smt(@IntDiv).
qed.


lemma divr2i_p1 m i j :
  0 <= i =>
  i < j =>
  0 <= m < 2 ^ j =>
  m %/ 2 ^ i
  =
  if nth witness (int2bs j m) i
  then 2 * (m %/ 2 ^ (i + 1)) + 1
  else 2 * (m %/ 2 ^ (i + 1)).
proof.
move=> ge0_i ltj_i rngm.
rewrite (int2bs_cat i j) 1:/# nth_cat (: !i < size (int2bs i m)) /=; 1: by smt(size_int2bs).
rewrite size_int2bs (:  (i - max 0 i)  = 0) 1:/#/=.
rewrite (int2bs_cat 1 (j-i)) 1:/# nth_cat (: 0 < size (int2bs 1 (m %/ 2 ^ i))) /=; 1: by smt(size_int2bs).
rewrite /(int2bs 1) nth_mkseq 1:/# /=. 
rewrite exprS 1:/#. 
smt(@IntDiv).
qed.

lemma shrxor1_divr2i m i j :
  0 <= i < 32 =>
  i < j =>
  0 <= to_uint m < 2 ^ j =>
  to_uint ((m `>>` W8.of_int i) `^` W32.one)
  =
  if nth witness (int2bs j (to_uint m)) i
  then to_uint m %/ 2 ^ i - 1
  else to_uint m %/ 2 ^ i + 1.
proof.
move=> rng_i ltj_i rng_m.
rewrite (int2bs_cat i j) 1:/# nth_cat (: !i < size (int2bs i (to_uint m))) /=; 1: by smt(size_int2bs).
rewrite size_int2bs (:  (i - max 0 i)  = 0) 1:/#/=.
rewrite (int2bs_cat 1 (j-i)) 1:/# nth_cat (: 0 < size (int2bs 1 (to_uint m %/ 2 ^ i))) /=; 1: by smt(size_int2bs).
rewrite /(int2bs 1) nth_mkseq 1:/# /= /(`>>`) /= (modz_small _ 256) 1:/#. 

+ case (to_uint m %/ 2 ^ i %% 2 <> 0 ) => Hbit.
  + have ->/= : (m `>>>` i) = W32.of_int (to_uint (m `>>>` i) %/ 2 * 2) + W32.one by smt(@W32 @IntDiv).
    have  /=:= (W32.of_uintK (to_uint m %/ 2 ^ i - 1)).
    rewrite pmod_small; 1: split; 1,2: smt(@IntDiv @W32 pow2_32).
    move => <-; rewrite -to_uint_eq; apply W32.wordP => k kb; rewrite xorwE.
    + case(k = 0).
      + move => ->.
        rewrite !get_to_uint /= !of_uintK /=.
        by rewrite !(pmod_small _ 4294967296); smt(@IntDiv @W32 pow2_32).
    move => ?.
    have ->/= : W32.one.[k] = false by rewrite of_intwE /=; smt(@IntDiv).
    rewrite to_uint_shr /= 1:/# !of_intwE /= /int_bit /= kb /= !(pmod_small _ 4294967296);1,2: by split; smt(@IntDiv @W32 pow2_32).
    do 4!congr; have  -> : 2^k = 2^(k-1)*2 by rewrite -exprSr;smt().
    rewrite !(divzMl);1..4:  smt(StdOrder.IntOrder.expr_gt0).
    by smt(@IntDiv).
+ have ->/= : (m `>>>` i) = W32.of_int (to_uint (m `>>>` i) %/ 2 * 2) by smt(@W32 @IntDiv).
    have  /=:= (W32.of_uintK (to_uint m %/ 2 ^ i + 1)).
    rewrite pmod_small;1: by split; smt(@IntDiv @W32 pow2_32).
    move =><-; rewrite -to_uint_eq; apply W32.wordP => k kb; rewrite xorwE.
    + case(k = 0).
      move => ->; rewrite !get_to_uint /= !of_uintK /=.
      rewrite !(pmod_small _ 4294967296);1,2: by split;smt(@IntDiv @W32 pow2_32).  
      by smt().
    move => ?.
    have -> /=: W32.one.[k] = false.
    + rewrite of_intwE /= kb /int_bit neqF /= pdiv_small; split => // _.
      by rewrite -(Ring.IntID.expr0 2); smt(gt_exprsbde expr_gt0).
    rewrite to_uint_shr /= 1:/# !of_intwE /= /int_bit /= kb /= !(pmod_small _ 4294967296);1,2: by split; smt(@IntDiv @W32 pow2_32).
    do 4!congr; have  -> : 2^k = 2^(k-1)*2 by rewrite -exprSr;smt().
    rewrite !(divzMl);1..4:  smt(StdOrder.IntOrder.expr_gt0).
    by smt(@IntDiv).
qed.

lemma le2i2j m i j :
  0 <= i =>
  i <= j =>
  0 <= m < 2 ^ j =>
  2 ^ i <= 2 ^ j - m %/ 2 ^ i * 2 ^ i.
move => *.
rewrite {1}(divz_eq m (2^(j))).
case (i = j) => *; 1: smt(@IntDiv @Ring.IntID).
have ->/= : m %/ 2 ^ j = 0 by smt().
have ? : (2 ^ j - 1) %/ 2 ^ i * 2 ^ i < 2 ^ j %/ 2 ^ i * 2 ^ i; last by smt(@IntDiv @Ring.IntID).
have <- := int2bsK (j+1) (2 ^ j - 1) _ _;1,2: smt(@StdOrder.IntOrder).
have -> : 2 ^ j %/ 2 ^ i * 2 ^ i = 2^j by smt(@Ring.IntID @IntDiv).
rewrite int2bsS 1:/# /= bs2int_rcons size_int2bs (: max 0 j = j) 1:/#.
have -> /= : b2i ((2 ^ j - 1) %/ 2 ^ j %% 2 <> 0) = 0 by smt(@Ring.IntID @IntDiv).
rewrite int2bsK 1,2:/#.
by smt(@IntDiv).
qed.

lemma cnsh_val ps (idx : W32.t) (i : int) (lfs : dgstblock list) :
     0 <= i
  => i <= h
  => 0 <= to_uint idx < 2 ^ h
  => size lfs = 2 ^ h
  =>
  rev (cons_ap_trh_gen
        (list2tree (take (2 ^ i) (drop ((to_uint idx %/ 2 ^ i) * 2 ^ i) lfs)))
        (rev (take i (int2bs h (to_uint idx))))
        ps (set_typeidx (adr2ads zero_address) 2) i (to_uint idx %/ 2 ^ i))
  =
  mkseq (fun j =>
         val_bt_trh (list2tree (take (2 ^ j) (drop (to_uint ((idx `>>` W8.of_int j) `^` W32.one) * 2 ^ j) lfs)))
         ps (set_typeidx (adr2ads zero_address) 2) j (to_uint ((idx `>>` W8.of_int j) `^` W32.one)))
        i.
proof.
move=> ge0_i.
elim: i ge0_i idx lfs ps.
(* + move=> idx lfs ps ge0_idx; rewrite expr0 size_eq1 => rngidx [lf] ->. *)
+ move=> idx lfs ps ge0_h rngidx eq2s_lfs /=.
  rewrite mkseq0 take0 rev_nil (drop_take1_nth witness) 1:/#.
  rewrite list2tree1 /= rev_nil //.
move=> i ge0_i ih idx lfs ps les_i rngidx eq2s_lfs /=.
rewrite mkseqS 1:// /=.
rewrite {1}exprD_nneg 1,2:// /= (: 2 ^ i * 2 = 2 ^ i + 2 ^ i) 1:/#.
rewrite takeD 1,2:expr_ge0 1,2://.
have ge2i1_if: 2 ^ (i + 1) <= size lfs - to_uint idx %/ 2 ^ (i + 1) * 2 ^ (i + 1).
+ by rewrite eq2s_lfs le2i2j 1:/#.
rewrite (list2treeS i) 1://.
+ rewrite size_take 1:expr_ge0 1:// size_drop 1:mulr_ge0 1:divz_ge0 1:expr_gt0 3:expr_ge0 1,3://; 1: smt(to_uint_cmp).
  by rewrite ifT; move: ge2i1_if; rewrite exprD_nneg; smt(expr_ge0).
+ rewrite size_take 1:expr_ge0 1:// ?size_drop 1:expr_ge0 1://.
  + by rewrite mulr_ge0 1:divz_ge0 1:expr_gt0 3:expr_ge0 1,3://; 1: smt(to_uint_cmp).
  rewrite lez_maxr 1:lez_maxr; 1:smt(expr_ge0).
  + by move: ge2i1_if; rewrite exprD_nneg; smt(expr_ge0).
  by move: ge2i1_if; rewrite exprD_nneg; smt(expr_ge0).
rewrite (take_nth witness) 1:size_int2bs 1:/# rev_rcons /=.
case (nth witness (int2bs h (to_uint idx)) i) => nthv.
+ rewrite rev_cons.
  congr.
  rewrite -(ih idx lfs ps) 1:// 1:/# 1,2://.
  congr. congr. congr. congr.
  rewrite drop_drop 1:expr_ge0 1:// 1:mulr_ge0 1:divz_ge0 1:expr_gt0 3:expr_ge0 1,3://; 1: smt(to_uint_cmp).
  congr.
  rewrite (divr2i_p1 _ i h) 1:// 1:/# 1:// nthv /= exprD_nneg 1,2:// /#.
  by rewrite (divr2i_p1 _ i h) 1:// 1:/# 1:// nthv /=.
  congr. congr. congr. congr.
  rewrite (shrxor1_divr2i _ _ h) 2:/# 2://; 1: smt(h_max).
  rewrite nthv /= mulrDl /=.
  by rewrite (divr2i_p1 _ i h) 1:// 1:/# 1:// nthv /= exprD_nneg 1,2:// /#.
  rewrite (shrxor1_divr2i _ _ h) 2:/# 2://; 1: smt(h_max).
  rewrite nthv /=.
  by rewrite (divr2i_p1 _ i h) 1:// 1:/# 1:// nthv /=.
rewrite rev_cons.
congr.
rewrite -(ih idx lfs ps) 1:// 1:/# 1,2://.
congr. congr. congr. congr. congr.
by rewrite (divr2i_p1 _ i h) 1:// 1:/# 1:// nthv /= exprD_nneg 1,2:// /#.
by rewrite (divr2i_p1 _ i h) 1:// 1:/# 1:// nthv /=.
congr. congr. congr.
rewrite drop_drop 1:expr_ge0 1:// 1:mulr_ge0 1:divz_ge0 1:expr_gt0 3:expr_ge0 1,3://; 1: smt(to_uint_cmp).
congr.
rewrite (shrxor1_divr2i _ _ h) 2:/# 2://; 1: smt(h_max).
rewrite nthv /= mulrDl /=.
by rewrite (divr2i_p1 _ i h) 1:// 1:/# 1:// nthv /= exprD_nneg 1,2:// /#.
rewrite (shrxor1_divr2i _ _ h) 2:/# 2://; 1: smt(h_max).
rewrite nthv /=.
by rewrite (divr2i_p1 _ i h) 1:// 1:/# 1:// nthv /=.
qed.


lemma drop_range i n m :
  0 <= i =>
  drop i (range n m) = range (n + i) m.
proof.
elim: i; 1: by rewrite drop0.
move => i ge0_i ih.
case (m - n <= i + 1) => cs.
+ by rewrite (range_geq (n + _)) 2:drop_oversize 2:size_range /#.
move: ih; rewrite addrA (drop_nth witness) 1:size_range 1:/#.
by rewrite (range_ltn (n + i)) 1:/#.
qed.

lemma take_range i n m :
  0 <= i =>
  0 <= n =>
  take i (range n m) = range n (min (n + i) m).
proof.
elim: i => [ge0_n | i ge0_i ih ge0_n].
+ by rewrite take0 // range_geq 1:/#.
case (m - n <= i + 1) => cs.
+ rewrite take_oversize 1:size_range 1:/#.
  by rewrite lez_minr 1:/#.
rewrite (take_nth witness) 1:size_range 1:/#.
by rewrite ih 1:// nth_range 2:lez_minl 3:-rangeSr /#.
qed.

lemma nthcnsh ss ps (idx : W32.t) (i : int) :
     0 <= i < h
  => 0 <= to_uint idx < 2 ^ h
  => nth witness (cons_ap_trh_gen
                  (list2tree (map (leafnode_from_idx ss ps (adr2ads zero_address)) (range 0 (2 ^ h))))
                  (rev (BS2Int.int2bs h (to_uint idx)))
                  ps (set_typeidx (adr2ads zero_address) 2) h 0)
                 (h - (i + 1))
     =
     val_bt_trh (list2tree (map (leafnode_from_idx ss ps (adr2ads zero_address))
                            (range (to_uint ((idx `>>` W8.of_int i) `^` W32.one) * 2 ^ i)
                                   (to_uint ((idx `>>` W8.of_int i) `^` W32.one) * 2 ^ i + 2 ^ i))))
                ps (set_typeidx (adr2ads zero_address) 2) i
                (to_uint ((idx `>>` W8.of_int i) `^` W32.one)).
proof.
move=> rngi rngidx.
pose cnsap := cons_ap_trh_gen _ _ _ _ _ _.
have sz_cnsap : size cnsap = h.
+ rewrite /cnsap 1:&(szcnsh) 1:/# 2:size_rev 2:size_int2bs 2:/#.
  + by rewrite &(list2tree_height) 1:/# 1:size_map 1:size_range; 1:smt(expr_ge0).
  + rewrite &(list2tree_fullybalanced _ h) 1:/# 1:size_map 1:size_range; 1:smt(expr_ge0).
rewrite -sz_cnsap -nth_rev 1:/#.
move: (cnsh_val ps idx h (map (leafnode_from_idx ss ps (adr2ads zero_address)) (range 0 (2 ^ h))) _ _ _ _) => //.
+ smt(ge0_h).
+ rewrite size_map size_range; smt(size_ge0 ge0_h).
pose cnsapi := cons_ap_trh_gen _ _ _ _ _ _.
have -> ->: cnsap = cnsapi.
rewrite /cnsap /cnsapi.
rewrite (: to_uint idx %/ 2 ^ h = 0) 1:pdiv_small 1,2:// /=.
+ by rewrite drop0 ?take_oversize 1:size_map 1:size_range 2:size_int2bs; smt(expr_ge0 ge0_h).
rewrite nth_mkseq 1:// /=.
rewrite -map_drop -map_take.
rewrite drop_range 1:mulr_ge0 2:expr_ge0 2://.
+ by move: (W32.to_uint_cmp ((idx `>>` W8.of_int i) `^` W32.one)) => /#.
rewrite take_range 1:expr_ge0 1:// /= 1:mulr_ge0 2:expr_ge0 2://.
+ by move: (W32.to_uint_cmp ((idx `>>` W8.of_int i) `^` W32.one)) => /#.
by rewrite lez_minl /=; 1:smt(bnd_uint_bs).
qed.

lemma idx_conv idx:
    0 <= to_uint idx < 2 ^ h
 => to_uint idx
    =
    BS2Int.bs2int (take h (BytesToBits (rev (take n (toByte idx n))))).
proof.
move=> rngidx.
rewrite {1}(: n = size (toByte idx n)) 2:take_size.
+ by rewrite /toByte size_rev size_mkseq; smt(ge1_n).
rewrite /BytesToBits /toByte revK map_mkseq /= /(\o).
pose mks := mkseq _ _.
have ->:
  mks = (chunk 8 (W32.w2bits idx)) ++ (mkseq (fun _ => nseq 8 false) (n - 4)).
+ rewrite /mks {1}(: n = 4 + (n - 4)) 1:// mkseq_add 1://; 1: smt(ge4_n).
  congr.
  + rewrite /chunk size_w2bits &(eq_in_mkseq) => i rngi /=.
    rewrite get_unpack8 1:// /w2bits drop_mkseq 1:/# /= take_mkseq 1:/#.
    rewrite &(eq_in_mkseq) => j rngj @/(\o).
    by rewrite bits8iE // /#.
  rewrite &(eq_in_mkseq) => i rngi /=; rewrite w2bitsE.
  rewrite &(eq_from_nth false) ?size_mkseq 1:size_nseq //= => j rngj.
  by rewrite nth_mkseq 2:nth_nseq 1,2:// /unpack8 initE /= ifF /#.
rewrite flatten_cat take_cat.
rewrite (size_flatten_ctt 8) 2:size_mkseq => //.
+  by move=> bs; apply /in_chunk_size.
rewrite size_w2bits /= ifT; 1: smt(h_max).
rewrite chunkK 1,2:// /to_uint /w2bits (: 32 = h + (32 - h)) 1:/# mkseq_add; 1,2: smt(ge1_h h_max).
rewrite take_cat size_mkseq ifF 2:take_le0 3:cats0; 1,2:smt(ge1_h).
rewrite BS2Int.bs2int_cat eq_sym -{1}Ring.IntID.addr0 eq_sym; congr.
pose mks2 := mkseq _ (32 - h); suff : mks2 = nseq (32 - h) false.
+ by move => ->; rewrite BS2Int.bs2int_nseq_false.
rewrite &(eq_from_nth witness) ?size_mkseq 1:size_nseq 1:// => i rngi.
rewrite nth_mkseq 2:nth_nseq 1,2:/# /=.
suff: b2i idx.[h + i] = 0 by smt().
rewrite b2i_get 2:pdiv_small 2:exprD_nneg //; 1,2,3: smt(ge1_h).
split => [| _]; 1: smt().
rewrite (ltr_le_trans (2 ^ h)); 1: smt(mulr_ge0 expr_ge0).
by rewrite ler_pemulr 1:expr_ge0 1://; smt(mulr_ge0 expr_gt0).
qed.

equiv sig_eq (O <: DSS_RFC.RO.POracle) _idx :
  XMSS_TW_RFC(O).sign ~ XMSS_RFC_Abs(RFC_O(O)).sign :
  ={glob O} /\ skrel sk{1} sk{2} /\ ={m} /\ to_uint sk{2}.`idx = _idx /\ _idx <= 2^h - 1 ==>
  ={glob O} /\  sigrel res{1}.`1 res{2}.`1 /\ to_uint res{2}.`2.`idx = _idx+1 /\ (_idx < 2^h - 1 => skrel res{1}.`2 res{2}.`2).
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
  + rewrite &(Index.val_inj) eqsk21 Index.insubdK.
    rewrite BS2Int.bs2int_ge0 /= /l; pose tkh := take h _.
    + rewrite (: h = size tkh) {1}/tkh 1:size_take; 1: smt(ge1_h).
      + rewrite (size_flatten_ctt 8) => //.
        + by move=> bs /mapP [x] ->; rewrite size_w2bits.
        rewrite size_map size_rev size_take; 1: smt(ge1_n).
        by rewrite size_rev size_mkseq; smt(ge1_n len8_h).
      by rewrite BS2Int.bs2int_le2Xs.
    by rewrite idx_conv; 1:smt(W32.to_uint_cmp).
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
  while{2} (   #pre
            /\ size authentication_path{2} = h
            /\ 0 <= j{2} <= h
            /\ (forall kk, 0 <= kk < j{2} =>
                nth witness (map (fun (b : nbytes) => bs2block b) authentication_path{2}) kk
                =
                (let k = to_uint ((idx1{2} `>>` W8.of_int kk) `^` W32.one) in
                 let _lstart = k * 2 ^ kk in
                 (val_bt_trh (list2tree (map (leafnode_from_idx sk_seed0{2} pub_seed0{2} (adr2ads zero_address)) (range _lstart (_lstart + 2 ^ kk))))
                  pub_seed0{2} (set_typeidx (adr2ads zero_address) trhtype) kk k))))
                  (* (k %/ 2))))) *)
            (h - j{2}); last first.
  + wp; skip => &1 &2 /> eqsk1 eqsk21 eqsk22 eqsk231 eqsk232 le2h1_idx.
    split; 1: smt(size_nseq ge1_h).
    move => apr jr; split => [/# | /lezNgt gehj eqhszap ? lehj apdef].
    rewrite AuthPath.insubdK 1:// ?NBytes.valKd /RFC.skr2sko /=.
    rewrite -/(adr2ads zero_address) XAddress.insubdK /valid_xadrs.
    + by rewrite zeroadsE 1:HAX.Adrs.insubdK 1:zeroadiP 1:zeroxadiP.
    rewrite &(eq_from_nth witness) ?size_rev ?size_map ?DBHL.valP 1:eq_sym 1://.
    move=> i rng_i; rewrite apdef 1:/# nth_rev ?DBHL.valP 1://.
    rewrite /cons_ap_trh /RFC.skr2sko /= DBHL.insubdK /= 1:&(szcnsh); 1: smt(ge1_h).
    + by rewrite &(list2tree_height) 2:size_map 2:size_range; 1,2: smt(ge1_h expr_ge0).
    + by rewrite size_rev BS2Int.size_int2bs; 1: smt(ge1_h).
    + by rewrite &(list2tree_fullybalanced _ h) 2:size_map 2:size_range; smt(ge1_h expr_ge0).
    rewrite eqsk22 eqsk232 eqsk21.
    by rewrite nthcnsh //; smt(W32.to_uint_cmp).
  move=> &1 z.
  wp; sp.
  exlim pub_seed0, sk_seed0, k, j, address1 => ps0t sk0t kt jt adt.
  call (tree_hash_correct ps0t sk0t (kt * 2 ^ jt) jt).
  skip => &2 /> eqsk1 eqsk21 eqsk22 eqsk231 eqsk232 le2h1_idx eqszaph ge0j ? apdef lthj.
  do ? split; 1: by rewrite mulr_ge0 2:expr_ge0 2:// /to_uint 1:BS2Int.bs2int_ge0.
  + move => ?; apply bnd_uint_bs; 1,2: smt(W32.to_uint_cmp).
  + by rewrite dvdz_mull 1:dvdzz.
  move => ? le2jkk ? resr resrval; do ? split; [ by rewrite size_put | smt() | smt() | | smt()].
  move=> kk ge0_k ltj1_kk; case (kk = j{2}) => [eqj | neqj].
  + rewrite (nth_map witness) 1:size_put 1:/# nth_put 1:/# ifT 1:eqj 1:// /bs2block resrval eqj.
    by rewrite mulzK; 1:smt(expr_gt0).
  move: (apdef kk _); 1: smt().
  by rewrite ?(nth_map witness) 1:/# 1:size_put 1:/# nth_put 1:/# ifF 1:eq_sym 1:// => ->.

sp; elim*=> adt.
seq 1 1 : (   #pre
           /\ sigWOTS{1}
              =
              DBLL.insubd (map (fun (b : nbytes) => bs2block b) (LenNBytes.val sig_ots{2}))).
+ inline{1} WOTS_TW_ES.sign; inline{2} WOTS.sign_seed.
  wp.
  while (   ps0{1} = pub_seed0{2} /\ idx_new{2} = skt.`idx + W32.one
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
         /\ size sig0{2} = len
         /\ size sig2{1} <= len
         /\ 0 <= i{2} <= len
         /\ Index.val idx0{1} = to_uint idx0{2}
         /\ to_uint idx0{2} <= 2 ^ h - 1).
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
              /\ 0 <= s{2} < w
              /\ i0{2} = 0
              /\ 0 <= i{2} < len
              /\ to_uint idx0{2} <= 2 ^ h - 1)
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
        + pose ft :=  XMSSRFCAbs.f _ _ _.
          rewrite /BytesToBits (: n = size (map W8.w2bits (NBytes.val ft))).
          + by rewrite size_map NBytes.valP.
          by rewrite (size_flatten_ctt 8) => // bs /mapP [x] ->; rewrite size_w2bits.
        do ? congr.
        rewrite /set_hash_addr /set_chain_addr /set_ots_addr ?setE /=.
        rewrite  /adr2ads /set_hidx /set_idx (HAX.Adrs.insubdK (adr2idxs _)).
        + rewrite /adr2idxs /valid_adrsidxs  1:size_rev.
          rewrite size_map size_sub 1:// /= /valid_xidxvalslp /valid_xidxvalslpch; left.
          rewrite ?nth_put ?nth_rev ?(nth_map witness) ?size_rev ?size_put ?size_map ?size_iota //=.
          rewrite ?initE ?nth_iota //= ifT 2:ifF 1,2:// ifT 2:ifT 1,2:// ifT 2:ifF 1,2://.
          rewrite ?initE /= ifT //= ifF 1:// ifT 1:// ifT 1:// initE /= ifT 1://= to_uint0 /=.
          rewrite ifT 2:ifF 1,2:// ifT 1://; split; 1:smt(w_vals ge2_len).
          split; 1: rewrite /valid_chidx to_uintK_small 2://.
          + by split => // _; rewrite (IntOrder.ltr_trans len) 1:// 1:ltW32_len.
          by rewrite ifF 1:// initE ifT 1:// /=; smt(W32.to_uint_cmp).
        rewrite HAX.Adrs.insubdK /adr2idxs /valid_adrsidxs 1:size_put 1:size_rev.
        + rewrite size_map size_sub 1:// /= /valid_xidxvalslp /valid_xidxvalslpch; left.
          rewrite ?nth_put ?nth_rev ?(nth_map witness) ?size_rev ?size_put ?size_map ?size_iota //=.
          rewrite ?initE ?nth_iota //= ifT 2:ifT 1,2:// ifT 2:ifF 1,2:// ifT 2:ifF 1,2://.
          rewrite ?initE /= ifT //= ifT 1:// ifT 1:// ifF 1:// initE /= ifT 1://= to_uint0 /=.
          split; 1 :smt(w_vals ge2_len).
          split; 1: rewrite /valid_chidx to_uintK_small 2://.
          + by split => // _; rewrite (IntOrder.ltr_trans len) 1:// 1:ltW32_len.
          by smt(W32.to_uint_cmp).
        rewrite /idxs2adr; apply ext_eq => j rngj /=.
        rewrite ?initE rngj /=.
        case (3 <= j <= 6) => subrngi; last first.
        + by do ? (rewrite ifF 1:/# initE rngj /=).
        rewrite 1:nth_put 2:nth_rev ?size_rev ?size_map ?size_sub ?size_iota 1,2:// 1:/#.
        case (j = 6) => [// /#| neq6j].
        rewrite initE rngj /= neq6j /= ifF 1:/# (nth_map witness) 1:size_sub // 2:nth_sub 1,2:/#.
        rewrite ?initE rngj /=.
        case (j = 5) => [// /#| neq5j].
        by case (j = 4) => /#.
      rewrite /set_hash_addr ?setE /=; congr; rewrite fun_ext => i.
      case (i = 6) => [// /#| ?].
      rewrite initE /=.
      case (0 <= i < 8) => rngi //. by rewrite ifF.
      by rewrite get_out.
    skip => &1 &2 /> ? skeq *.
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
    rewrite (nth_map witness) 1:EmsgWOTS.valP //; 1: smt(BaseW.valP).
    rewrite (nth_map witness) 1:EmsgWOTS.valP //; 1: smt(BaseW.valP).
    rewrite (nth_map witness) 1:EmsgWOTS.valP //; 1: smt(BaseW.valP).
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
    rewrite XAddress.insubdK /valid_xadrs HAX.Adrs.insubdK 1:zeroadiP 1:zeroxadiP.
    by rewrite HAX.Adrs.insubdK 1:zeroadiP /put /=; smt(w_vals gt2_len Index.valP).
    congr. rewrite HAX.Adrs.insubdK 1:zeroadiP /put /= ifF 1:/#.
    rewrite /set_hash_addr /set_chain_addr /set_ots_addr ?setE /=.
    + rewrite /adr2idxs &(eq_from_nth witness) 1:size_rev 1:size_map 1:size_sub 1,2:// /=.
      move => j rngj.
      rewrite nth_rev ?size_map ?size_sub ?size_iota 1,2://.
      rewrite (nth_map witness) ?size_sub 1:// 2:nth_sub 1,2:/#.
      rewrite initE (: 0 <= 3 + (max 0 4 - (j + 1)) < 8) 1:/# /=.
      case (j = 0) => [/= -> | neq0j].
      + by rewrite ifF 1:/#.
      case (j = 1) => [/= -> | ?].
      + rewrite ifT 2:ifT 1,2:/# to_uintK_small; split => // _.
        apply (IntOrder.ltr_trans len) => //; apply ltW32_len.
      case (j = 2) => [/= -> /=| ?].
      + rewrite ifF 1:// initE ifT 1:// /= ifF 1:// initE ifT 1:// /= ifT //.
      case (j = 3) => [/= -> /=| ? /#].
      by rewrite ifF 1:// initE ifT 1:// /= ifF 1:// initE ifT 1:// /= ifF //.
    rewrite nth_rcons nth_put 1:/#.
    case (j < size sig2{1}) => ?; [ rewrite ifF /# | rewrite ?ifT; 1,2: smt(size_rcons)].
    rewrite /bs2block; move/(congr1 DigestBlock.insubd): (H0) => ->.
    rewrite DigestBlock.valKd; congr.
    rewrite /set_chain_addr /set_ots_addr ?setE /=.
    rewrite /adr2ads /set_kpidx zeroidxsE /set_idx.
    rewrite XAddress.insubdK /valid_xadrs ?HAX.Adrs.insubdK ?zeroadiP ?zeroxadiP.
    rewrite /put /= /set_chidx /set_idx HAX.Adrs.insubdK.
    + rewrite /valid_adrsidxs /= /valid_xidxvalslp /valid_xidxvalslpch /=; left; smt(w_vals gt2_len Index.valP).
    congr.
    rewrite /adr2idxs &(eq_from_nth witness) 1:size_rev 1:size_map 1:size_sub 1,2:// /= /put /=.
    move => jt rngj.
      rewrite nth_rev ?size_map ?size_sub ?size_iota 1,2://.
      rewrite (nth_map witness) ?size_sub 1:// 2:nth_sub 1,2:/#.
      rewrite initE (: 0 <= 3 + (max 0 4 - (jt + 1)) < 8) 1:/# /=.
      case (jt = 0) => [/= -> | neq0j].
      + by rewrite ifF 1:/#.
      case (jt = 1) => [/= -> | ?].
      + rewrite ifT 2:ifT 1,2:/# to_uintK_small; split => // _.
        apply (IntOrder.ltr_trans len) => //; apply ltW32_len.
      case (jt = 2) => [/= -> /=| ?].
      + rewrite ifF 1:// initE ifT 1:// /= ifF 1:// initE ifT 1:// /= ifT //.
      case (jt = 3) => [/= -> /=| ? /#].
      by rewrite ifF 1:// initE ifT 1:// /= ifF 1:// initE ifT 1:// /= ifF //.
    by move/lezNgt: H H3; rewrite ?(nth_map witness) 1:EmsgWOTS.valP // /#.
    rewrite skeq (nth_map witness) 1:LenNBytes.valP // /bs2block DigestBlock.insubdK //.
    rewrite /BytesToBits (: n = size (map W8.w2bits (NBytes.val (nth witness (LenNBytes.val wots_skey{2}) (size sig2{1}))))).
    + by rewrite size_map NBytes.valP.
    by rewrite (size_flatten_ctt 8) => // bs /mapP [x] ->; rewrite size_w2bits.
    by rewrite size_rcons.
    smt(size_put).
    by rewrite size_rcons /#.
    smt(size_ge0).
    smt(size_ge0).
    smt(size_rcons).
    smt(size_rcons).
  wp -1 -1.
  sp; seq 1 1 : (#pre /\ DBLL.val skWOTS0{1} = map bs2block (LenNBytes.val wots_skey{2})).
  + conseq (: DBLL.val skWOTS0{1} = map bs2block (LenNBytes.val wots_skey{2}))=> //.
    call genSK_eq; auto=> /> &1 &2 sk1 sk21 sk22 sk231 sk232 skt_idx ap_eq.
    rewrite -sk21 /adr2ads /adr2idxs /set_ots_addr /set_type /sub /zero_address.
    rewrite -map_rev /mkseq -map_rev //= rev_iota.
    (* Use user reduction? *)
    rewrite (iotaS _ 3) // (iotaS _ 2) // (iotaS _ 1) // (iota1) //=.
    (* This is probably simplifiable---copy-pasted without thought from old proof *)
    rewrite /RFC.skr2sko XAddress.insubdK /valid_xadrs ?HAX.Adrs.insubdK ?zeroidxsE ?zeroadiP ?zeroxadiP /=.
    rewrite /set_typeidx HAX.Adrs.insubdK 1:valid_xadrsidxs_adrsidxs 1:zeroxadiP /put /=.
    rewrite /set_kpidx /set_idx HAX.Adrs.insubdK 1:valid_xadrsidxs_adrsidxs 1:zeroxadiP /put /=.
    rewrite to_uint_small /=; 1:smt(Index.valP ge1_h h_max pow2_32 gt_exprsbde).
    split; 1: smt(Index.valP ge1_h h_max pow2_32 gt_exprsbde w_vals gt2_len).
    move=> j ge0_j lt3_j; rewrite ?setE ?initE.
    rewrite ifT 1:/# /=.
    by do ? (rewrite ifF 1:/# ?initE ifT 1:/# ?initE /=).
  outline{2} [1 .. 8] by { msg <@ WOTS_Encode.encode(M0); }.
  ecall{2} (WOTSEncodeP M0{2}).
  skip => &1 &2 />.
  progress.
  rewrite /len1 NBytes.valP -log2w_eq -fromint_div; 1: smt(logw_vals).
  by rewrite from_int_ceil mulrC divMr; smt(logw_vals).
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
  rewrite nth_rev; 1: smt(size_rev size_map size_sub).
  rewrite (nth_map witness); 1: smt(size_rev size_map size_sub).
  rewrite nth_sub; 1: smt(size_rev size_map size_sub).
  by do ? (rewrite initE /=); smt(size_rev size_map size_sub W32.initE W32.to_uintK_small W32.to_uint0 Index.valP ge1_h).
  rewrite /bs2block DigestBlock.insubdK /BytesToBits.
  rewrite (: n = size (map W8.w2bits (NBytes.val _M'{2}))) 1:size_map 1:NBytes.valP 1://.
  by rewrite (size_flatten_ctt 8) => // bs /mapP [x] ->; rewrite size_w2bits.
  rewrite -/EmsgWOTS.ofemsgWOTS EmsgWOTS.ofemsgWOTSK //.
  rewrite /encode_int size_cat /checksum /int2lbw /= ?size_mkseq.
  smt(ge1_len1 ge1_len2).
  by rewrite /BytesToBits flattenK 1://; 1: move=> x /mapP [y [_ ->]]; 1: by rewrite size_w2bits.
  smt().
  rewrite size_nseq. smt(ge0_len).
  smt(ge2_len).
  smt(Params.ge0_len).
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

lemma flrdv_intdiv i d:
  0 <= i => 1 <= d => floor (i%r / d%r) = i %/ d.
proof.
move => rngi rngd; rewrite floorP.
rewrite RField.mulrC; split => [|_].
+ by rewrite RealOrder.ler_pdivl_mull 1:/# -fromintM le_fromint; smt(leq_trunc_div).
by rewrite RealOrder.ltr_pdivr_mull 1:/# -fromintD -fromintM lt_fromint; smt(ltz_ceil).
qed.

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
      This exactly requires that the index on
      the RFC/implementation side can be injected into the
      Index subtype (without losing values), which is also why
      we have the `take h`
    *)
    pose tkh := take h _; rewrite (ltr_le_trans (2 ^ (size tkh))); 1: smt(BS2Int.bs2int_le2Xs).
    rewrite ler_weexpn2l // size_take 2:(size_flatten_ctt 8); 1: smt(ge1_h).
    + by move=> x /mapP [t] ->; rewrite size_w2bits.
    rewrite size_map /toByte ?size_rev size_mkseq; smt(ge1_n ge1_h).
    rewrite eqs21 idx_conv; 1: smt(Index.valP).
    do 3! congr; pose tb := toByte _ n; rewrite (: n = size tb) 1:/tb 2:take_size 2://.
    by rewrite size_rev size_mkseq; smt(ge1_n).
  move=> *.
  do ? split; 1: smt(Index.valP).
  + rewrite eqs22 DBLL.insubdK 1:size_map 1:LenNBytes.valP 1://.
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
+ call pkFromSig_eq; auto=> /> &1 &2 ->.
  move=> eqpk1 eqpkoid idx_sig_lt_l -> eqsig eqauth eqcm eqpkr @/RFC.pkr2pko.
  rewrite /= zeroidxsE XAddress.insubdK.
  + by rewrite /valid_xadrs HAX.Adrs.insubdK 1:zeroadiP zeroxadiP.
  rewrite /set_typeidx /set_kpidx HAX.Adrs.insubdK /put /= 1:zeroadiP.
  rewrite /set_idx ?HAX.Adrs.insubdK /put 1:zeroadiP /=.
  + by rewrite /valid_adrsidxs /= /valid_xidxvalslp /valid_xidxvalslpch /=; left; smt(w_vals ge2_len W32.to_uint_cmp).
  split; 2: smt(w_vals ge2_len W32.to_uint_cmp).
  rewrite /ads2adr /set_type /set_ots_addr HAX.Adrs.insubdK.
  + by rewrite /valid_adrsidxs /= /valid_xidxvalslp /valid_xidxvalslpch /=; left; smt(w_vals ge2_len W32.to_uint_cmp).
  rewrite /idxs2adr /zero_address &(ext_eq) => i rngi.
  rewrite ?setE ?initE rngi /=; case (3 <= i <= 6) => subrngi.
  + case (i = 6) => [// | ns]; case (i = 5) => [// | nf /=]; rewrite ?initE rngi /=.
    by case (i = 4) => [// | nfr /=]; case (i = 3) => [// | /#].
  rewrite ifF 1:/# initE rngi /=.
  case (i = 7) => [// | nfs /=]; rewrite initE rngi /=.
  by do ? (rewrite ifF 1:/# initE rngi /=).
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
          /\ (forall i, 0 <= i < 5 \/ i = 7 =>
              address0{2}.[i] = if i = 3 then W32.of_int 2 else W32.zero)
          /\ get_tree_index address0{2} = (to_uint idx_sig0{2} %/ 2 ^ k{2})
          /\ to_uint idx_sig0{2} < l
          /\ 0 <= k{2} <= h)
         (h - k{2}).
+ move => _ z.
  proc change 2 : (! odd (to_uint idx_sig0 %/ 2 ^ k)).
  + move=> &2; rewrite oddPn.
    by rewrite flrdv_intdiv; smt(W32.to_uint_cmp expr_gt0).
  auto => &2 /> eqnds ad0get ad0tidx ltl ge0k _ lthk; split => parity.
  + do ? split; 4..: smt(); last first.
    + move: ad0tidx.
      rewrite /get_tree_index /set_tree_index /set_tree_height.
      rewrite ?get_setE 1,2:// /= => ->.
      rewrite exprD_nneg 1,2:// divz_mul 1:expr_ge0 1://.
      rewrite to_uintK_small //; split => [|_].
      + by rewrite 2?divz_ge0 1:// 1:expr_gt0 1://; 1: smt(W32.to_uint_cmp).
      rewrite &(IntOrder.ler_lt_trans (to_uint idx_sig0{2})).
      rewrite -divz_mul 1:expr_ge0 1:// leq_div 2:mulr_ge0 2:expr_ge0 2,3://; 1: smt(W32.to_uint_cmp).
      by rewrite &(IntOrder.ltr_trans l) 1:// /l; smt(pow2_32 h_max gt_exprsbde).
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
    + rewrite ?setE &(ext_eq) => i rngi.
      pose adr := idxs2adr _.
      rewrite (: adr = Array8.init (fun (j : int) =>
                                  if j = 3 then W32.of_int 2 else
                                  if j = 5 then W32.of_int (k{2} + 1) else
                                  if j = 6 then W32.of_int (to_uint idx_sig0{2} %/ 2 ^ (k{2} + 1)) else W32.zero)).
      rewrite /adr /adr2ads /set_thtbidx (HAX.Adrs.insubdK (adr2idxs _)).
      + rewrite /adr2idxs /valid_adrsidxs /set_type 1:size_rev.
        rewrite size_map size_sub 1:// /= /valid_xidxvalslp /valid_xidxvalslptrh; right; right.
        rewrite ?nth_put ?nth_rev ?(nth_map witness) ?size_rev ?size_put ?size_map ?size_iota //=.
        rewrite ?setE ?initE ?nth_iota //= ifT 2:ifF 1,2:// ifT 2:ifF 1,2:// ifT 2:ifF 1,2://.
        rewrite ?initE /= ifT //= ifF 1:// ifT 1:// ifT 1:// initE /= ifT 1://= to_uint0 /=.
        rewrite ifT 2:ifF 1,2:// ifT 1:// ?initE ifT 1:// ifF 1:// /= ifF 1://.
        rewrite ifT 2:ifF 1,2:// ifT 1:// ?initE ifT 1:// ifF 1:// /= ifT 1:// ifT 1:// ifF 1://.
        by rewrite initE ifT 1:// /= ifT 1://; smt(expr_ge0 expr_gt0).
      rewrite HAX.Adrs.insubdK /adr2idxs /valid_adrsidxs ?size_put ?size_rev ?size_map ?size_iota /=.
      split; 1:smt().
      rewrite /valid_xidxvalslp /valid_xidxvalslptrh; right; right.
      rewrite ?nth_put ?size_put ?size_rev ?size_map ?size_iota //=.
      rewrite ?nth_rev ?(nth_map witness) ?nth_iota ?size_map ?size_iota //=.
      rewrite /set_type ?setE initE ifT 1:/# /= ifF 1:/# initE ifT 1:/# /= ifF 1:/#.
      rewrite /set_type ?setE.
      rewrite initE ifT 1:/# /= ifF 1:/# initE ifT 1:/# /= ifT 1:/#.
      rewrite initE ifT 1:/# /= ifF 1:/#  initE ifT 1:/# /=.
      rewrite initE ifF 1:/# /= ifT 1:/#  initE ifF 1:/# /=.
      rewrite initE ifT 1:/# /= ifF 1:/#  initE ifT 1:/# /=.
      rewrite ifT 1:/# /=.
      rewrite /valid_tbidx /valid_thidx; split; 2:smt().
      rewrite divz_ge0 1:expr_gt0 1://; split=>[|_]; 1:smt(W32.to_uint_cmp).
      by rewrite /nr_nodes ltz_divLR 1:expr_gt0 1:// -exprD_nneg; smt(ge1_h).
      rewrite /idxs2adr; apply ext_eq => j rngj /=.
    rewrite ?initE rngj /=.
    case (3 <= j <= 6) => subrngi; last first.
    + by rewrite ifF 1:/# ifF 1:/# ifF 1:/#.
    rewrite ?nth_put ?nth_rev ?size_put ?size_rev ?size_map ?size_sub ?size_iota 1,2:// 1:/#.
    case (j = 6) => [// /#| neq6j].
    case (j = 5) => [// /#| neqj].
    rewrite ifF 1:/# ifF 1:/# (nth_map witness) 1:size_sub 1:// 1:/# nth_sub 1:/# /=.
    rewrite /set_type ?setE initE ifT 1:/# /= ifF 1:/# initE ifT 1:/# /= ifF 1:/#.
    rewrite  initE ifT 1:/# /= ifF 1:/#  initE ifT 1:/# /=.
    case (j = 3) => [// /#| /#].
  rewrite /set_tree_index /set_tree_height /get_tree_height /= ?setE ?initE rngi /=.
  case (i = 6) => eqi6.
  + by rewrite ifF 1:/# initE rngi /= ifF 1:/# eqi6.
  case (i = 5) => eqi5.
  + by rewrite initE rngi eqi5 /= to_uintK_small //; smt(pow2_32 h_max gt_exprsbde).
  rewrite ?initE rngi /= eqi5 /= eqi6 /= /#.
  + do ? congr.
      rewrite exprD_nneg 1,2:// divz_mul 1:expr_ge0 1://.
      by move/oddWn: parity => -[a' ^ eqa -> /=]; rewrite mulKz 1://.
    rewrite (nth_map witness) 1:AuthPath.valP 1:// /bs2block.
    rewrite DigestBlock.insubdK.
    + rewrite (size_flatten_ctt 8); 1: by move=> y /mapP [t] ->; rewrite size_w2bits.
      by rewrite size_map NBytes.valP.
    by rewrite BytesToBitsK NBytes.valKd.
    move=> i vali.
    rewrite /get_tree_index /set_tree_index /set_tree_height ?get_setE 1..3:// /=.
    by rewrite ifF 2:ifF /#.
  do ? split; 4..: smt(); last first.
  move: (ad0tidx).
  rewrite /get_tree_index /set_tree_index /set_tree_height.
  rewrite ?get_setE 1,2:// /= => ->.
  rewrite exprD_nneg 1,2:// divz_mul 1:expr_ge0 1://.
  move/oddW: (parity) => -[a' ^ eqa -> /=].
  rewrite divzDl 1:dvdz_mulr 1:dvdzz mulKz // divz_small // /=.
  rewrite to_uintK_small 2://.
  move/(congr1 (transpose (%/) (2))): eqa.
  move: (divzMDl a' 1 2 _) => //.
  rewrite (divz_small 1 2) 1:// /= mulrC => ->.
  rewrite -divz_mul 1:expr_ge0 1:// -{2}(Ring.IntID.expr1 2) -exprD_nneg 1,2:// => <-.
  rewrite divz_ge0 1:expr_gt0 1://; split => [|_]; 1:smt(W32.to_uint_cmp).
  rewrite ltz_divLR 1:expr_gt0 1://.
  rewrite -Ring.IntID.mulr1 ltr_pmul 2://; 1,2: smt(W32.to_uint_cmp pow2_32 h_max).
  by rewrite exprn_egt1 1,3:/#.
  (* rewrite (drop_nth witness). *)
  (* + by rewrite size_map AuthPath.valP; smt(ge1_h). *)
  move: (ad0tidx).
  rewrite /get_tree_index /set_tree_index /set_tree_height.
  rewrite ?get_setE 1,2:// /= => ->.
  rewrite exprD_nneg 1,2:// divz_mul 1:expr_ge0 1://.
  move/oddW: (parity) => -[a' ^ eqa -> /=].
  rewrite divzDl 1:dvdz_mulr 1:dvdzz mulKz // divz_small // /=.
  rewrite (take_nth witness); 1: by rewrite size_map AuthPath.valP; smt(ge1_h).
  rewrite rev_rcons BS2Int.int2bsS 1:// rev_rcons /= ifT 1:-oddP 1://.
  (* rewrite (: (h - (k{2} + 1) + 1) = h - k{2}) 1:/# /trh /=. *)
  rewrite /trh /= ifF; 1: smt(ge1_n).
  move/(congr1 BitsToBytes) /(congr1 NBytes.insubd): eqnds.
  rewrite BytesToBitsK NBytes.valKd => ->.
  (* move: ad0tidx; rewrite /set_tree_height /get_tree_index get_setE 1:// /=. *)
  (* move => ->; move/oddW: (parity) => [ a ^ adf -> /=]. *)
  (* rewrite mulKz //= *)
  rewrite take_cat drop_cat ?DigestBlock.valP /= take0 drop0 cats0.
  rewrite -eqa DigestBlock.insubdK.
  + rewrite (size_flatten_ctt 8); 1: by move=> y /mapP [t] ->; rewrite size_w2bits.
    by rewrite size_map NBytes.valP.
  do 3! congr.
  + rewrite ?setE &(ext_eq) => i rngi.
    pose adr := idxs2adr _.
    rewrite (: adr = Array8.init (fun (j : int) =>
                                  if j = 3 then W32.of_int 2 else
                                  if j = 5 then W32.of_int (k{2} + 1) else
                                  if j = 6 then W32.of_int a' else W32.zero)).
    + rewrite /adr /adr2ads /set_thtbidx (HAX.Adrs.insubdK (adr2idxs _)).
      + rewrite /adr2idxs /valid_adrsidxs /set_type 1:size_rev.
        rewrite size_map size_sub 1:// /= /valid_xidxvalslp /valid_xidxvalslptrh; right; right.
        rewrite ?nth_put ?nth_rev ?(nth_map witness) ?size_rev ?size_put ?size_map ?size_iota //=.
        rewrite ?setE ?initE ?nth_iota //= ifT 2:ifF 1,2:// ifT 2:ifF 1,2:// ifT 2:ifF 1,2://.
        rewrite ?initE /= ifT //= ifF 1:// ifT 1:// ifT 1:// initE /= ifT 1://= to_uint0 /=.
        rewrite ifT 2:ifF 1,2:// ifT 1:// ?initE ifT 1:// ifF 1:// /= ifF 1://.
        rewrite ifT 2:ifF 1,2:// ifT 1:// ?initE ifT 1:// ifF 1:// /= ifT 1:// ifT 1:// ifF 1://.
        by rewrite initE ifT 1:// /= ifT 1://; smt(expr_ge0 expr_gt0).
      rewrite HAX.Adrs.insubdK /adr2idxs /valid_adrsidxs ?size_put ?size_rev ?size_map ?size_iota /=.
      split; 1:smt().
      rewrite /valid_xidxvalslp /valid_xidxvalslptrh; right; right.
      rewrite ?nth_put ?size_put ?size_rev ?size_map ?size_iota //=.
      rewrite ?nth_rev ?(nth_map witness) ?nth_iota ?size_map ?size_iota //=.
      rewrite /set_type ?setE initE ifT 1:/# /= ifF 1:/# initE ifT 1:/# /= ifF 1:/#.
      rewrite /set_type ?setE.
      rewrite initE ifT 1:/# /= ifF 1:/# initE ifT 1:/# /= ifT 1:/#.
      rewrite initE ifT 1:/# /= ifF 1:/#  initE ifT 1:/# /=.
      rewrite initE ifF 1:/# /= ifT 1:/#  initE ifF 1:/# /=.
      rewrite initE ifT 1:/# /= ifF 1:/#  initE ifT 1:/# /=.
      rewrite ifT 1:/# /=.
      rewrite /valid_tbidx /valid_thidx; split; 2:smt().
      move/(congr1 (transpose (%/) (2))): eqa.
      move: (divzMDl a' 1 2 _) => //.
      rewrite (divz_small 1 2) 1:// /= mulrC => ->.
      rewrite -divz_mul 1:expr_ge0 1:// -{2}(Ring.IntID.expr1 2) -exprD_nneg 1,2:// => <-.
      rewrite divz_ge0 1:expr_gt0 1://; split => [|_]; 1:smt(W32.to_uint_cmp).
      by rewrite /nr_nodes ltz_divLR 1:expr_gt0 1:// -exprD_nneg; smt(ge1_h).
    rewrite /idxs2adr; apply ext_eq => j rngj /=.
    rewrite ?initE rngj /=.
    case (3 <= j <= 6) => subrngi; last first.
    + by rewrite ifF 1:/# ifF 1:/# ifF 1:/#.
    rewrite ?nth_put ?nth_rev ?size_put ?size_rev ?size_map ?size_sub ?size_iota 1,2:// 1:/#.
    case (j = 6) => [// /#| neq6j].
    case (j = 5) => [// /#| neqj].
    rewrite ifF 1:/# ifF 1:/# (nth_map witness) 1:size_sub 1:// 1:/# nth_sub 1:/# /=.
    rewrite /set_type ?setE initE ifT 1:/# /= ifF 1:/# initE ifT 1:/# /= ifF 1:/#.
    rewrite  initE ifT 1:/# /= ifF 1:/#  initE ifT 1:/# /=.
    case (j = 3) => [// /#| /#].
  rewrite /set_tree_height /get_tree_height /= ?setE ?initE rngi /=.
  case (i = 6) => eqi6.
  + by rewrite ifF 1:/# initE rngi /= ifF 1:/# eqi6.
  case (i = 5) => eqi5.
  + by rewrite initE rngi eqi5 /= to_uintK_small //; smt(pow2_32 h_max gt_exprsbde).
  rewrite ?initE rngi /= eqi5 /= eqi6 /= /#.
  + rewrite (nth_map witness) 1:AuthPath.valP 1:// /bs2block.
    rewrite DigestBlock.insubdK.
    + rewrite (size_flatten_ctt 8); 1: by move=> y /mapP [t] ->; rewrite size_w2bits.
      by rewrite size_map NBytes.valP.
    by rewrite BytesToBitsK NBytes.valKd.
    move=> i vali.
    rewrite /get_tree_index /set_tree_index /set_tree_height ?get_setE 1..3:// /=.
    by rewrite ifF 2:ifF /#.
auto => &1 &2 /> eqpk1 eqpk2 ? ltlidx eqidx eqsfl2 eqsfl3 eqcm eqpk11 eqpkots.
split.
+ split.
  + rewrite BS2Int.int2bs0s take0 ?rev_nil //= /bs2block.
    rewrite DigestBlock.insubdK 2://.
    rewrite (size_flatten_ctt 8); 1: by move=> y /mapP [t] ->; rewrite size_w2bits.
    by rewrite size_map NBytes.valP.
  split; 2: smt(ge0_h).
  move=> i vali.
  rewrite /get_tree_index /set_tree_index /set_tree_height ?get_setE 1..3:// //.
  case (i = 3) => // neqi3.
  case (i = 4) => // neqi4.
  case (i = 7) => // neqi7.
  by rewrite initE /= /#.
move=> ad0r kr ndsr; split; 1: smt().
move/lezNgt => gehk + ad0get tridx + leh_kr @/RFC.pkr2pko /=.
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
  rewrite zeroidxsE XAddress.insubdK.
  + by rewrite /valid_xadrs HAX.Adrs.insubdK 1:zeroadiP zeroxadiP.
  rewrite /set_typeidx (HAX.Adrs.insubdK [0;0;0;0]) 1:valid_xadrsidxs_adrsidxs 1:zeroxadiP /put /=.
  rewrite /set_kpidx /set_idx (HAX.Adrs.insubdK [0;0;0;1]).
  rewrite /valid_adrsidxs /= /valid_xidxvalslp /valid_xidxvalslppkco /=; right; left.
  rewrite /valid_kpidx; smt(expr_gt0).
  rewrite HAX.Adrs.insubdK /put /= /valid_adrsidxs /= /valid_xidxvalslp /valid_xidxvalslppkco /=.
  right; left; smt(Index.valP expr_gt0).
  rewrite /set_ltree_addr /set_type /set_ots_addr ?setE /idxs2adr /=.
  rewrite &(ext_eq) => j rngj; rewrite ?initE rngj /=.
  case (3 <= j <= 6) => subrngi; last first.
  + rewrite ifF 1:/# /= initE rngj /=.
    case (j = 7) => // ?.
    do ? (rewrite initE rngj /= ifF 1:/#).
    by rewrite initE rngj /=.
  case (j = 4) => ?.
  + by rewrite 2?ifF 1,2:/# ifT 1:/# eqidx to_uintK.
  rewrite initE rngj /= eq_sym ifF 1:/# initE rngj /=.
  case (j = 6) => ?.
  + by rewrite ifT /#.
  rewrite initE rngj /= eq_sym ifF 1:/# initE rngj /=.
  case (j = 5) => ?.
  + by rewrite ifT /#.
  by rewrite (: j = 3) /#.
  rewrite &(LenNBytes.val_inj) &(inj_map NBytes.val NBytes.val_inj).
  move/(congr1 (List.map BitsToBytes)): (eqpkots).
  rewrite -(map_comp BitsToBytes (BytesToBits \o NBytes.val)).
  rewrite (eq_map (_ \o (_ \o NBytes.val)) NBytes.val); 1: smt(BytesToBitsK).
  move => <-; rewrite LenNBytes.insubdK 1:size_map 1:size_chunk; 1: smt(ge1_n).
  + rewrite size_map size_chunk 1:// (size_flatten_ctt (8 * n)); 1: by move=> y /mapP [t] ->; rewrite DigestBlock.valP.
    by rewrite size_map DBLL.valP mulzA ?mulKz 1://; smt(ge1_n).
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
  by rewrite /chn chfltn_id.
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


(*** Security reduction (moved from XMSS_Security_RFCAbs_Reduction) *)
require (*****) DigitalSignaturesROM.
clone import DigitalSignaturesROM as DSS_TOP with
  type pk_t <- xmss_pk,
  type sk_t <- xmss_sk,
  type msg_t <- msg_t,
  type sig_t <- sig_t,

  type in_t <- nbytes * (dgstblock * index * msg_t),
  type out_t <- msgFLXMSSTW,
  type d_in_t <- int,
  type d_out_t <- bool,

    op doutm <- fun _ => duniform DigestBlockFT.enum

proof *.
import DSS.
import KeyUpdating.
import KeyUpdatingROM.

module (S : Scheme_RO) (O : RO.POracle) = {
   proc keygen() = {
      var kp;
      kp <@ XMSS_RFC_Abs(RFC_O(O)).kg();
      return (kp.`2,kp.`1);
   }

   proc sign = XMSS_RFC_Abs(RFC_O(O)).sign

   (* THIS IS A HACK BECAUSE RFC SHOULD BE CHECKING FOR IDX RANGE.  *)
   proc verify(pk : xmss_pk, m : msg_t, sig : sig_t) : bool  = {
       var r;
       r <@ XMSS_RFC_Abs(RFC_O(O)).verify(pk,m,sig);
       return 0 <= to_uint sig.`sig_idx < l && r;
   }
}.

module B_Oracles(O : DSS_RFC.DSS.KeyUpdating.SOracle_CMA) : SOracle_CMA = {
   proc sign(m : msg_t) : sig_t = {
      var sig;
      sig <@ O.sign(m);
      return ({| sig_idx = W32.of_int (Index.val sig.`2.`1) ; r = sig.`1;

          r_sig = (LenNBytes.insubd (map NBytes.insubd (map (BitsToBytes \o DigestBlock.val) (DBLL.val sig.`2.`2))),
                  AuthPath.insubd (rev (map NBytes.insubd (map  (BitsToBytes \o DigestBlock.val) (DBHL.val sig.`2.`3))))) |});
   }
}.

module (B(A : Adv_EUFCMA_RO) : DSS_RFC.KeyUpdatingROM.Adv_EUFCMA_RO) (RO : RO.POracle, O : DSS_RFC.DSS.KeyUpdating.SOracle_CMA) = {
   proc forge(pk : pkXMSSTWRFC) : msg_t * sigXMSSTW = {
         var f;
         f <@ A(RO,B_Oracles(O)).forge({| pk_oid = impl_oid; pk_root = NBytes.insubd (BitsToBytes (DigestBlock.val pk.`1)); pk_pub_seed = pk.`2|});
         return (f.`1,
          (f.`2.`r,
            (Index.insubd (to_uint f.`2.`sig_idx),
             DBLL.insubd (map (fun (b : nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (LenNBytes.val f.`2.`r_sig.`1)),
             DBHL.insubd (rev (map (fun (b : nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (AuthPath.val f.`2.`r_sig.`2))))));
   }
}.

lemma verify1_ll (O <: RO.Oracle) : islossless O.o => islossless XMSS_RFC_Abs(RFC_O(O)).verify.
move => Oll.
proc.
islossless.
+ while (true) (h - k);move => *; auto => /> /#.
+ while (true) (Params.len - i).
  + move => *; inline *; wp; while (true) (s - chain_count);move => *; auto => /> /#.
    by auto;smt().
+ while (true) (outlen - consumed);move => *; auto => /> /#.
+ while (true) (Params.len1 - i);move => *; auto => /> /#.
+ while (true) (outlen - consumed);move => *; auto => /> /#.
qed.

lemma verify2_ll (O <: RO.Oracle) : islossless O.o => islossless XMSS_TW_RFC(O).verify.
move => Oll.
proc.
islossless.
while (true) (len - size pkWOTS);move => *; auto => />;smt(size_rcons).
qed.

lemma sign1_ll (O <: RO.Oracle) : islossless O.o => islossless XMSS_TW_RFC(O).sign.
move => Oll.
islossless.
+ while (true) (l - size leafl); last by auto;smt(size_rcons).
  move => z;wp;conseq (: true);1:smt(size_rcons).
  islossless.
  + while (true) (len - size pkWOTS);move => *; auto => />;smt(size_rcons).
  + while (true) (len - size skWOTS);move => *; auto => />;smt(size_rcons).
  + while (true) (len - size sig);move => *; auto => />;smt(size_rcons).
  while (true) (len - size skWOTS);move => *; auto => />;smt(size_rcons).
qed.

lemma sign2_ll (O <: RO.Oracle) : islossless O.o => islossless S(O).sign.
move => Oll.
islossless.
+ while (true) (Params.len - i).
  + move => *; inline *; wp; while (true) (s - chain_count);move => *; auto => /> /#.
    by auto;smt().
+ while (true) (outlen - consumed);move => *; auto => /> /#.
+ while (true) (Params.len1 - i);move => *; auto => /> /#.
+ while (true) (outlen - consumed);move => *; auto => /> /#.
+ while (true) (Params.len - i);move => *; auto => /> /#.
+ while (true) (h-j);last by auto => /> /#.
  move => z;wp;conseq (: true);1:smt().
  islossless.
  + while (true) (2^t - i); last by auto;smt().
    move => zz;wp;conseq (: true);1:smt().
    while (true) (to_uint offset - 2 + 1).
    + move => zzz;auto => /> &hr; rewrite uleE /= => ? _.
      by rewrite to_uintB /=;rewrite ?uleE /#.
    conseq (: true) => /=;1: by move => &hr ?? ofs ?;rewrite uleE /= /#.
    islossless.
    + while (true) (Params.len - i).
    + move => *; inline *; wp; while (true) (s - chain_count);move => *; auto => /> /#.
      by auto;smt().
+ while (true) (Params.len - i);move => *; auto => /> /#.
qed.

lemma security &m  (O <: RO.Oracle  {-O_CMA_Default, -DSS_RFC.DSS.KeyUpdating.O_CMA_Default}) (A <: Adv_EUFCMA_RO {-O_CMA_Default, -DSS_RFC.DSS.KeyUpdating.O_CMA_Default, -O}):
    islossless O.o =>
    (forall (RO <: RO.POracle{-A}) (O0 <: SOracle_CMA{-A}),
      islossless O0.sign => islossless RO.o => islossless A(RO, O0).forge) =>
     (forall  (RO <: RO.POracle{-A}), hoare [ A(RO,O_CMA_Default(S(O))).forge :
         size O_Base_Default.qs = 0 ==> size O_Base_Default.qs <= l]) =>
    Pr [ EUF_CMA_RO(S,A,O_CMA_Default,O).main() @ &m : res ] <=
    Pr[DSS_RFC.KeyUpdatingROM.EUF_CMA_RO(XMSS_TW_RFC, B(A), DSS_RFC.DSS.KeyUpdating.O_CMA_Default, O).main
                   () @ &m : res].
proof.
move => O_ll A_ll Abounded.
byequiv => //.
proc.
seq 1 1 : (={glob A,glob O}); 1: by call(:true);auto.

inline {1} 1; inline {2} 1;inline {2} 3;inline {1} 4.

seq 3 4 : (O_Base_Default.qs{1} = DSS_RFC.DSS.O_Base_Default.qs{2}
       /\ pkrel pk{2} pk{1}
       /\ ={glob O}
       /\ m{1} = f{2}.`1
       /\ f{2}.`2 = sig{1}); last first.
+ sp;case (0 <= to_uint sig0{1}.`sig_idx < l); last first.
  + inline {1} 3;inline {2} 2;wp;conseq (: _ ==> true);1: by auto => />.
    + call {1} (: true ==> true);1: by apply (verify1_ll O).
    + call {2} (: true ==> true);1: by apply (verify2_ll O).
    by auto.
  wp;call(:O_Base_Default.qs{1} = DSS_RFC.DSS.O_Base_Default.qs{2} /\ ={arg} ==>
     O_Base_Default.qs{1} = DSS_RFC.DSS.O_Base_Default.qs{2} /\ ={res});1: by proc; auto => /#.
  wp;call(: pkrel  arg{2}.`1 arg{1}.`1 /\ ={m,glob O} /\ sigrel arg{2}.`3 arg{1}.`3 ==> ={res});
    1: by symmetry;proc*;call(ver_eq O);auto => /#.
  auto =>  /> &1 &2 *;do split.
  + by rewrite Index.insubdK;smt().
  + rewrite DBHL.insubdK /=;1: by rewrite size_rev size_map AuthPath.valP.
    by rewrite revK.

seq 2 2 : (={glob A, glob O}
   /\ O_Base_Default.qs{1} = DSS_RFC.DSS.O_Base_Default.qs{2}
   /\ O_Base_Default.qs{1} = []
   /\ pkrel pk{2} pk{1}
   /\ skrel DSS_RFC.DSS.KeyUpdating.O_CMA_Default.sk{2} O_CMA_Default.sk{1}
   /\ to_uint O_CMA_Default.sk{1}.`idx = 0).
+ inline {1} 2; inline {2} 2;wp => /=.
  inline {1} 1;wp;symmetry;call (kg_eq O).
  auto => />.

sp;symmetry.

conseq (: pk0{1} = pk{1} /\
  ((glob A){2} = (glob A){1} /\ (glob O){2} = (glob O){1}) /\
  O_Base_Default.qs{2} = DSS_RFC.DSS.O_Base_Default.qs{1} /\
  O_Base_Default.qs{2} = [] /\
  pkrel pk{1} pk{2} /\
  skrel DSS_RFC.DSS.KeyUpdating.O_CMA_Default.sk{1} O_CMA_Default.sk{2} /\
  to_uint O_CMA_Default.sk{2}.`idx = 0
  ==>
  !(2^h < size O_Base_Default.qs{2}) =>
  O_Base_Default.qs{2} = DSS_RFC.DSS.O_Base_Default.qs{1} /\
  pkrel pk{1} pk{2} /\ (glob O){2} = (glob O){1} /\ m{2} = f{1}.`1 /\ f{1}.`2 = sig{2})
 _ (: size O_Base_Default.qs =  0 ==> size O_Base_Default.qs <= l).
+ smt().
+ smt().
+ by call (Abounded O);  auto => />.

call(: 2^h < size O_Base_Default.qs,
       ={glob O}
    /\ O_Base_Default.qs{2} = DSS_RFC.DSS.O_Base_Default.qs{1} /\ size O_Base_Default.qs{2} = to_uint O_CMA_Default.sk{2}.`idx
    /\ (to_uint O_CMA_Default.sk{2}.`idx < 2 ^ h => skrel DSS_RFC.DSS.KeyUpdating.O_CMA_Default.sk{1} O_CMA_Default.sk{2} ),true).
+ proc;inline {1} 1.
  case : (to_uint O_CMA_Default.sk{2}.`idx < 2 ^ h); last first.
  + sp;wp => /=; conseq(: _ ==> true).
    + move => &1 &2 />*;split => *;
      have ? : to_uint (O_CMA_Default.sk{2}.`idx + W32.one) = 2^h + 1;
       rewrite ?to_uintD_small /=;smt(size_rcons l_max).
    + call {1} (: true ==> true);1: by apply (sign1_ll O).
    + call {2} (: true ==> true);1: by apply (sign2_ll O).
    by auto.

  exlim O_CMA_Default.sk{2}.`idx => _idx.
  wp; call (sig_eq O (to_uint _idx)).
  auto => /> &1 &2.
  move =>  H0 H1 H2  H3;split;1:smt().
  move =>  H4 H5 H6 H7 H8 H9 s1 s2 H10 H11 H12 H13 H14 H15 H16;do split.
  + have ? : W32.of_int (Index.val s1.`1.`2.`1) = s2.`1.`sig_idx.
    + apply W32.to_uint_eq; rewrite /= of_uintK /= -H11; smt(Index.valP l_max).
    have ? : LenNBytes.insubd (map NBytes.insubd (map (BitsToBytes \o DigestBlock.val) (DBLL.val s1.`1.`2.`2))) = s2.`1.`r_sig.`1.
    + rewrite H12 /= DBLL.insubdK;1: by rewrite size_map LenNBytes.valP.
      rewrite  -!map_comp /(\o) /=.
      have -> /= : (fun (x : nbytes) =>
        NBytes.insubd (BitsToBytes (DigestBlock.val (DigestBlock.insubd (BytesToBits (NBytes.val x)))))) = idfun.
      + apply fun_ext => x; rewrite DigestBlock.insubdK.
        + rewrite /BytesToBits (size_flatten_ctt 8); last by rewrite size_map NBytes.valP.
          by move => xx; rewrite mapP => Hex;elim Hex;smt(@W8).
        by rewrite BytesToBitsK NBytes.valKd /#.
      by rewrite map_id LenNBytes.valKd.
    have ? : AuthPath.insubd (rev (map NBytes.insubd (map (BitsToBytes \o DigestBlock.val) (DBHL.val s1.`1.`2.`3)))) = s2.`1.`r_sig.`2; last by smt().
    rewrite -!map_rev H13 -!map_comp /(\o) /=.
    have -> /= : (fun (x : nbytes) =>
        NBytes.insubd (BitsToBytes (DigestBlock.val (DigestBlock.insubd (BytesToBits (NBytes.val x)))))) = idfun.
    + apply fun_ext => x; rewrite DigestBlock.insubdK.
      + rewrite /BytesToBits (size_flatten_ctt 8); last by rewrite size_map NBytes.valP.
        by move => xx; rewrite mapP => Hex;elim Hex;smt(@W8).
      by rewrite BytesToBitsK NBytes.valKd /#.
    by rewrite map_id AuthPath.valKd.
  + by smt(size_rcons).
  + by smt().

+ move => &2 ?;proc;conseq />.
  by inline 1;wp;call (sign1_ll O); auto.
+ move => *;proc;wp;conseq (: _ ==> true);1:smt(size_rcons).
  by call(sign2_ll O).
+ conseq (: _ ==> ={res,glob O}); first by smt().
  by sim.

+ by move => *;proc*;call(:true);auto.

auto => /> &1 &2 H1????????;do split.
+ move => *; do split;2:smt().
  have ? : pk{2}.`pk_pub_seed = pk{1}.`2 by smt().
  have ? : pk{2}.`pk_root = NBytes.insubd (BitsToBytes (DigestBlock.val pk{1}.`1)); last by smt().
+ rewrite H1 /bs2block DigestBlock.insubdK.
  + rewrite /BytesToBits (size_flatten_ctt 8); last by rewrite size_map NBytes.valP.
    move => x; rewrite mapP => Hex;elim Hex;smt(@W8).
  by rewrite BytesToBitsK NBytes.valKd.

by smt().
qed.
