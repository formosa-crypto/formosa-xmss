require import AllCore IntDiv List StdOrder RealExp Distr DList.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.
require import Array8.

require (****) XMSS_TW.
require import XMSS_RFC_Abs.
import XMSS_RFC_Params Address BaseW.

import IntOrder.

op BitsToBytes (bits : bool list) : W8.t list = map W8.bits2w (chunk W8.size bits).
op BytesToBits (bytes : W8.t list) : bool list = flatten (map W8.w2bits bytes).
op W64toBytes_ext (x : W64.t) (l : int) : W8.t list =
  rev (mkseq (fun i => nth W8.zero (to_list (W8u8.unpack8 x)) i) l).

op idxs2adrs (il : int list) : adrs =
  init (fun (i : int) =>
        if 3 <= i <= 6
        then W32.of_int (nth witness il (6 - i))
        else W32.zero).

clone XMSS_TW as XMSS_Security with
  type mseed <- nbytes,
  type mkey <- nbytes,
  type msgXMSSTW <- W8.t list,
  op mkg <-
    (fun (ms : nbytes) (i : FLXMSSTW.SA.index) =>
     prf ms (NBytes.insubd (toByte (W32.of_int (FLXMSSTW.SA.Index.val i)) n))),
  op dmseed <- dmap (dlist W8.dword Params.n) NBytes.insubd,
  (* TODO: op MKey.enum <- map NBytes.insubd <all W8.t lists of length n>
  op dmkey <- duniform MKey.enum, *)
  op FLXMSSTW.n <- n,
  op FLXMSSTW.log2_w <- ilog 2 w,
  op FLXMSSTW.h <- h,
  op FLXMSSTW.chtype <= 0,
  op FLXMSSTW.pkcotype <= 1,
  op FLXMSSTW.trhtype <= 2,
  op FLXMSSTW.SA.dmsgFLXMSSTW <- duniform FLXMSSTW.SA.WTW.DigestBlockFT.enum,
  type FLXMSSTW.SA.WTW.pseed <- nbytes,
  type FLXMSSTW.SA.WTW.sseed <- nbytes,
  op FLXMSSTW.SA.WTW.dsseed <- dmap (dlist W8.dword Params.n) NBytes.insubd,
  op FLXMSSTW.SA.WTW.dpseed <- dmap (dlist W8.dword Params.n) NBytes.insubd,
  op FLXMSSTW.SA.WTW.prf_sk <-
    (fun (ss : nbytes) (psad : nbytes * FLXMSSTW.SA.adrs) =>
     DigestBlock.insubd (BytesToBits
                         (NBytes.val
                          (WOTS.prf_keygen ss (psad.`1, (idxs2adrs (FLXMSSTW.SA.HAX.Adrs.val psad.`2))))))),
  op FLXMSSTW.SA.WTW.thfc <-
    (fun (i : int) (ps : nbytes) (ad : FLXMSSTW.SA.adrs) (x : bool list) =>
     let nb2db = (fun (x : nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val x))) in
     let mad = (idxs2adrs (FLXMSSTW.SA.HAX.Adrs.val ad)) in
     if i = 8 * n then
      nb2db (WOTS.f ps mad (NBytes.insubd (BitsToBytes x)))
     else if i = 8 * n * 2 then
      let xl = take (8 * n) x in
      let xr = drop (8 * n) x in
      nb2db (rand_hash ps mad (NBytes.insubd (BitsToBytes xl)) (NBytes.insubd (BitsToBytes xl)))
     else if i = 8 * n * len then
      let wpk = LenNBytes.insubd (map NBytes.insubd (chunk n (BitsToBytes x))) in
      nb2db (ltree ps mad wpk)
     else witness)
proof *.
realize FLXMSSTW.ge1_n by exact: ge1_n.
realize FLXMSSTW.val_log2w by case: w_vals => ->; smt(ilog_powK).
realize FLXMSSTW.ge1_h by smt(h_g0).
realize FLXMSSTW.dist_adrstypes by trivial.
realize FLXMSSTW.SA.WTW.ch0. admitted. (* TODO: instantiate chain *)
realize FLXMSSTW.SA.WTW.chS. admitted. (* TODO: instantiate chain *)
realize FLXMSSTW.SA.WTW.two_encodings. admitted. (* TODO: instantiate encoding *)
realize FLXMSSTW.SA.dmsgFLXMSSTW_ll.
rewrite duniform_ll -size_eq0 2!size_map size_range.
suff /#: 0 < 2 ^ (8 * n).
by rewrite expr_gt0.
qed.
realize FLXMSSTW.SA.dmsgFLXMSSTW_uni by exact: duniform_uni.
realize FLXMSSTW.SA.dmsgFLXMSSTW_fu by apply /duniform_fu /WTW.DigestBlockFT.enumP.
realize FLXMSSTW.SA.WTW.dsseed_ll by apply /dmap_ll /dlist_ll /W8.dword_ll.
realize FLXMSSTW.SA.WTW.dpseed_ll by apply /dmap_ll /dlist_ll /W8.dword_ll.
realize FLXMSSTW.SA.WTW.ddgstblock_ll. admitted. (* TODO: Proof artifact, not needed (might instantiate just because?) *)
realize MKey.enum_spec. admitted. (* TODO: instantiate enum and prove, but shouldn't be necessary *)
realize MsgXMSSTW.enum_spec. admitted. (* TODO: this shouldn't be necessary *)
realize rng_qS. admitted. (* TODO: Proof artifact, move to section *)
realize ge0_qH. admitted. (* TODO: Proof artifact, move to section *)
realize dmseed_ll by apply /dmap_ll /dlist_ll /W8.dword_ll.
realize dmkey_ll. admitted. (* TODO: instantiate and can do *)
realize dmkey_uni. admitted. (* TODO: instantiate and can do *)
realize dmkey_fu. admitted. (* TODO: instantiate and can do *)
