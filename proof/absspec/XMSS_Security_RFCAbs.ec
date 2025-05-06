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

clone XMSS_TW as XMSS_Security with
  type mseed <- nbytes,
  type mkey <- nbytes,
  type msgXMSSTW <- W8.t list,
  op mkg <-
    (fun (ms : nbytes) (i : FLXMSSTW.SA.index) =>
     prf ms (NBytes.insubd (toByte (W32.of_int (FLXMSSTW.SA.Index.val i)) n))),
  op dmseed <- dmap (dlist W8.dword Params.n) NBytes.insubd,
  op FLXMSSTW.n <- n,
  op FLXMSSTW.log2_w <- ilog 2 w,
  op FLXMSSTW.h <- h,
  op FLXMSSTW.chtype <= 0,
  op FLXMSSTW.pkcotype <= 1,
  op FLXMSSTW.trhtype <= 2,
  type FLXMSSTW.SA.WTW.pseed <- nbytes,
  type FLXMSSTW.SA.WTW.sseed <- nbytes,
  (* TODO: Not sure about this address stuff *)
  type FLXMSSTW.SA.HAX.Adrs.sT <- adrs,
  (* op FLXMSSTW.SA.HAX.Adrs.insub <-,
     op FLXMSSTW.SA.HAX.Adrs.val <- *)
  op FLXMSSTW.SA.WTW.dsseed <- dmap (dlist W8.dword Params.n) NBytes.insubd,
  op FLXMSSTW.SA.WTW.dpseed <- dmap (dlist W8.dword Params.n) NBytes.insubd,
  op FLXMSSTW.SA.WTW.prf_sk <-
    (fun (ss : nbytes) (psad : nbytes * adrs) =>
     DigestBlock.insubd (BytesToBits (NBytes.val (WOTS.prf_keygen ss psad)))),
  op FLXMSSTW.SA.WTW.thfc <-
    (fun (i : int) (ps : nbytes) (ad : adrs) (x : bool list) =>
     if i = 8 * n then
      DigestBlock.insubd (BytesToBits (NBytes.val (WOTS.f ps ad (NBytes.insubd (BitsToBytes x)))))
     else if i = 8 * n * 2 then
      let xl = take (8 * n) x in
      let xr = drop (8 * n) x in
      DigestBlock.insubd (BytesToBits
                          (NBytes.val
                           (rand_hash ps ad (NBytes.insubd (BitsToBytes xl)) (NBytes.insubd (BitsToBytes xl)))))
     else if i = 8 * n * len then
      let wpk = LenNBytes.insubd (map NBytes.insubd (chunk n (BitsToBytes x))) in
      DigestBlock.insubd (BytesToBits (NBytes.val (ltree ps ad wpk)))
     else witness)
(*
proof *.

FLXMSSTW.ge1_n, FLXMSSTW.val_log2w, FLXMSSTW.ge1_h, FLXMSSTW.dist_adrstypes,
FLXMSSTW.SA.WTW.ch0, FLXMSSTW.SA.WTW.chS, FLXMSSTW.SA.WTW.two_encodings
FLXMSSTW.SA.dmsgFLXMSSTW_ll, FLXMSSTW.SA.dmsgFLXMSSTW_uni, FLXMSSTW.SA.dmsgFLXMSSTW_fu,
FLXMSSTW.SA.WTW.dsseed_ll, FLXMSSTW.SA.WTW.dsseed_ll, MKey.enum_spec,
MsgXMSSTW.enum_spec, dmkey_ll, dmkey_uni, dmkey_fu.
*)
(* TODO: Instantiate encoding operator *)
(* TODO: Instantiate chain operator *)
(* TODO: Instantiate enums for MKey and MsgXMSSTW *)
(* TODO: In security proof, move proof parameters to section so we don't have to prove things about them *)
