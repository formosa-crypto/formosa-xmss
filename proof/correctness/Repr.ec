pragma Goals : printall.

require import AllCore List IntDiv.

from Jasmin require import JModel.

(*****) import StdBigop.Bigint.

require import Params Parameters Types BaseW Hash WOTS XMSS_MT_Params LTree XMSS_MT_Types.

require import Array32 Array64 Array68 Array131 Array2144.

require import BitEncoding.
(*---*) import BitChunking.

require import Utils Bytes.


require import Bytes.

(* Encode : impl -> spec *)
(* Decode : spec -> impl *)

(** -------------------------------------------------------------------------------------------- **)

op load_buf (mem : global_mem_t) (ptr : W64.t) (len : int) : W8.t list =
  mkseq (fun i => loadW8 mem (to_uint ptr + i)) len.

lemma size_load_buf (mem : global_mem_t) (ptr : W64.t) (len : int) :
    0 <= len =>
    size (load_buf mem ptr len) = len.
proof.
move => ?; rewrite /load_buf size_mkseq /#.
qed.

lemma nth_load_buf (mem : global_mem_t) (ptr : W64.t) (len i : int) :
    0 <= i < len =>
    nth witness (load_buf mem ptr len) i = mem.[to_uint ptr + i].
proof.
move => ?.
by rewrite nth_mkseq //=.
qed.

(** -------------------------------------------------------------------------------------------- **)

op sub_list ['a] (x : 'a list) (k len : int) : 'a list = 
  mkseq (fun (i : int) => nth witness x (k + i)) len.

lemma size_sub_list (x : 'a list) (k len : int) :
    0 <= len =>
      size (sub_list x k len) = len.
proof.
move => ?.
rewrite /sub_list size_mkseq /#.
qed.

lemma nth_sub_list ['a] (x : 'a list) (k len : int) (i : int) :
    0 <= i < len =>
    nth witness (sub_list x k len) i = nth witness x (k + i).
proof.
move => ?.
rewrite /sub_list nth_mkseq //=.
qed.

(** -------------------------------------------------------------------------------------------- **)

lemma size_toByte_32 (x : W32.t) (i : int) : 
    0 <= i => 
    size (toByte x i) = i.
proof.
move => ?.
rewrite /toByte size_rev size_mkseq /#.
qed.

lemma size_toByte_64 (x : W64.t) (i : int) : 
    0 <= i => 
    size (toByte_64 x i) = i.
proof.
move => ?.
rewrite /toByte_64.
rewrite size_rev size_mkseq /#.
qed.

(* TMP: MOVE THIS TO THE RIGHT PLACE LATER *)
op BitsToBytes (bits : bool list) : W8.t list = map W8.bits2w (chunk W8.size bits).

import W4u8.

import W4u8.Pack.
import W8u8.Pack.

(** -------------------------------------------------------------------------------------------- **)

op nbytes_flatten (x : nbytes list) : W8.t list =
  flatten (map (NBytes.val) x).

lemma nth_nbytes_flatten (x : nbytes list, i : int):
    0 <= i %/ n < size x =>
    nth witness (nbytes_flatten x) i = nth witness (NBytes.val (nth witness x (i %/ n))) (i %% n).
move => H.
rewrite /nbytes_flatten (nth_flatten witness n).
    - pose P := (fun (s0 : W8.t list) => size s0 = n).
      pose L := (map NBytes.val x).
      rewrite -(all_nthP P L witness) /P /L size_map => j?. 
      by rewrite (nth_map witness) // NBytes.valP.
by rewrite (nth_map witness).
qed.

(** -------------------------------------------------------------------------------------------- **)

op DecodeWotsSk (sk : wots_sk) : W8.t Array2144.t = 
  Array2144.of_list witness (nbytes_flatten (LenNBytes.val sk)).

op DecodeWotsPk (pk : wots_pk) : W8.t Array2144.t = 
  Array2144.of_list witness (nbytes_flatten (LenNBytes.val pk)).

op EncodeWotsPk (pk : W8.t Array2144.t) : wots_pk = 
  LenNBytes.insubd (map NBytes.insubd (chunk n (to_list pk))).

op EncodeWotsSignature (s : W8.t Array2144.t) : wots_signature = 
  LenNBytes.insubd (map NBytes.insubd (chunk 32 (to_list s))). 

op EncodeWotsSignatureList (s : W8.t list) : wots_signature = 
  LenNBytes.insubd (map NBytes.insubd (chunk 32 s)). 

lemma encodewotssig_list_array (s : W8.t Array2144.t) :
    EncodeWotsSignature s = EncodeWotsSignatureList (to_list s).
proof.
rewrite /EncodeWotsSignature /EncodeWotsSignatureList.
by congr.
qed.

op DecodeWotsSignature_List (s : wots_signature) : W8.t list = nbytes_flatten (LenNBytes.val s).

lemma size_DecodeWotsSignature_List (x : wots_signature) :
    size (DecodeWotsSignature_List x) = n * len.
proof.
by rewrite /DecodeWotsSignature_List size_nbytes_flatten LenNBytes.valP.
qed.


(** -------------------------------------------------------------------------------------------- **)

op DecodePkNoOID (x : xmss_pk) : W8.t Array64.t = 
  Array64.of_list witness (NBytes.val x.`pk_root ++ NBytes.val x.`pk_pub_seed).

op EncodePkNoOID (x : W8.t Array64.t) : xmss_pk = {| pk_oid      = witness;
                                                     pk_root     = NBytes.insubd (sub x 0 32); 
                                                     pk_pub_seed = NBytes.insubd (sub x 32 32);
                                                   |}. 

import W4u8.
import W8u8.

op EncodeIdx (idx : W32.t) : W8.t list = W32toBytes_ext idx XMSS_INDEX_BYTES.

op DecodeIdx (idx_bytes : W8.t list) : W32.t = 
  W32.bits2w (flatten (map W8.w2bits (rev idx_bytes))).

(* 
  The bits of the most significant byte of w are guaranteed to be zero because w 
  represents a value less than  2^20 
*)
import StdOrder.IntOrder.

lemma EncodeIdxK (idx : W32.t) :
    0 <= to_uint idx < 2^XMSS_FULL_HEIGHT =>
    DecodeIdx (EncodeIdx idx) = idx.
proof.
rewrite /XMSS_FULL_HEIGHT /= => ?. (* We only need for bytes, the 4th is all zeros *)
rewrite /DecodeIdx /EncodeIdx.
rewrite bits2wE wordP => i?. 
rewrite initiE //= /XMSS_INDEX_BYTES.
rewrite (nth_flatten false 8).
       + pose X := (fun (s : bool list) => size s = 8).
         pose Y := (map W8.w2bits (rev (W32toBytes_ext idx 3))).
         rewrite -(all_nthP X Y witness) /X /Y size_map size_rev size_W32toBytes_ext // => k?. 
         rewrite (nth_map witness); first by rewrite size_rev size_W32toBytes_ext.
         by rewrite size_w2bits.

case (0 <= i %/ 8 && i %/ 8 < 3) => [Ha | Hb].
  + rewrite (nth_map witness); first by rewrite size_rev size_W32toBytes_ext //.
    rewrite nth_rev; first by rewrite size_W32toBytes_ext /#.
    rewrite size_W32toBytes_ext //=.
    rewrite nth_W32toBytes_ext // 1:/#.
    rewrite unpack8E initiE 1:/# /= bits8E /= initiE 1:/# /=.
    congr => /#.

have ->: nth [] (map W8.w2bits (rev (W32toBytes_ext idx 3))) (i %/ 8) = [].
  + rewrite nth_out 2:/# size_map size_rev size_W32toBytes_ext // /#.

rewrite nth_out 1:/#.
have E: 24 <= i < 32 by smt().
rewrite get_to_uint (: (0 <= i && i < 32)) 1:/# /=.
case (i = 24) => [-> // /#  | ?].
case (i = 25) => [-> // /#  | ?].
case (i = 26) => [-> // /#  | ?].
case (i = 27) => [-> // /#  | ?].
case (i = 28) => [-> // /#  | ?].
case (i = 29) => [-> // /#  | ?].
case (i = 30) => [-> // /#  | ?].
case (i = 31) => [-> // /#  | /#].
qed.

lemma EncodeIdxK2 (idx : W32.t) :
    0 <= to_uint idx < 2^XMSS_FULL_HEIGHT - 1 =>
    DecodeIdx (EncodeIdx idx) = idx.
proof.
rewrite /XMSS_FULL_HEIGHT /= => ?. (* We only need for bytes, the 4th is all zeros *)
rewrite /DecodeIdx /EncodeIdx.
rewrite bits2wE wordP => i?. 
rewrite initiE //= /XMSS_INDEX_BYTES.
rewrite (nth_flatten false 8).
       + pose X := (fun (s : bool list) => size s = 8).
         pose Y := (map W8.w2bits (rev (W32toBytes_ext idx 3))).
         rewrite -(all_nthP X Y witness) /X /Y size_map size_rev size_W32toBytes_ext // => k?. 
         rewrite (nth_map witness); first by rewrite size_rev size_W32toBytes_ext.
         by rewrite size_w2bits.

case (0 <= i %/ 8 && i %/ 8 < 3) => [Ha | Hb].
  + rewrite (nth_map witness); first by rewrite size_rev size_W32toBytes_ext //.
    rewrite nth_rev; first by rewrite size_W32toBytes_ext /#.
    rewrite size_W32toBytes_ext //=.
    rewrite nth_W32toBytes_ext // 1:/#.
    rewrite unpack8E initiE 1:/# /= bits8E /= initiE 1:/# /=.
    congr => /#.

have ->: nth [] (map W8.w2bits (rev (W32toBytes_ext idx 3))) (i %/ 8) = [].
  + rewrite nth_out 2:/# size_map size_rev size_W32toBytes_ext // /#.

rewrite nth_out 1:/#.
have E: 24 <= i < 32 by smt().
rewrite get_to_uint (: (0 <= i && i < 32)) 1:/# /=.
case (i = 24) => [-> // /#  | ?].
case (i = 25) => [-> // /#  | ?].
case (i = 26) => [-> // /#  | ?].
case (i = 27) => [-> // /#  | ?].
case (i = 28) => [-> // /#  | ?].
case (i = 29) => [-> // /#  | ?].
case (i = 30) => [-> // /#  | ?].
case (i = 31) => [-> // /#  | /#].
qed.

lemma size_EncodeIdx (x : W32.t) : size (EncodeIdx x) = XMSS_INDEX_BYTES.
proof.
by rewrite /XMSS_INDEX_BYTES /EncodeIdx size_W32toBytes_ext /#.
qed.


op DecodeSkNoOID (x : xmss_sk) : W8.t Array131.t = 
  Array131.of_list witness (
          EncodeIdx x.`idx ++ 
          NBytes.val x.`sk_seed ++ 
          NBytes.val x.`sk_prf ++ 
          NBytes.val x.`sk_root ++ 
          NBytes.val  x.`pub_seed_sk
  ).

(** -------------------------------------------------------------------------------------------- **)

lemma enc_dec_wots_pk (pk : wots_pk) :
    n = XMSS_N /\ len = XMSS_WOTS_LEN =>
    pk = EncodeWotsPk (DecodeWotsPk pk).
proof.
rewrite /XMSS_N /XMSS_WOTS_LEN => [#] n_val len_val.
rewrite /EncodeWotsPk /DecodeWotsPk.
apply len_n_bytes_eq.
apply (eq_from_nth witness); first by rewrite !LenNBytes.valP.
rewrite LenNBytes.valP => j?.
rewrite LenNBytes.insubdK.
  + by rewrite /P size_map size_chunk 1:/# size_to_list n_val len_val.
rewrite (nth_map witness).
  + rewrite size_chunk 1:/# size_to_list n_val /#.
rewrite /chunk nth_mkseq.
  + rewrite size_to_list n_val /#.
apply nbytes_eq.
rewrite NBytes.insubdK.
  + rewrite /P size_take 1:/# size_drop 1:/# size_to_list /#.
simplify.
apply (eq_from_nth witness); first by rewrite size_take 1:/# size_drop 1:/# size_to_list NBytes.valP /#.
rewrite NBytes.valP n_val => i?.
rewrite nth_take // 1:/# nth_drop 1,2:/# get_to_list get_of_list 1:/#.
rewrite /nbytes_flatten (nth_flatten witness n).
  + pose P := (fun (s : W8.t list) => size s = n).
    pose L := (map NBytes.val (LenNBytes.val pk)).
    rewrite -(all_nthP P L witness) /P /L size_map LenNBytes.valP n_val => l Hl. 
    rewrite (nth_map witness).
       - by rewrite LenNBytes.valP.
    by rewrite NBytes.valP.
by rewrite (nth_map witness) 2:/# LenNBytes.valP /#.
qed.

(** -------------------------------------------------------------------------------------------- **)

op EncodeAuthPath (x : W8.t list) : auth_path = 
  AuthPath.insubd (map NBytes.insubd (chunk n x)).

op DecodeAuthPath_List (ap : auth_path) : W8.t list = nbytes_flatten (AuthPath.val ap).

lemma size_DecodeAuthPath_List (x : auth_path) :
    size (DecodeAuthPath_List x) = n * (h %/ d).
proof.
by rewrite /DecodeAuthPath_List size_nbytes_flatten AuthPath.valP.
qed.

op wots_sig_bytes : int = len * n.
op auth_path_bytes : int = (h %/ d) * n.
op reduced_sig_bytes : int = wots_sig_bytes + auth_path_bytes.

op EncodeReducedSignature (x : W8.t list) :  wots_signature * auth_path =
  (
      EncodeWotsSignatureList (sub_list x 0 wots_sig_bytes), 
      EncodeAuthPath (sub_list x wots_sig_bytes auth_path_bytes)
  ).

op EncodeSignature (sig_bytes : W8.t list) : sig_t =
  {| sig_idx  = DecodeIdx (sub_list sig_bytes 0 XMSS_INDEX_BYTES);
     r        = NBytes.insubd (sub_list sig_bytes XMSS_INDEX_BYTES XMSS_N);
     r_sigs   = map EncodeReducedSignature 
                    (
                        chunk reduced_sig_bytes 
                          (
                              sub_list sig_bytes 
                              (XMSS_INDEX_BYTES + XMSS_N)
                              (size sig_bytes - (XMSS_INDEX_BYTES + XMSS_N))
                          )
                    );
  |}.

lemma sig_eq (s1 s2 : sig_t) :
    s1.`sig_idx = s2.`sig_idx /\
    s1.`r       = s2.`r       /\
    s1.`r_sigs  = s2.`r_sigs => 
    s1 = s2 by smt(). 

import W4u8.

lemma nth_toByte dflt (x : W32.t) (n i : int) :
    0 < n => 
    0 <= i < n => 
    nth dflt (toByte x n) i = (unpack8 x).[n - (i + 1)].
proof.
move => ??.
rewrite /toByte nth_rev; first by rewrite size_mkseq /#.
by rewrite size_mkseq (: max 0 n = n) 1:/# nth_mkseq 1:/# /=.
qed.

lemma toByte_32_64 (x : W32.t) (n : int) :
    0 < n =>
    toByte x n = W64toBytes_ext (zeroextu64 x) n.
proof.
move => ?.
apply (eq_from_nth witness); rewrite size_toByte_32 1:/# ?size_W64toBytes_ext // => i?.
rewrite nth_W64toBytes_ext //.
rewrite nth_toByte //.
rewrite !unpack8E. 
case (0 <= n - (i + 1) < 4) => ?.
  + rewrite !initiE 1,2:/# /= !bits8E wordP => j?.  
    rewrite !initiE //=.
    rewrite zeroextu64E pack2E initiE 1:/# /= initiE 1:/# /= ifT 1:/#.
    congr; smt().
rewrite initE ifF 1:/#.
case (0 <= n - (i + 1) < 8) => ?.
  + rewrite initiE 1:/# /= zeroextu64E pack2E bits8E wordP => j?.
    by rewrite initiE //= initiE 1:/# /= initiE 1:/# /= ifF 1:/# /=.
by rewrite initE ifF 1:/#.
qed.

require import BitEncoding.

import BS2Int.

lemma DecodeIdxK (bytes : W8.t list) : 
    size bytes = XMSS_INDEX_BYTES =>
    0 <= to_uint (DecodeIdx bytes) < 2^XMSS_FULL_HEIGHT =>
    EncodeIdx (DecodeIdx bytes) = bytes.
proof.
rewrite /XMSS_INDEX_BYTES => H0 H1.
rewrite /EncodeIdx /W32toBytes_ext /DecodeIdx.
apply (eq_from_nth witness); rewrite size_rev ?size_mkseq (: max 0 XMSS_INDEX_BYTES = 3) 1:/# //= => [/# | i?].
rewrite nth_rev; first by rewrite size_mkseq /#.
rewrite size_mkseq /XMSS_INDEX_BYTES /= (: max 0 3 = 3) 1:/# /=.
rewrite nth_mkseq 1:/# /= get_unpack8 1:/# bits8E wordP => w?. 
rewrite initiE //= bits2wE //= initiE 1:/# (nth_flatten false 8).
- pose X := (fun (s : bool list) => size s = 8).
  pose Y := (map W8.w2bits (rev bytes)).
  rewrite -(all_nthP X Y witness) /X /Y size_map => k?. 
  by rewrite (nth_map witness).
rewrite (nth_map witness); first by rewrite size_rev H0 /#.
rewrite w2bitsE nth_mkseq 1:/# /= nth_rev 1:/#.
rewrite H0 /#.
qed.
