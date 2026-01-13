pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList.

from Jasmin require import JModel.

require import Params Address BaseW Hash WOTS LTree XMSS_MT_TreeHash XMSS_MT_Types XMSS_MT_Params XMSS_MT_PRF.
require import XMSS_IMPL Parameters.
require import Utils Repr Bytes.

require import Correctness_Mem.
require import Correctness_Address.
require import Correctness_Hash.
require import Correctness_Bytes.
require import Correctness_WOTS.
require import LTReeProof.
require import RootFromSigProof.

(*---*) import W8u8.Pack.
(*---*) import BitEncoding.BitChunking.

require import Array8 Array32 Array64 Array2144.
require import WArray64.

lemma toByte_W32_eq_toByte_64_W64 (x : W32.t) (y : W64.t) (n : int) :
    to_uint x = to_uint y =>
        0 < n <= 32 =>
           toByte x n = toByte_64 y n.
proof.
move=> Heq Hn.
apply (eq_from_nth witness).
+ rewrite size_toByte_32 1:/# size_toByte_64 /#.
rewrite size_toByte_32 1:/# => i Hi.
rewrite toByte_32_64 1:/#. 
rewrite -W64toBytes_ext_toByte_64.
rewrite /W64toBytes_ext.
rewrite !nth_rev ?size_mkseq 1,2:/#.
rewrite !nth_mkseq 1,2:/# /=.
case: ( 0 <= max 0 n - (i + 1) < 8) => [Ha | Hb].
+ rewrite /unpack8 !initiE 1,2:/# /=.
  rewrite !bits8E wordP => k? /=.
  rewrite !initiE //=.
  rewrite !get_to_uint. 
  have ->: 0 <= (max 0 n - (i + 1)) * 8 + k < 64 = true by smt().
  simplify.
  rewrite to_uint_zeroextu64.
  smt().
+ rewrite !get_out /#.
qed.


lemma verify_correctness (ptr_m           (* Apontador p mensagem *) 
                          ptr_mlen        (* Apontador p tamanho mensagem *) 
                          ptr_sm          (* Apontador p signed message *) 
                          sm_len : W64.t) (* Apontador p tamanho da signed message *) 
                         (_pk : W8.t Array64.t) :
    n = XMSS_N /\
    d = XMSS_D /\
    h = XMSS_FULL_HEIGHT /\ 
    floor (log2 w%r) = XMSS_WOTS_LOG_W /\
    w = XMSS_WOTS_W /\
    len1 = XMSS_WOTS_LEN1 /\
    len2 = XMSS_WOTS_LEN2 /\
    len = XMSS_WOTS_LEN /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    F_padding_val = XMSS_HASH_PADDING_F /\
    padding_len = XMSS_PADDING_LEN /\ 
    H_msg_padding_val = XMSS_HASH_PADDING_HASH =>
    equiv [
      M(Syscall).__xmssmt_core_sign_open ~ XMSS_MT_PRF.verify :

      valid_idx ((EncodeSignature (load_sig_mem Glob.mem{1} ptr_sm)).`sig_idx) /\

      XMSS_SIG_BYTES < to_uint sm_len /\
      0 <= to_uint sm_len  < W64.max_uint /\

      (* pointers are valid *)
      0 <= to_uint ptr_m < W64.max_uint /\
      0 <= to_uint ptr_m + to_uint sm_len  < W64.max_uint /\

      0 <= to_uint ptr_sm + to_uint sm_len < W64.max_uint /\ 
      0 <= to_uint ptr_sm < W64.max_uint /\

      0 <= to_uint ptr_mlen + 8 < W64.max_uint /\
      0 <= to_uint ptr_mlen < W64.max_uint /\

      disjoint_ptr   (to_uint ptr_m) (to_uint sm_len)
                     (to_uint ptr_mlen) 8 /\ (* 1 W64 = 8 bytes *)

      disjoint_ptr (to_uint ptr_sm) (to_uint sm_len)
                   (to_uint ptr_m) (to_uint sm_len) /\ 

      disjoint_ptr   (to_uint ptr_sm) (to_uint sm_len)
                     (to_uint ptr_mlen) 8 /\ (* 1 W64 = 8 bytes *)
   
      arg{1} = (ptr_m, ptr_mlen, ptr_sm, sm_len, _pk) /\ 
      arg{2}.`1 = EncodePkNoOID _pk /\  (* pk *)
      Types.Msg_t.val arg{2}.`2 = load_buf Glob.mem{1} (ptr_sm + (of_int XMSS_SIG_BYTES)%W64) 
                                  (to_uint (sm_len  - (of_int XMSS_SIG_BYTES)%W64)) /\ (* message *)
      arg{2}.`3 = EncodeSignature (load_sig_mem Glob.mem{1} ptr_sm) (* signature *)  /\

      0 <= to_uint ptr_m + to_uint sm_len < W64.max_uint
      ==>
      (res{2} <=> res{1} = W64.zero) 
    ].
proof.
rewrite /XMSS_N /XMSS_D /XMSS_FULL_HEIGHT => [#] n_val d_val h_val *.
proc => /=.
   
seq 9 0 : #pre; first by auto.

swap {1} 8.
swap {2} 3 -2.
swap {2} 8 -7.
swap {1} 26 -25.
 
seq 2 2 : ( 
  #pre /\ 
  to_list pub_root{1} = NBytes.val (pk{2}.`Types.pk_root) /\ 
  to_list pub_seed{1} = NBytes.val seed{2} /\
  to_list pub_seed{1} = sub pk{1} n n /\
  root{2} = pk{2}.`Types.pk_root /\
  to_list pub_root{1} = NBytes.val root{2}
).
    + auto => /> *; do split.
       * apply (eq_from_nth witness); rewrite size_to_list ?NBytes.valP ?n_val // ?size_sub // => j?.
         rewrite /EncodePkNoOID /= NBytes.insubdK ?size_sub 1,2:/# nth_sub 1:/# initiE /#.
       * apply (eq_from_nth witness); rewrite size_to_list ?NBytes.valP ?n_val // ?size_sub // => j?.
         rewrite /EncodePkNoOID /= NBytes.insubdK ?size_sub 1,2:/# nth_sub 1:/# initiE /#.
       * apply (eq_from_nth witness); rewrite size_to_list ?NBytes.valP ?n_val // ?size_sub // => j?.
         rewrite nth_sub 1:/# get_to_list initiE 1:/# /#.
       * apply (eq_from_nth witness); rewrite size_to_list ?NBytes.valP ?n_val // ?size_sub // => j?.
         rewrite get_to_list initiE 1:/# /EncodePkNoOID /=.
         rewrite NBytes.insubdK ?size_sub ?nth_sub /#.

swap {1} 4 -2.

seq 2 0 : (
    #pre /\ 
    ots_addr{1} = zero_address
).
    + inline {1} 2; inline {1} 1; wp.
      ecall {1} (zero_addr_res addr{1}); auto => /> &1 &2 *.
      by apply zero_addr_setZero.

swap {2} 3 -2.
 
seq 0 1 : (
    #pre /\ 
    address{2} = zero_address
); first by auto.
    
swap {1} 3 -1.

seq 2 0 : (
  #pre /\ 
  ltree_addr{1}.[3] = W32.one /\
  (forall (k : int), 0 <= k < 8 => (k <> 3) => ltree_addr{1}.[k] = W32.zero)
).
    + inline {1} 2; inline {1} 1; wp.
      ecall {1} (zero_addr_res addr{1}); auto => /> *.
      by rewrite get_setE //= ifF // zero_addr_i.

seq 5 0 : (
  #pre /\ 
  node_addr{1}.[3] = (of_int 2)%W32 /\
  (forall (k : int), 0 <= k < 8 => (k <> 3) => node_addr{1}.[k] = W32.zero) /\
  t64{1} = smlen{1} - W64.of_int 4963 /\
  sm_offset{1} = W64.zero
).
    + inline {1} 2; inline {1} 1; wp.
      ecall {1} (zero_addr_res addr{1}); auto => /> *. 
      by rewrite get_setE //= ifF // zero_addr_i.
 
(* ------------------------------------------------------------------------------- *)
(*                                                                                 *)
(* ------------------------------------------------------------------------------- *)
 
seq 15 13 : (
  to_list root{1} = NBytes.val node{2} /\
  to_list pub_root{1} = NBytes.val root{2} /\
  0 <= to_uint mlen_ptr{1} < W64.max_uint /\
  0 <= to_uint (loadW64 Glob.mem{1} (to_uint mlen_ptr{1})) < W64.max_uint
); last first.
 
case (node{2} = root{2}).

(* ==== valid signature ========================================================= *)

    + conseq (: 
         to_list root{1} = NBytes.val node{2} /\ 
         to_list pub_root{1} = NBytes.val root{2} /\
         node{2} = root{2} /\ 
         root{1} = pub_root{1} /\
         0 <= to_uint mlen_ptr{1} < W64.max_uint /\
         0 <= to_uint (loadW64 Glob.mem{1} (to_uint mlen_ptr{1})) < W64.max_uint
         ==> 
         _ 
      ); first by auto => /> &1 &2 H0 H1 *; rewrite tP => j?; rewrite -!get_to_list H0 H1.
 
    + seq 1 1 : (#pre /\ are_equal{1} = W8.zero /\ is_valid{2}).
        - ecall {1} (p_memcmp_true root{1} pub_root{1}); auto.

    inline; rcondf {1} 6; first by auto; wp; sp.
    conseq (: _ ==> is_valid{2} /\ res_0{1} = W64.zero); first by auto.
 
    seq 28 0 : (
          #pre /\ 
          res_00{1} = W64.zero /\
          0 <= to_uint bytes3{1} < W64.max_uint
    ); first by auto.

    wp.
    while {1} (
      is_valid{2} /\ 
      res_00{1} = W64.zero /\ 
      0 <= to_uint i1{1} <= to_uint bytes3{1} /\
      0 <= to_uint bytes3{1} < W64.max_uint
    ) (to_uint bytes3{1} - to_uint i1{1}); auto => /> &hr *; [by rewrite !to_uintD /# | by rewrite ultE /#]. 

(* ==== invalid signature ======================================================= *)

    + conseq (: 
         to_list root{1} = NBytes.val node{2} /\ 
         to_list pub_root{1} = NBytes.val root{2} /\
         node{2} <> root{2} /\ 
         root{1} <> pub_root{1} /\
         0 <= to_uint mlen_ptr{1} < W64.max_uint /\
         0 <= to_uint (loadW64 Glob.mem{1} (to_uint mlen_ptr{1})) < W64.max_uint
         ==> 
         _ 
      ); first by auto => /> &1 &2 H0 H1 *; apply array_neq; rewrite H0 H1; smt(NBytes.val_inj).

    + seq 1 1 : (#pre /\ are_equal{1} <> W8.zero /\ is_valid{2} = false).
        - ecall {1} (p_memcmp_false root{1} pub_root{1}); auto => />.

    inline; rcondt {1} 6; first by auto.
    wp.
    conseq (: _ ==> is_valid{2} = false /\ res_00{1} <> W64.zero); first by auto.
    seq 10 0 : (
        is_valid{2} = false /\
        res_00{1} <> W64.zero /\
        0 <= to_uint inlen{1} < W64.max_uint
    ); first by auto => /> *; smt(@W64 pow2_64).

    while {1} (
      is_valid{2} = false /\ 
      res_00{1} <> W64.zero /\ 
      0 <= to_uint i0{1} <= to_uint inlen{1} /\
      0 <= to_uint inlen{1} < W64.max_uint
    ) (to_uint inlen{1} - to_uint i0{1}); auto => /> &hr *; [by rewrite !to_uintD /# | by rewrite ultE /#]. 

(* ------------------------------------------------------------------------------ *)
(*                                                                                 *)
(* ------------------------------------------------------------------------------- *)

seq 1 0 : (
        #{/~t64{1} = smlen{1} - (of_int 4963)%W64}pre /\
        loadW64 Glob.mem{1} (to_uint mlen_ptr{1}) = smlen{1} - (of_int 4963)%W64
).
- auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 ?H17 H18 H19 HM H20 H21 H22 H23 H24 H25*.
  rewrite load_store_W64 /XMSS_FULL_HEIGHT /=.
  rewrite /XMSS_FULL_HEIGHT /= in H1.
  have E :  disjoint_ptr (to_uint ptr_sm) (XMSS_SIG_BYTES) 
                         (to_uint ptr_mlen) 8 by smt().
  have ->: load_sig_mem (storeW64 Glob.mem{1} (to_uint ptr_mlen) (sm_len - (of_int 4963)%W64)) ptr_sm = load_sig_mem Glob.mem{1} ptr_sm.
    + apply (eq_from_nth witness); rewrite !size_load_buf // /XMSS_SIG_BYTES => i?.
      rewrite !nth_load_buf // storeW64E /stores => />.
      rewrite !bits8E !get_setE !ifF 1..7:/# //. 
      rewrite /disjoint_ptr /XMSS_SIG_BYTES in E.  
      smt(disjoint_ptr_ptr).
  do split; 1,2: by smt().
    + rewrite H19; apply (eq_from_nth witness); rewrite !size_load_buf //; 1..3: by rewrite to_uintB ?of_uintK ?uleE;smt(@W64). 
      rewrite /XMSS_SIG_BYTES. 
      have ->: to_uint (sm_len - (of_int 4963)%W64) = to_uint sm_len - XMSS_SIG_BYTES.
         * rewrite to_uintB; 1: by rewrite uleE /#.
           by rewrite of_uintK /= /XMSS_SIG_BYTES.
      rewrite /XMSS_SIG_BYTES => j?.
      rewrite /XMSS_SIG_BYTES in E.
      have E1: disjoint_ptr (to_uint ptr_sm+XMSS_SIG_BYTES) (to_uint sm_len-XMSS_SIG_BYTES) 
               (to_uint ptr_mlen) 8 by smt(disjoint_ptr_offset).
      rewrite !nth_load_buf // storeW64E /stores => />.
      rewrite !bits8E !get_setE. 
      have ->: to_uint (ptr_sm + (of_int 4963)%W64) = 
               to_uint ptr_sm + XMSS_SIG_BYTES by rewrite /XMSS_SIG_BYTES to_uintD_small /#.
      rewrite !ifF 1..7:/#; smt(disjoint_ptr_ptr).

seq 0 0 : (
    #pre /\
    load_buf Glob.mem{1} sm_ptr{1} XMSS_INDEX_BYTES = EncodeIdx (s{2}.`sig_idx)
).
- auto => /> *.
  rewrite /EncodeSignature => />.
  rewrite DecodeIdxK 2:/#; first by rewrite size_sub_list.
  apply (eq_from_nth witness); rewrite size_load_buf // ?size_sub_list // /XMSS_INDEX_BYTES => i?.
  rewrite nth_sub_list //= !nth_load_buf // /#. 

seq 1 1 : (
    #pre /\ 
    to_uint idx{1} = to_uint idx_sig{2} /\
    idx_sig{2} = s{2}.`sig_idx /\
    valid_idx idx_sig{2}
).
- ecall {1} (bytes_to_ull_ptr_correct Glob.mem{1} sm_ptr{1} idx_sig{2}).
  auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 ?
             H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 *.
  split => [/# | H30 H31 H32 H33 result ->].
  rewrite /EncodeSignature => />.
  do congr; apply (eq_from_nth witness); rewrite size_load_buf // ?size_sub_list // /XMSS_INDEX_BYTES => i?.
  rewrite nth_sub_list //= !nth_load_buf // /#. 

swap {2} [5..7] -3.
   
(*
hash_message function needs to hash a structured input of the form:

toByte(X, 32) || R || root || index || M

where:
- toByte(X, 32) is padding
- R is randomness from the signature (n bytes)
- root is the public root (n bytes)
- index is the signature index (n bytes)
- M is the actual message

Instead of allocating a new buffer and copying all this data together, the implementation uses a single buffer with this layout:

[--- sig_bytes space ---][--- message ---]
 ^                       ^
 |                       |
 prefix space            message starts here
 (for padding + R +      
  root + index)

This does 

 *) 
seq 2 0 : (
  #pre /\
  load_buf Glob.mem{1} (m_ptr{1} + (of_int XMSS_SIG_BYTES)%W64) (to_uint smlen{1} - XMSS_SIG_BYTES) = Types.Msg_t.val m{2}
).
- sp.
  exists * m_ptr{1}, sm_ptr{1}, bytes{1}, Glob.mem{1}.
  elim * => P0 P2 P4 Pmem.
  call {1} (memcpy_mem_mem Pmem P0 (W64.of_int 4963)  P2 (W64.of_int 4963) P4).
  auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 
                   H16 H17 HH H18 H19 HM H20 H21 H22 H23 H24 H25 H26 H27 H28
                   H29 H30 H31 *.
have E0 : to_uint (sm_len - (of_int 4963)%W64) = to_uint sm_len - 4963 by rewrite to_uintB; [rewrite uleE /# |]; rewrite of_uintK.

  have E1 : disjoint_ptr (to_uint ptr_sm) (to_uint sm_len) (to_uint ptr_m + XMSS_SIG_BYTES) (to_uint sm_len - XMSS_SIG_BYTES).
    + have := HH. 
      rewrite /disjoint_ptr. 
      move => H k1 Hk1 k2 Hk2.
      have := H k1 Hk1 (k2 + XMSS_SIG_BYTES) _ ; smt().

  have E :  disjoint_ptr (to_uint ptr_sm) (XMSS_SIG_BYTES) 
                         (to_uint ptr_mlen) 8 by smt().

  do split. 

    * smt(W64.to_uint_cmp).
    * smt(W64.to_uint_cmp).
    * smt(W64.to_uint_cmp).
    * smt(W64.to_uint_cmp).
    * smt(W64.to_uint_cmp).
    * rewrite H27 E0.
      have X: disjoint_ptr (to_uint ptr_sm + 4963) (to_uint sm_len - 4963)
         (to_uint ptr_m + 4963) (to_uint sm_len - 4963) by smt(disjoint_ptr_offset).
      smt().
    * auto => /> H32 H33 H34 H35 H36 H37 memL H38 H39 *.
      do split.

         - smt(W32.to_uint_cmp).
         - move => ?. (* TODO: indentacao *)
      suff ->: (EncodeSignature (load_sig_mem memL ptr_sm)).`sig_idx =
               (EncodeSignature (load_sig_mem Pmem ptr_sm)).`sig_idx by apply H1.
      congr; congr.
      apply (eq_from_nth witness); rewrite !size_load_sig /XMSS_SIG_BYTES //= => b?.
      rewrite /load_sig_mem !nth_load_buf 1,2:/# H39 //= 1:/#.
      have: forall k, 4963 <= k < to_uint sm_len =>
              to_uint ptr_sm + b <> to_uint ptr_m + k.
        move=> k Hk_range.
        have := HH; rewrite /disjoint_ptr => Hdisj_full.
        have Hb_bound: 0 <= b < XMSS_SIG_BYTES by smt().
        have Hk_bound: 0 <= k < to_uint sm_len by smt().
        smt().
      move=> ?.
      have ?: 4963 <= to_uint (loadW64 Pmem (to_uint ptr_mlen)) + 4963 by smt().
      smt().

         - rewrite H19. (* TODO: indentacao *)
      apply (eq_from_nth witness); rewrite !size_load_buf /XMSS_SIG_BYTES//=; 1..3: by smt(W64.to_uint_cmp).
      have ->: to_uint (sm_len - W64.of_int 4963) = to_uint sm_len - XMSS_SIG_BYTES by smt(@W64).
      move => b?.
      rewrite !nth_load_buf //= H39 //=; first by smt(@W64 pow2_64).
      have: forall k, 0 <= k < to_uint (loadW64 Pmem (to_uint ptr_mlen)) =>
              to_uint ptr_sm + XMSS_SIG_BYTES + b <> to_uint ptr_m + 4963 + k.
        move=> k Hk_range.
        have := H37; rewrite /disjoint_ptr => Hdisj_full.
        have ?: 0 <= b < to_uint sm_len - XMSS_SIG_BYTES by smt().
        have ?: 0 <= k < to_uint (loadW64 Pmem (to_uint ptr_mlen)) by smt().
        have ?: to_uint (loadW64 Pmem (to_uint ptr_mlen)) = to_uint sm_len - 4963 by smt(@W64).
        have ?: 0 <= XMSS_SIG_BYTES + b < to_uint sm_len by smt().
        have ?: 0 <= 4963 + k < to_uint sm_len by smt().
        smt().
      move=> ?.
      rewrite to_uintD_small; [smt(@W64 pow2_64) | ].
      smt().

         - congr. (* TODO; Indentacao *)
      apply (eq_from_nth witness); rewrite !size_load_sig /XMSS_SIG_BYTES //= => b?.
      rewrite /load_sig_mem !nth_load_buf 1,2:/# H39 //= 1:/#.
      have: forall k, 4963 <= k < to_uint sm_len =>
              to_uint ptr_sm + b <> to_uint ptr_m + k.
        move=> k Hk_range.
        have := HH; rewrite /disjoint_ptr => Hdisj_full.
        have ?: 0 <= b < XMSS_SIG_BYTES by smt().
        have ?: 0 <= k < to_uint sm_len by smt().
        smt().
      move=>?.
      have ?: 4963 <= to_uint (loadW64 Pmem (to_uint ptr_mlen)) + 4963 by smt().
      smt().

         - suff ->: loadW64 memL (to_uint ptr_mlen) = loadW64 Pmem (to_uint ptr_mlen) by apply H27.
      rewrite /loadW64 !pack8E !wordP => j Hj.
      rewrite !initiE //= !initiE //= 1,2:/#.
      congr; rewrite H39 //=.
        * smt().
        * smt(disjoint_ptr_ptr).

         - rewrite -H28. (* TODO: Indentacao *)
      suff mem_eq: forall i, 0 <= i < XMSS_INDEX_BYTES =>
                       memL.[to_uint ptr_sm + i] = Pmem.[to_uint ptr_sm + i].
                * apply (eq_from_nth witness); rewrite !size_load_buf /XMSS_INDEX_BYTES //= => idx Hidx.
                  rewrite !nth_load_buf //= /#.
      move => idx Hidx; rewrite H39 //= 1:/#.
      have: forall k, 4963 <= k < to_uint (loadW64 Pmem (to_uint ptr_mlen)) + 4963 =>
              to_uint ptr_sm + idx <> to_uint ptr_m + k.
        move=> k Hk_range.
        have := HH; rewrite /disjoint_ptr => Hdisj_full.
        have Hidx_bound: 0 <= idx < XMSS_INDEX_BYTES by smt().
        smt().
      move=> ?.
      smt().
         
         - rewrite /XMSS_SIG_BYTES H19. (* TODO: Indentacao *)
           have ->: to_uint (sm_len - W64.of_int XMSS_SIG_BYTES) =
               to_uint (loadW64 Pmem (to_uint ptr_mlen)). rewrite E0. smt().
have len_eq: to_uint sm_len - 4963 = to_uint (loadW64 Pmem (to_uint ptr_mlen)).
        * rewrite -E0 -H27 /#.
      rewrite len_eq H38.
      apply (eq_from_nth witness); rewrite !size_load_buf //= => i Hi.
      rewrite !nth_load_buf //= H39 //=.
        * smt(@W64 pow2_64).
          have ?: 0 <= i < to_uint (loadW64 Pmem (to_uint ptr_mlen)) by smt().

          move : H37 Hi; rewrite /disjoint_ptr -len_eq => H Hi.
          rewrite to_uintD_small /=;1: by smt(@W64 pow2_64).
             have -> :  to_uint ptr_m + 4963 + (to_uint sm_len - 4963) = to_uint ptr_m + to_uint sm_len by ring. 
          have ? : forall j, 0 <= j < to_uint sm_len - 4963 =>
             to_uint ptr_m + 4963 + j <> to_uint ptr_sm + 4963 + i; by smt().

seq 3 2 : (
  #pre /\ 
  to_list buf{1} = NBytes.val _R{2} /\
  _R{2} = s{2}.`r /\
  idx_bytes{2} = (NBytes.insubd (toByte idx_sig{2} n))%NBytes  
).
- sp; exists * t64{1}; elim * => P.
  call {1} (p_memcpy_ptr_correct P).
  auto => /> &1 &2 *; do split => *; 1..3: by smt(@W64 pow2_64).
  apply (eq_from_nth witness); rewrite size_to_list ?NBytes.valP ?n_val // => i?.
  rewrite get_to_list initiE //= /EncodeSignature => />.
  rewrite /XMSS_INDEX_BYTES /XMSS_N NBytes.insubdK; first by rewrite /P size_sub_list /#.
  rewrite nth_sub_list // nth_load_buf 1:/# /loadW8.
  congr; rewrite to_uintD /#.

outline {2} [1..2] by { 
    _M' <@ M_Hash.hash (
          (ThreeNBytesBytes.insubd (NBytes.val _R ++ NBytes.val root ++ NBytes.val idx_bytes))%ThreeNBytesBytes, 
          Types.Msg_t.val m); 
}.

seq 2 0 : (
    #pre /\
    to_uint t64{1} = to_uint m_ptr{1} + 4963 - 32 - 3 * 32
); first by auto => /> *; have E : 0 < to_uint sm_len; [smt() | smt(@W64 pow2_64)].

seq 1 0 : (#pre /\ bytes{1} = smlen{1} - (of_int 4963)%W64); first by auto.

seq 0 0 : (
  #pre /\
  load_buf Glob.mem{1} (m_ptr{1} + (of_int (4963 - 32 - 3 * 32 + 128))%W64) (to_uint bytes{1}) = Types.Msg_t.val m{2}
).
- auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 
  H16 ?H17 H18 H19 HM H20 H21 H22 H23 H24 H25 H26 H27 H28 H29
  H30 H31 <- *. 
  apply (eq_from_nth witness); rewrite !size_load_buf //; 1..3:smt(@W64 pow2_64).
  have ->: to_uint (sm_len - (of_int 4963)%W64) = to_uint sm_len - 4963 by rewrite to_uintB ?uleE of_uintK /#.
  smt(@W64 pow2_64).
  move => i?.
  rewrite !nth_load_buf //. 
  smt(@W64 pow2_64).
   
seq 1 1 : (
  #pre /\ 
  to_list root{1} = NBytes.val _M'{2}
).
- do 2! (inline {1} 1; wp; sp); exists * Glob.mem{1}, buf{1}, (init (fun (i_0 : int) => pk{1}.[0 + i_0]))%Array32, idx{1}, t64{1}, bytes{1}. 
  elim * => P0 P1 P2 P3 P4 P5.
  call {1} (hash_message_correct P0 P1 P2 P3 P4 P5) => [/# |]. 
  auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 
  H16 H17 H18 H19 HM H20 H21 H22 H23 H24 H25 H26 H27 H28 H29
  H30 H31 H32 H33 H34 H35 H36 *.
  do split; 1,3: by smt(@W64 pow2_64).
   + rewrite to_uintB ?uleE of_uintK /= /#. 
   + smt().
   + apply three_nbytes_eq; apply (eq_from_nth witness); rewrite !ThreeNBytesBytes.valP ?n_val // => i?. 
     rewrite !ThreeNBytesBytes.insubdK ?size_cat ?size_toByte_32 // ?n_val ?size_to_list ?size_toByte_64 //= ?NBytes.valP ?n_val //=.
     rewrite H34.
     case (0 <= i < n) => [H_first | ?].
        * rewrite nth_cat !size_cat !NBytes.valP ifT 1:/#.
          rewrite nth_cat !NBytes.valP ifT 1:/#.
          rewrite nth_cat !size_cat !NBytes.valP size_to_list ifT 1:/#.
          rewrite nth_cat !NBytes.valP ifT /#.
     case (n <= i < 2 * n) => [H_snd | H_trd].
        * rewrite nth_cat !size_cat !NBytes.valP.
          rewrite nth_cat !NBytes.valP ifT 1:/# ifF 1:/#.
          rewrite nth_cat !size_cat !NBytes.valP size_to_list ifT 1:/#.
          rewrite nth_cat !NBytes.valP ifF 1:/#.
          rewrite get_to_list initiE //= 1:/#.
          rewrite /EncodePkNoOID /= NBytes.insubdK ?size_sub 1,2:/# nth_sub /#.
        * rewrite nth_cat !size_cat !NBytes.valP.
          rewrite nth_cat !NBytes.valP ifF 1:/#.
          rewrite nth_cat !size_cat !NBytes.valP size_to_list ifF 1:/#.
          rewrite NBytes.insubdK. search toByte.
              + rewrite size_toByte_32 /#.
          smt(toByte_W32_eq_toByte_64_W64).

   + rewrite -H36; congr. 
     rewrite wordP => j?.
     rewrite !get_to_uint (: 0 <= j < 64 = true) 1:/# /=.
     rewrite !to_uintD H35 !of_uintK /#.

   + auto => /> ? H37 H38 H39 H40 H41 resL resR memL H42 H43 H44 *.
 do split.
        * smt(W32.to_uint_cmp).
        * move => Hx.
          rewrite /XMSS_FULL_HEIGHT /= in H1.
          have ?: to_uint (EncodeSignature (load_sig_mem P0 ptr_sm)).`sig_idx
                              = 
                  to_uint (EncodeSignature (load_sig_mem memL ptr_sm)).`sig_idx; last by smt().
         congr; rewrite /EncodeSignature; auto => />.
         congr.
         rewrite /XMSS_INDEX_BYTES.
         apply (eq_from_nth witness); rewrite !size_sub_list //= => idx Hidx.
         rewrite !nth_sub_list //=.
         rewrite /load_sig_mem !nth_load_buf 1,2:/#.
         apply H44 => [/#|].
         have:
              forall (k : int), 
                   4835 <= k < 4963 => 
                      0 <= k < to_uint sm_len =>
                         to_uint ptr_sm + idx <> to_uint ptr_m + k
         by move => k Hk_range Hk_bound; have := H18; rewrite /disjoint_ptr => Hdisj; smt().
        smt().
        *   suff ->: 
                  load_buf memL (ptr_sm + W64.of_int XMSS_SIG_BYTES) 
                                (to_uint (sm_len - W64.of_int XMSS_SIG_BYTES)) 
                                =
                  load_buf P0 (ptr_sm + W64.of_int XMSS_SIG_BYTES) 
                              (to_uint (sm_len - W64.of_int XMSS_SIG_BYTES)) 
            by apply HM. 
            apply (eq_from_nth witness); rewrite !size_load_buf //=; 1..3: by smt(to_uint_cmp).
            have ZZ: to_uint (sm_len - W64.of_int XMSS_SIG_BYTES) = 
                     to_uint sm_len - XMSS_SIG_BYTES.
            - by rewrite to_uintB ?uleE to_uint_small //#.

  rewrite !ZZ=> i Hi.
  rewrite !nth_load_buf //=.
  rewrite H44 //; [smt(@W64 pow2_64) | ].

  have: forall k, 4835 <= k < 4963 => 0 <= k < to_uint sm_len =>
          to_uint ptr_sm + XMSS_SIG_BYTES + i <> to_uint ptr_m + k; last first.
           - have Hsm_bound: 4963 <= to_uint sm_len by rewrite /XMSS_SIG_BYTES in H2; smt(). smt(@W64 pow2_64).
    move=> k Hk_range Hk_bound.
    have := H18; rewrite /disjoint_ptr.
    move => ?; smt(disjoint_ptr_ptr).
        *
  suff ->: load_sig_mem P0 ptr_sm = load_sig_mem memL ptr_sm by trivial.
  apply (eq_from_nth witness); rewrite !size_load_sig // => i Hi.
  rewrite /load_sig_mem !nth_load_buf 1,2:/# H44 //; [smt(@W64 pow2_64) | ].
  have: forall k, 4835 <= k < 4963 => 0 <= k < to_uint sm_len =>
          to_uint ptr_sm + i <> to_uint ptr_m + k.
    move=> k Hk_range Hk_bound.
have := H18; rewrite /disjoint_ptr => Hdisj_full.
    have Hi_bound: 0 <= i < to_uint sm_len by rewrite /XMSS_SIG_BYTES in Hi; smt().
    have Hk_bound2: 0 <= k < to_uint sm_len by smt(). smt().

  move=> Hdisj; rewrite H35.
  have Hsm_bound: 4963 <= to_uint sm_len by rewrite /XMSS_SIG_BYTES in H2; smt().
  smt().
 
  * suff ->: loadW64 memL (to_uint ptr_mlen) = loadW64 P0 (to_uint ptr_mlen) by apply H28.
  rewrite /loadW64 !pack8E !wordP => j Hj.
  rewrite !initiE //= !initiE //= 1,2:/#.
  rewrite H44 //; [smt(@W64 pow2_64) | ].
  have: forall i, 0 <= i < 8 =>
          forall k, 4835 <= k < 4963 => 0 <= k < to_uint sm_len =>
          to_uint ptr_mlen + i <> to_uint ptr_m + k.
    move=> i Hi k Hk_range Hk_bound.
    have := H17; rewrite /disjoint_ptr => Hdisj_full.
    have Hi_bound: 0 <= i < 8 by smt().
    have Hk_bound2: 0 <= k < to_uint sm_len by smt().
    smt().
  move=> Hdisj; rewrite H35.
  have Hsm_bound: 4963 <= to_uint sm_len by rewrite /XMSS_SIG_BYTES in H2; smt().
  smt(disjoint_ptr_ptr).

  *   suff ->: load_buf memL ptr_sm XMSS_INDEX_BYTES = load_buf P0 ptr_sm XMSS_INDEX_BYTES by apply H29.
  apply (eq_from_nth witness); rewrite !size_load_buf /XMSS_INDEX_BYTES //= => i Hi.
  rewrite !nth_load_buf //= -H44 //; [smt(@W64 pow2_64) | ].
  have: forall k, 4835 <= k < 4963 => 0 <= k < to_uint sm_len =>
          to_uint ptr_sm + i <> to_uint ptr_m + k by smt().
  smt().

* suff ->: load_buf memL (ptr_m + W64.of_int XMSS_SIG_BYTES) (to_uint sm_len - XMSS_SIG_BYTES) =
           load_buf P0 (ptr_m + W64.of_int XMSS_SIG_BYTES) (to_uint sm_len - XMSS_SIG_BYTES) by apply H33.
  apply (eq_from_nth witness); rewrite !size_load_buf. 
smt().
smt().
smt().
smt().
  move=> i Hi.
  rewrite !nth_load_buf //=.
  rewrite -H44 //; [smt(@W64 pow2_64) | ].
  rewrite H35 /XMSS_SIG_BYTES.
  have ->: to_uint (ptr_m + W64.of_int 4963) = to_uint ptr_m + 4963 by rewrite to_uintD_small; smt(@W64 pow2_64).
  smt().

*    suff ->: load_buf memL (ptr_m + W64.of_int 4963) (to_uint (sm_len - W64.of_int 4963)) =
           load_buf P0 (ptr_m + W64.of_int 4963) (to_uint (sm_len - W64.of_int 4963)) by apply H36.
apply (eq_from_nth witness); rewrite !size_load_buf. 
smt().
smt().
smt().
smt().
  move=> i Hi.
  rewrite !nth_load_buf //=.
  rewrite -H44 //; [smt(@W64 pow2_64) | ].
  rewrite H35 /XMSS_SIG_BYTES.
  have ->: to_uint (ptr_m + W64.of_int 4963) = to_uint ptr_m + 4963 by rewrite to_uintD_small; smt(@W64 pow2_64).
  smt().

(* ======================= ============== *)
 
seq 2 0 : (
    #{/~sm_offset{1} = W64.zero}
     {/~to_uint t64{1} = to_uint m_ptr{1} + 4963 - 32 - 3 * 32}pre /\
    to_uint sm_offset{1} = 35
); first by auto.
 
unroll {1} 2; rcondt {1} 2; first by auto.
    
conseq />.

(*
started here 
*)

swap {2} 1 1.

seq 3 1 : (
    #pre /\ 
    i{1} = W32.zero /\ 
    ={idx_leaf} /\
    0 <= to_uint idx_leaf{1} < 2 ^ XMSS_FULL_HEIGHT
).
- auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 HM H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 *.
  split. rewrite andwC; congr; first by smt(@W32 pow2_32).
  by rewrite h_val d_val /(`<<`).
  rewrite /XMSS_FULL_HEIGHT /=.
  split.
smt(W32.to_uint_cmp).
  move => Ha.
  rewrite /(`<<`) /=; have -> : 1023 = (2^10 - 1) by auto.
  rewrite W32.andwC and_mod //= of_uintK /=.
  by smt(W32.to_uint_cmp).

 
seq 1 1 : (
  #{/~to_uint idx{1} = to_uint idx_sig{2}}pre /\
  to_uint idx{1} = to_uint idx_tree{2} /\
  0 <= to_uint idx{1} < 2 ^ XMSS_FULL_HEIGHT
).
- auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 
                   H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 
                   H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 *.
  rewrite h_val d_val /= to_uint_shr ?of_uintK //=.
  rewrite to_uint_shr 1:/# /= /#.
   
seq 0 1 : (
    #pre /\ 
    (sig_ots{2}, auth{2}) = nth witness s{2}.`r_sigs 0
); first by auto => /> /#.

seq 3 1 : #pre.
- inline {1}.
  auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 
                   H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 
                   H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 *.
  rewrite /zero_address /set_layer_addr.
  do split.
    * rewrite tP => i?.
      rewrite initiE 1:/# get_setE 1:/# initiE 1:/#.
      case: (i = 0) => /#.
    * rewrite tP => i?.
      rewrite initiE 1:/# get_setE 1:/# initiE 1:/#.
      case: (i = 0) => /#.
    * move => k??.
      rewrite get_setE /#.      
    * move => k??.
      rewrite get_setE /#.


seq 3 1 : (
  #{/~(forall (k : int),
       0 <= k && k < 8 => k <> 3 => ltree_addr{1}.[k] = W32.zero)}
   {/~(forall (k : int),
       0 <= k && k < 8 => k <> 3 => node_addr{1}.[k] = W32.zero)}
   {/~ots_addr{1} = zero_address}
   {/~address{2} = zero_address}pre /\
   ots_addr{1}.[3] = W32.zero /\

   sub ots_addr{1} 0 4 = sub address{2} 0 4 /\
   sub ltree_addr{1} 0 3 = sub address{2} 0 3 /\
   sub node_addr{1} 0 3 = sub address{2} 0 3 /\
   node_addr{1}.[4] = W32.zero
).
- inline {1}.
  auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 
                   H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 
                   H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 *.
  rewrite /zero_address /set_tree_addr.
  rewrite /XMSS_FULL_HEIGHT /= in H39.
  do split.
    * apply (eq_from_nth witness); rewrite !size_sub //= => j?.
      rewrite !nth_sub 1,2:/# /= !get_setE 1..4:/#.
      case: (j = 1) => ?.
         + rewrite ifF 1:/# ifF 1:/#.
           rewrite /truncateu32 to_uint_shr 1:/#.
           congr.
           rewrite of_uintK /#.
      case: (j = 2) => [?| /#].
         * rewrite /truncateu32.
           congr. 
           smt(@W32 pow2_32).
    * apply (eq_from_nth witness); rewrite !size_sub //= => j?.
      rewrite !nth_sub 1,2:/# /= !get_setE 1..4:/#.
      case: (j = 1) => ?.
         + rewrite ifF 1:/# ifF 1:/#.
           rewrite /truncateu32 to_uint_shr 1:/#.
           congr.
           rewrite of_uintK /#.
      case: (j = 2) => ?.
         * rewrite /truncateu32.
           congr. 
           rewrite H40 ; smt(@W32 pow2_32).
         * have ->: j = 0 by smt().
           rewrite initiE 1:/#.    
           by apply H26.
    * apply (eq_from_nth witness); rewrite !size_sub //= => j?.
      rewrite !nth_sub 1,2:/# /= !get_setE 1..4:/#.
      case: (j = 1) => ?.
         + rewrite ifF 1:/# ifF 1:/#.
           rewrite /truncateu32 to_uint_shr 1:/#.
           congr.
           rewrite of_uintK /#.
      case: (j = 2) => ?.
         * rewrite /truncateu32.
           congr. 
           rewrite -H40 ; smt(@W32 pow2_32).
         * have ->: j = 0 by smt().
           rewrite initiE 1:/#.    
           by apply H28.
     * smt().

inline {2} 1.
conseq />.
 
seq 0 7 : (
  #pre /\

   idx_sig0{2} = idx_leaf{2} /\
   sig_ots0{2} = sig_ots{2} /\
   auth0{2} = auth{2} /\
   M{2} = _M'{2} /\
   _seed{2} = seed{2} /\
  
   sub ots_addr{1} 0 4 = sub address0{2} 0 4 /\
   sub ltree_addr{1} 0 3 = sub address0{2} 0 3 /\
   sub node_addr{1} 0 3 = sub address0{2} 0 3
); first by auto => /> *; do split; apply (eq_from_nth witness); rewrite !size_sub // => i?; rewrite !nth_sub // !get_setE //; smt(sub_k).

seq 1 1 : (#pre /\ sub ots_addr{1} 0 5 = sub address0{2} 0 5).
- inline {1}; auto => /> *; do split; apply (eq_from_nth witness); rewrite !size_sub // => i?; rewrite !nth_sub // !get_setE //; smt(sub_k).

seq 3 0 : (
    #pre /\ 
   to_uint t64{1} = to_uint sm_ptr{1} + 35 /\
   sig_ots0{2} = EncodeWotsSignature (load_sig Glob.mem{1} t64{1})
).
- auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15
H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29
H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43
H44 H45 H46 H47 *.
  do split.
    * smt(@W64 pow2_64).                         
    * have ->: sig_ots{2} = (nth witness (EncodeSignature (load_sig_mem Glob.mem{1} ptr_sm)).`r_sigs 0).`1 by smt().
  rewrite /EncodeSignature /=.
  rewrite (nth_map witness); first by rewrite size_chunk 1:/# size_sub_list size_load_sig /#.
  rewrite nth_chunk 1:/# ?size_sub_list ?size_load_sig 1,2:/#.
  rewrite /EncodeReducedSignature /=.
  rewrite /EncodeWotsSignatureList /EncodeWotsSignature.
  congr; congr; congr.
  have ->: sm_offset{1} = W64.of_int 35 by smt(@W64).
  rewrite /load_sig_mem /load_sig /XMSS_INDEX_BYTES /XMSS_N.
  apply (eq_from_nth witness); first by rewrite size_sub_list 1:/# size_to_list /#.
  rewrite size_sub_list 1:/# => i Hi.
  rewrite nth_sub_list 1:/# get_to_list initiE 1:/# /=.
  rewrite nth_take 1,2:/# nth_drop 1,2:/# nth_sub_list 1:/#.
  rewrite nth_load_buf 1:/# /loadW8.
  congr; rewrite to_uintD_small; smt(@W64 pow2_64).
 
seq 1 1 : (
  #pre /\
  wots_pk{1} = DecodeWotsPk pk_ots{2}
).
- wp.
  exists * root{1}, pub_seed{1}, ots_addr{1}, address0{2}. 
  elim * => P1 P2 P3 P4; call (pk_from_sig_correct P1 P2 P3 P4) => [/# |].
- auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15
H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29
H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43
H44 H45 H46 ? H47 ?HH *.
  do split.
    + smt(W64.to_uint_cmp).
    + smt(@W64 pow2_64).
    + rewrite H34; smt(@NBytes). 
    + rewrite H22; smt(@NBytes).
    + auto => /> H48 H49 resL resR  H50 H51 *.
      do split.
        * smt(sub_k).
        * apply (eq_from_nth witness); rewrite !size_sub //= => j?.
          rewrite -H43.
          have ->: nth witness (sub P3 0 4) j = nth witness (sub P3 0 5)j
                   by rewrite !nth_sub /#. 
          rewrite -H51 !nth_sub /#.
        * apply (eq_from_nth witness); rewrite !size_sub //= => j?.
          have ->: nth witness (sub P4 0 4) j =
                   nth witness (sub P4 0 5) j by rewrite !nth_sub /#.
          rewrite -HH -H51 !nth_sub /#. 
        * apply (eq_from_nth witness); rewrite !size_sub //= => j?.
          rewrite -HH H51 /#.
 
seq 0 0 : (
     #{/~to_uint t64{1} = to_uint sm_ptr{1} + 35}
     {/~sig_ots0{2} = EncodeWotsSignature (load_sig Glob.mem{1} t64{1})}pre /\
     sig_ots0{2} = EncodeWotsSignature (load_sig Glob.mem{1} (sm_ptr{1} + W64.of_int 35))
).
- auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15
H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29
H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43
H44 H45 H46 ? H47 H48 *. 
congr.
congr.
rewrite wordP => k?.
rewrite !get_to_uint (: 0 <= k < 64) 1:/# /=.
rewrite to_uintD_small of_uintK /#.

seq 3 0 : (#{/~to_uint sm_offset{1} = 35}pre /\ to_uint sm_offset{1} = 2179); first by auto => /> *; smt(@W64).
 
seq 1 2 : (
   #{/~sub ots_addr{1} 0 4 = sub address0{2} 0 4}
{/~sub ots_addr{1} 0 5 = sub address0{2} 0 5}pre /\
   sub ltree_addr{1} 0 5 = sub address0{2} 0 5
).
- inline {1}.
auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15
H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29
H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43
H44 H45 ? H46 H47 *. 
do split; apply (eq_from_nth witness); rewrite !size_sub // => i?; rewrite !nth_sub //= !get_setE //.
 - smt(sub_k).
 - smt(sub_k).
 - smt(sub_k).
 - case: (i = 3) => ?.
      * rewrite !ifF 1..6:/#.
        smt().
   case: (i = 4)=> ?.
      * smt(@W32 pow2_32).
   rewrite !ifF 1..3:/#.
   smt(sub_k).

wp; conseq />.
  
seq 1 1 : (
    #{/~wots_pk{1} = DecodeWotsPk pk_ots{2}}pre /\ 
    to_list leaf{1} = NBytes.val nodes0{2}
).
- exists * wots_pk{1}, pub_seed{1}, ltree_addr{1}, address0{2}.
  elim * => P0 P1 P2 P3.
  call (ltree_correct P0 P1 P2 P3) => [/#|]. 
  auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15
H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29
H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47*.
  do split. smt(enc_dec_wots_pk). smt(@NBytes).
  move => ? H48 resL resR H49 H50 *.
  do split.
     * smt(sub_k).
     * rewrite -H43.
      apply (eq_from_nth witness); rewrite !size_sub // => j?.
      rewrite !nth_sub 1,2:/# /=.
      have ->: resL.`3.[j] = nth witness (sub resL.`3 0 5) j by rewrite nth_sub /#.
      rewrite H50 nth_sub /#.
     *rewrite -H46.
      apply (eq_from_nth witness); rewrite !size_sub // => j?.
      rewrite !nth_sub 1,2:/# /=.
      have ->: resL.`3.[j] = nth witness (sub resL.`3 0 5) j by rewrite nth_sub /#.
      rewrite H50 nth_sub /#.
     * by rewrite H50 /#.

seq 0 2 : (
    #{/~sub ltree_addr{1} 0 5 = sub address0{2} 0 5}pre /\ 
     sub node_addr{1} 0 5 = sub address0{2} 0 5 /\
    to_uint address0{2}.[6] = to_uint idx_leaf{1}
).
- inline {1}.
  auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15
H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29
H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46*.
  rewrite /set_tree_index /set_type.
  do split; apply (eq_from_nth witness); rewrite !size_sub // => j?.
    * rewrite !nth_sub 1,2:/# /= !get_setE 1..6:/#.
      rewrite !ifF 1..6:/#. smt(sub_k).
    * rewrite !nth_sub 1,2:/# /= !get_setE 1..6:/#.
      rewrite !ifF 1..6:/#. smt(sub_k).
    * rewrite !nth_sub 1,2:/# /= !get_setE 1..6:/#.
      case: (j = 3) => ?.
         + rewrite !ifF 1..5:/#.
           smt().
      case: (j = 4) => ?.
         + rewrite ifF 1:/#. smt().
      rewrite !ifF 1..4:/#.
      smt(sub_k).
 
seq 4 0 : (
    #pre /\ 
    t64{1} = sm_ptr{1} + sm_offset{1} 
); first by auto.

outline {2} [1..2] by { nodes0 <@ ComputeRoot.compute_root (_seed, nodes0, address0, idx_sig0, auth0); }; conseq />.
   
seq 1 2 : (
  #{/~to_list root{1} = NBytes.val _M'{2}}
   {/~to_list pub_root{1} = NBytes.val root{2}}
   {/~to_list leaf{1} = NBytes.val nodes0{2}}pre /\
   to_list root{1} = NBytes.val node{2}
).
wp; exists * leaf{1}, pub_seed{1}, idx_leaf{1}, t64{1}, node_addr{1}, address0{2}.
elim * => P0 P1 P2 P3 P4 P5.
call (compute_root_equiv P0 P1 P2 P3 P4 P5) => [/# |].
skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15
H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29
H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43
H44 H45 H46 H47 H48 H49 H50 H51 *.
do split.
- rewrite H22; smt(@NBytes).
- rewrite H49; smt(@NBytes).
- have ->: auth{2} = (nth witness (EncodeSignature (load_sig_mem Glob.mem{1} ptr_sm)).`r_sigs 0).`2 by smt().
      rewrite /EncodeSignature /=.
      rewrite (nth_map witness); first by rewrite size_chunk 1:/# size_sub_list size_load_sig /#.
      rewrite nth_chunk 1:/# ?size_sub_list ?size_load_sig 1,2:/#.
      rewrite /EncodeReducedSignature /=.
      rewrite /EncodeAuthPath /XMSS_INDEX_BYTES /XMSS_N /XMSS_AUTH_PATH_BYTES.
      congr.
      apply (eq_from_nth witness); first by rewrite !size_map !size_iota /#.
      rewrite !size_map !size_iota => i Hi.
      rewrite (nth_map witness); first by rewrite size_chunk 1:/# size_sub_list /#.
      rewrite nth_chunk 1:/#. rewrite size_sub_list /#.
      rewrite (nth_map witness); first by rewrite size_chunk 1:/# size_load_buf /#.
      rewrite nth_chunk 1:/# ?size_load_buf 1,2:/#.
      congr; apply (eq_from_nth witness).
      rewrite size_take 1:/# size_drop 1:/# size_sub_list 1:/#.
      rewrite size_take 1:/# size_drop 1:/# size_load_buf 1:/#. smt().
      rewrite size_take 1:/# size_drop 1:/# size_sub_list 1:/#.
      move => j?.
      rewrite /XMSS_REDUCED_SIG_BYTES /XMSS_WOTS_SIG_BYTES /XMSS_SIG_BYTES /=.
      congr; congr; congr.
      apply (eq_from_nth witness). rewrite size_sub_list 1:/# size_load_buf /#.
      rewrite size_sub_list 1:/# => k?.
      rewrite nth_sub_list 1:/#. rewrite nth_take 1,2:/#.
      rewrite nth_load_buf 1:/# nth_drop 1,2:/#.
      rewrite nth_sub_list /= 1:/#.
      rewrite nth_load_buf 1:/#.
      congr.
      rewrite to_uintD /#.
- smt(W64.to_uint_cmp).
- smt(@W64 pow2_64).
- smt(W64.to_uint_cmp).
- smt(@W64 pow2_64).
- move => H52 H53 H54 H55 H56 H57 H58 H59 resL resR H60 H61 *.
  do split.
    + have ->: resL.`2.[3] = nth witness (sub resL.`2 0 5) 3 by rewrite nth_sub /#.
      by rewrite H61 nth_sub 1:/# H26.
    + rewrite -H44.
      apply (eq_from_nth witness); rewrite !size_sub // => j?.
      rewrite !nth_sub 1,2:/# /=.
      have ->: resL.`2.[j] = nth witness (sub resL.`2 0 5) j by rewrite nth_sub /#.
      rewrite H61 nth_sub /#.
    + have ->: resL.`2.[4] = nth witness (sub resL.`2 0 5) 4 by rewrite nth_sub /#.
      by rewrite H61 nth_sub 1:/# H45.
    + rewrite -H47.
      apply (eq_from_nth witness); rewrite !size_sub // => j?.
      rewrite !nth_sub 1,2:/# /=.
      have ->: resL.`2.[j] = nth witness (sub resL.`2 0 5) j by rewrite nth_sub /#.
      rewrite H61 nth_sub /#.
    + by rewrite H61 H50.

(* TODO: loop; move the proof here when all the subgoals are proved *)
  
seq 4 1 : (
  #{/~t64{1} = sm_ptr{1} + sm_offset{1}}
   {/~to_uint sm_offset{1} = 2179}
   {/~i{1} = W32.zero}pre /\
   to_uint sm_offset{1} = 2179 + 320 /\
   to_uint i{1} = j{2} /\
   j{2} = 1
).
- auto => /> &1 &2 *; smt(@W64 pow2_64).
  
while (
    (* Loop bounds *)
    1 <= j{2} <= d /\
    to_uint i{1} = j{2} /\

    (* Index relationships *)
  ={idx_leaf} /\
  0 <= to_uint idx_leaf{1} < 2^XMSS_FULL_HEIGHT /\
 
    to_uint idx{1} = to_uint idx_tree{2} /\

    (* Public key relationships *)
    to_list pub_root{1} = NBytes.val root{2} /\
    to_list pub_root{1} = sub pk{1} 0 n /\
    to_list pub_seed{1} = NBytes.val seed{2} /\
    to_list pub_seed{1} = sub pk{1} n n /\

    (* Address type fields *)
    ots_addr{1}.[3] = W32.zero /\
    ltree_addr{1}.[3] = W32.one /\
    node_addr{1}.[3] = (of_int 2)%W32 /\

    (* Address relationships - first 3 elements (layer) *)
    sub ots_addr{1} 0 4 = sub address{2} 0 4 /\
    sub ltree_addr{1} 0 3 = sub address{2} 0 3 /\
    sub node_addr{1} 0 3 = sub address{2} 0 3 /\
 
    (* Signature and memory relationships *)
    valid_idx (EncodeSignature (load_sig_mem Glob.mem{1} ptr_sm)).`sig_idx /\
    s{2} = EncodeSignature (load_sig_mem Glob.mem{1} ptr_sm) /\

   sm_ptr{1} = ptr_sm /\

    (* Memory bounds *)
    0 <= to_uint ptr_sm + to_uint sm_len < 18446744073709551615 /\
    0 <= to_uint ptr_sm < 18446744073709551615 /\
    XMSS_SIG_BYTES < to_uint sm_len /\

    (* Offset formula: starts at 35, increases by REDUCED_SIG_BYTES each iteration *)
    to_uint sm_offset{1} = 35 + j{2} * XMSS_REDUCED_SIG_BYTES /\

    (* Root relationships - this is the key invariant! *)
    root{2} = pk{2}.`Types.pk_root /\
    to_list root{1} = NBytes.val node{2} /\

    (* Additional address constraints *)
    node_addr{1}.[4] = W32.zero /\

    (* Bounds for post-condition *)
    0 <= to_uint (loadW64 Glob.mem{1} (to_uint mlen_ptr{1})) /\
    to_uint (loadW64 Glob.mem{1} (to_uint mlen_ptr{1})) < 18446744073709551615 /\

    to_list root{1} = NBytes.val node{2}
); last first.
 
(* 2nd *)
auto => /> &1 &2.
rewrite /XMSS_FULL_HEIGHT /= => H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15
                 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 
                 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 
                 H44 H45 H46 H47 H48 H49 H50 *.
rewrite !d_val !ultE !of_uintK /=.
do split.
- smt().
- smt(). 
- rewrite H21.
  rewrite /EncodePkNoOID /= n_val NBytes.insubdK // size_sub /#.
- rewrite H50 /#.
- smt(W64.to_uint_cmp).
- smt(@W64 pow2_64). 

(* 1st *)
seq 2 1: #pre.
- auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15
                 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 *.
  rewrite d_val h_val /=; do split.
  rewrite(: 1023 = 2^10 - 1) 1:/# and_mod 1:/#. 
  rewrite -H4.
  rewrite /(`<<`) /=.
  rewrite W32.andwC (: 1023 = 2^10 -1) 1:/# and_mod //= of_uintK /=.
  smt(@W32 pow2_32).
  smt(W32.to_uint_cmp).
  move => ?.
  rewrite /XMSS_FULL_HEIGHT.
  rewrite /(`<<`) /=.
  rewrite W32.andwC (: 1023 = 2^10 -1) 1:/# and_mod //= of_uintK /=.
  smt(@W32 pow2_32).

seq 1 1 : #pre.
- auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15
                 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 *.

rewrite !to_uint_shr ?of_uintK 1,2:/#.

by rewrite -H4 /= h_val d_val /=.
 
seq 0 1 : (
    #pre /\ 
    (sig_ots{2}, auth{2}) = nth witness s{2}.`r_sigs 1
); first by auto => /> /#.

seq 3 1 : #pre.
- inline {1}.
  auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 
                   H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 *.
  rewrite /zero_address /set_layer_addr.
  do split; apply (eq_from_nth witness); rewrite !size_sub //= => k?.
rewrite !nth_sub 1,2:/# !get_setE 1,2:/# /=; smt(sub_k).
rewrite !nth_sub 1,2:/# !get_setE 1,2:/# /=; smt(sub_k).
rewrite !nth_sub 1,2:/# !get_setE 1,2:/# /=; smt(sub_k).


seq 3 1 : #pre.
- inline {1}.
auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15
                 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 *.
do split; apply (eq_from_nth witness); rewrite !size_sub //= => k?.
+ rewrite /set_tree_addr !nth_sub 1,2:/# !get_setE 1..4:/# /=.
  case: (k = 1) => ?.
         * rewrite ifF 1:/# ifF 1:/#.
           rewrite /truncateu32 to_uint_shr 1:/#.
           congr.
           rewrite of_uintK /#.
      case: (k = 2) => ?.
         * rewrite /truncateu32.
           congr. 
           smt(@W32 pow2_32).
     smt(sub_k).

+ rewrite /set_tree_addr !nth_sub 1,2:/# !get_setE 1..4:/# /=.
  case: (k = 1) => ?.
         * rewrite ifF 1:/# ifF 1:/#.
           rewrite /truncateu32 to_uint_shr 1:/#.
           congr.
           rewrite of_uintK /#.
      case: (k = 2) => ?.
         * rewrite /truncateu32.
           congr. 
           smt(@W32 pow2_32).
     smt(sub_k).

+ rewrite /set_tree_addr !nth_sub 1,2:/# !get_setE 1..4:/# /=.
  case: (k = 1) => ?.
         * rewrite ifF 1:/# ifF 1:/#.
           rewrite /truncateu32 to_uint_shr 1:/#.
           congr.
           rewrite of_uintK /#.
      case: (k = 2) => ?.
         * rewrite /truncateu32.
           congr. 
           smt(@W32 pow2_32).
     smt(sub_k).

wp; conseq />.

inline {2} 1.

sp 0 6.

outline {2} [9..10] by { 
    nodes00 <@ ComputeRoot.compute_root (_seed0, nodes00, address1, idx_sig1, auth1); 
}; conseq />.
 
seq 1 2: (
  #{/~address1{2} = address{2}}pre /\ 
  sub ots_addr{1} 0 5 = sub address1{2} 0 5 /\
    sub ltree_addr{1} 0 3 = sub address1{2} 0 3 /\
    sub node_addr{1} 0 3 = sub address1{2} 0 3
). 
- inline {1}.
auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15
                 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 *.
rewrite /set_ots_addr /set_type.
do split; (apply (eq_from_nth witness); rewrite !size_sub //= => k?).
- rewrite !nth_sub 1,2:/# !get_setE 1:/#. smt(sub_k).
- rewrite !nth_sub 1,2:/# !get_setE 1..7:/# /=. 
  case: (k = 4) => //= ?.
  case: (k = 3) => //= ?.
  rewrite !ifF 1..3:/#.
  have ->: ots_addr{1}.[k] = nth witness (sub ots_addr{1} 0 4) k by rewrite nth_sub /#.
  rewrite H12 nth_sub /#.
- rewrite !nth_sub 1,2:/# !get_setE 1..6:/# /=. 
  rewrite !ifF 1..6:/#.
  have ->: ltree_addr{1}.[k] = nth witness (sub ltree_addr{1} 0 3) k by rewrite nth_sub /#.
  rewrite H13 nth_sub /#.
- rewrite !nth_sub 1,2:/# !get_setE 1..6:/# /=. 
  rewrite !ifF 1..6:/#.  
  smt(sub_k).
   
seq 4 1 : (
  #pre /\ 
  wots_pk{1} = DecodeWotsPk pk_ots0{2}
).
- wp. 
  exists * root{1}, pub_seed{1}, ots_addr{1}, address1{2}.
  elim * => P1 P2 P3 P4; call (pk_from_sig_correct P1 P2 P3 P4) => [/# |].
auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15
                 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 
                 H30 H31 H32*.
do split.
    + smt(W64.to_uint_cmp).
    + smt(@W64).
    + rewrite H23; smt(@NBytes).
    + have ->: sig_ots{2} = (nth witness (EncodeSignature (load_sig_mem Glob.mem{1} ptr_sm)).`r_sigs 1).`1 by smt().
      rewrite /EncodeSignature /=.
      rewrite (nth_map witness); first by rewrite size_chunk 1:/# size_sub_list size_load_sig /#.
      rewrite nth_chunk 1:/# ?size_sub_list ?size_load_sig 1,2:/#.
      rewrite /EncodeReducedSignature /=.
      rewrite /EncodeWotsSignatureList /EncodeWotsSignature.
      congr; congr; congr.
      have ->: sm_offset{1} = W64.of_int (35 + 1 * XMSS_REDUCED_SIG_BYTES) by smt(@W64).
      rewrite /load_sig_mem /load_sig /XMSS_INDEX_BYTES /XMSS_N /XMSS_REDUCED_SIG_BYTES /XMSS_WOTS_SIG_BYTES.
      apply (eq_from_nth witness); first by rewrite size_sub_list 1:/# size_to_list /#.
      rewrite size_sub_list 1:/# => i Hi.
      rewrite nth_sub_list 1:/# get_to_list initiE 1:/# /=.
      rewrite nth_take 1,2:/# nth_drop 1,2:/# nth_sub_list 1:/#.
      rewrite nth_load_buf 1:/# /loadW8.
      congr; rewrite to_uintD_small; smt(@W64 pow2_64).
    + rewrite H7; smt(@NBytes).
    + move => H33 H34 H35 H36 H37 resL resR H38 H39 *.
      do split. smt(sub_k). 
         * apply (eq_from_nth witness); rewrite !size_sub //= => j?.
           rewrite -H12.
           have ->: nth witness (sub P3 0 4) j = nth witness (sub P3 0 5) j by rewrite !nth_sub /#.
           rewrite !nth_sub 1,2:/#. smt(sub_k).
         * apply (eq_from_nth witness); rewrite !size_sub //= => j?. smt().

seq 3 0 : (
  #{/~to_uint sm_offset{1} = 35 + j{2} * XMSS_REDUCED_SIG_BYTES}pre /\
  to_uint sm_offset{1} = 35 + 2464 + 2144
).
- auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15
                 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 
                 H30 *.
  rewrite to_uintD of_uintK H22. smt().
 
seq 1 2: (
  #{/~sub ots_addr{1} 0 5 = sub address1{2} 0 5}pre /\
  sub ltree_addr{1} 0 5 = sub address1{2} 0 5 
).
inline {1}.
auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15
                 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 
                 H30 *.
do split; apply (eq_from_nth witness); rewrite !size_sub //= => j?.
    + rewrite !nth_sub 1,2:/# get_setE 1:/# ifF 1:/#.
      have ->: ltree_addr{1}.[j] = nth witness (sub ltree_addr{1} 0 3) j by rewrite nth_sub /#.
      rewrite H13 nth_sub /#.
    + rewrite !nth_sub 1,2:/# /set_ltree_addr /set_type.
      rewrite !get_setE 1..7:/#.
      rewrite !ifF 1..7:/#.
      smt(sub_k).
    + rewrite !nth_sub 1,2:/# /set_ltree_addr /set_type.
      rewrite !get_setE 1..6:/#.
       rewrite !ifF 1..6:/#.
      smt(sub_k).
    + rewrite !nth_sub 1,2:/#.
      rewrite /set_ltree_addr /set_type.
      rewrite !get_setE /= 1..7:/#.
      case: (j < 3) => [Hj_lt3 | Hj_ge3]; first by rewrite !ifF 1..3:/#; smt(sub_k).
      case: (j = 3) => [-> | ?]; first by by rewrite ifF 1:/# ifF 1:/# ifF 1:/# /=; apply H10.
      have ->: j = 4 by smt().
      rewrite ifT 1:/# /=.
      smt().

wp; conseq />.

seq 1 1 : (
    #{/~wots_pk{1} = DecodeWotsPk pk_ots0{2}}pre /\
    to_list leaf{1} = NBytes.val nodes00{2}
).

- exists * wots_pk{1}, pub_seed{1}, ltree_addr{1}, address1{2}.
  elim * => P0 P1 P2 P3. 
  call (ltree_correct P0 P1 P2 P3) => [/#|]. 
  auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15
                 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 
                 H30 HH *.
do split. 
- smt(enc_dec_wots_pk).  
- rewrite H7; smt(@NBytes).
- move => H31 H32 resL resR H33 H34 *.
  do split.
    * rewrite -H10.
      have ->: P2.[3] = nth witness (sub P2 0 5) 3 by rewrite nth_sub. 
      rewrite -H34.
      rewrite nth_sub /#.
    * rewrite -H13.
      apply (eq_from_nth witness); rewrite !size_sub //= => j?.
      rewrite !nth_sub //=; smt(sub_k).   
    * rewrite -H29.
      apply (eq_from_nth witness); rewrite !size_sub //= => j?.
      rewrite !nth_sub //=; smt(sub_k).   
    * smt().

sp.
wp; exists * leaf{1}, pub_seed{1}, idx_leaf{1}, t64{1}, node_addr{1}, address1{2}.
elim * => P0 P1 P2 P3 P4 P5.
auto => />.
call (compute_root_equiv P0 P1 P2 P3 P4 P5) => [/# |].
auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15
                 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 
                 H30 H31 H32 H33 *.
do split.
- rewrite H7; smt(@NBytes).
- rewrite H33; smt(@NBytes).
- have ->: auth{2} = (nth witness (EncodeSignature (load_sig_mem Glob.mem{1} ptr_sm)).`r_sigs 1).`2 by smt().             
  rewrite /EncodeSignature /=.
  rewrite (nth_map witness); first by rewrite size_chunk 1:/# size_sub_list size_load_sig /#.
  rewrite nth_chunk 1:/# ?size_sub_list ?size_load_sig 1,2:/#.
  rewrite /EncodeReducedSignature /=.
  rewrite /EncodeAuthPath /XMSS_INDEX_BYTES /XMSS_N /XMSS_AUTH_PATH_BYTES.
  congr.
  apply (eq_from_nth witness); first by rewrite !size_map !size_iota /#.
  rewrite !size_map !size_iota => i Hi.
  rewrite (nth_map witness); first by rewrite size_chunk 1:/# size_sub_list /#.
  rewrite nth_chunk 1:/#. rewrite size_sub_list /#.
  rewrite (nth_map witness). rewrite size_chunk 1:/# size_load_buf /#.
  congr.
  have ->: sm_offset{1} = W64.of_int (35 + 1 * XMSS_REDUCED_SIG_BYTES + XMSS_WOTS_SIG_BYTES) by smt(@W64).
  rewrite /load_sig_mem /load_sig /XMSS_REDUCED_SIG_BYTES /XMSS_WOTS_SIG_BYTES /wots_sig_bytes /auth_path_bytes.
  rewrite nth_chunk 1:/#. rewrite size_load_buf /#.  
  congr.
  congr.
  apply (eq_from_nth witness). rewrite size_load_buf 1:/# size_sub_list /#.
  rewrite size_sub_list 1:/# => j?.
  rewrite nth_sub_list 1:/#.
  rewrite nth_take 1,2:/#.
  rewrite nth_drop 1,2:/#.
  rewrite nth_sub_list 1:/# nth_load_buf 1:/#.
  rewrite nth_load_buf 1:/# /=.
  congr.
  rewrite to_uintD /#.
- smt(W64.to_uint_cmp).
- smt(@W64 pow2_64).
- smt(W64.to_uint_cmp).
- smt(@W64 pow2_64).
- rewrite /set_tree_index /set_type.
  apply (eq_from_nth witness); rewrite !size_sub //= => j?.
  rewrite !nth_sub 1,2:/#.
  rewrite !get_setE 1..6:/#.
  rewrite ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# /=.
  case: (j = 4) => [/#|?].
  case: (j = 3) => [/#|?].
  smt(sub_k).
- move => Hx Hy H36 H37 H38 H39 H40 H41 H42 resL resR H43 H44 *.
  do split.
* smt().
* smt().
* rewrite to_uintD /#.
* smt(sub_k).
* apply (eq_from_nth witness); rewrite !size_sub //= => j?.
  rewrite !nth_sub 1,2:/#; smt(sub_k).
* rewrite !to_uintD /#.
* rewrite -H23; smt(sub_k).
* rewrite ultE of_uintK to_uintD /#.
* rewrite ultE of_uintK to_uintD /#.
qed.
