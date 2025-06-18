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

      to_uint sm_len < XMSS_SIG_BYTES /\
      0 <= to_uint sm_len - XMSS_SIG_BYTES < W64.max_uint /\

      (* pointers are valid *)
      0 <= to_uint ptr_m < W64.max_uint /\
      0 <= to_uint ptr_m + to_uint sm_len < W64.max_uint /\

      0 <= to_uint ptr_sm + to_uint sm_len < W64.max_uint /\ (* nbao entendi *)
      0 <= to_uint ptr_sm < W64.max_uint /\

      0 <= to_uint ptr_mlen + 8 < W64.max_uint /\
      0 <= to_uint ptr_mlen < W64.max_uint /\

      disjoint_ptr   (to_uint ptr_m)  (to_uint sm_len) 
                     (to_uint ptr_sm) (to_uint sm_len) /\
          
      disjoint_ptr   (to_uint ptr_m) (to_uint sm_len)
                     (to_uint ptr_mlen) 8 /\ (* 1 W64 = 8 bytes *)

      disjoint_ptr   (to_uint ptr_sm) (to_uint sm_len)
                     (to_uint ptr_mlen) 8 /\ (* 1 W64 = 8 bytes *)
   
      arg{1} = (ptr_m, ptr_mlen, ptr_sm, sm_len, _pk) /\ 
      arg{2}.`1 = EncodePkNoOID _pk /\  (* pk *)
      arg{2}.`2 = load_buf Glob.mem{1} (ptr_sm + (of_int XMSS_SIG_BYTES)%W64) 
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

seq 1 2 : ( 
  #pre /\ 
  to_list pub_root{1} = NBytes.val (pk{2}.`Types.pk_root) /\ 
  to_list pub_seed{1} = NBytes.val seed{2} /\
  to_list pub_seed{1} = sub pk{1} n n
).
    + auto => /> *; do split; apply (eq_from_nth witness); rewrite size_to_list ?NBytes.valP ?n_val // ?size_sub // => j?;
      1,2: by rewrite get_to_list /EncodePkNoOID /= NBytes.insubdK ?size_sub ?n_val // nth_sub // /#.
      rewrite get_to_list initiE // nth_sub /#.

swap {1} 4 -2.
seq 2 0 : (#pre /\ ots_addr{1} = zero_address).
    + inline {1} 2; inline {1} 1; wp.
      ecall {1} (zero_addr_res addr{1}); auto => /> &1 &2 *.
      by apply zero_addr_setZero.

swap {2} 3 -2.
seq 0 1 : (#pre /\ address{2} = zero_address); first by auto.

swap {1} 3 -1.
seq 2 0 : (
  #pre /\ 
  ltree_addr{1}.[3] = W32.one /\
  (forall (k : int), 0 <= k < 8 => (k <> 3) => ltree_addr{1}.[k] = W32.zero)
).
    + inline {1} 2; inline {1} 1; wp.
      ecall {1} (zero_addr_res addr{1}); auto => /> *.
      by rewrite get_setE //= ifF // zero_addr_i.

seq 4 0 : (
  #pre /\ 
  node_addr{1}.[3] = (of_int 2)%W32 /\
  (forall (k : int), 0 <= k < 8 => (k <> 3) => node_addr{1}.[k] = W32.zero) /\
  t64{1} = smlen{1} /\
  sm_offset{1} = W64.zero
).
    + inline {1} 2; inline {1} 1; wp.
      ecall {1} (zero_addr_res addr{1}); auto => /> *. 
      by rewrite get_setE //= ifF // zero_addr_i.
 
(* ------------------------------------------------------------------------------- *)
(*                                                                                 *)
(* ------------------------------------------------------------------------------- *)
 
seq 17 13 : (
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

(* ------------------------------------------------------------------------------- *)
(*                                                                                 *)
(* ------------------------------------------------------------------------------- *)

seq 1 0 : (#{/~t64{1} = smlen{1}}pre /\ t64{1} = smlen{1} - (of_int 4963)%W64); first by auto.

seq 1 0 : (
        #{/~t64{1} = smlen{1} - (of_int 4963)%W64}pre /\
        loadW64 Glob.mem{1} (to_uint mlen_ptr{1}) = smlen{1} - (of_int 4963)%W64
).
- auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 *.
  rewrite load_store_W64 /XMSS_FULL_HEIGHT /=.
  rewrite /XMSS_FULL_HEIGHT /= in H1.
  have E :  disjoint_ptr (to_uint ptr_sm) (XMSS_SIG_BYTES) (to_uint ptr_mlen) 8 by smt().
  have ->: load_sig_mem (storeW64 Glob.mem{1} (to_uint ptr_mlen) (sm_len - (of_int 4963)%W64)) ptr_sm = load_sig_mem Glob.mem{1} ptr_sm.
    + apply (eq_from_nth witness); rewrite !size_load_buf // /XMSS_SIG_BYTES => i?.
      rewrite !nth_load_buf // storeW64E /stores => />.
      rewrite !bits8E !get_setE !ifF 1..7:/# //. 
      rewrite /disjoint_ptr /XMSS_SIG_BYTES in E.  
      smt(disjoint_ptr_ptr).
  do split; 1,2: by smt().
    + apply (eq_from_nth witness); rewrite !size_load_buf //; 1..3: by rewrite to_uintB ?of_uintK ?uleE /#.
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
    idx_sig{2} = s{2}.`sig_idx
).
- ecall {1} (bytes_to_ull_ptr_correct Glob.mem{1} sm_ptr{1} idx_sig{2}).
  auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17
             H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 *.
  split => [/# | H30 H31 H32 H33 result ->].
  rewrite /EncodeSignature => />.
  do congr; apply (eq_from_nth witness); rewrite size_load_buf // ?size_sub_list // /XMSS_INDEX_BYTES => i?.
  rewrite nth_sub_list //= !nth_load_buf // /#. 

swap {2} [5..7] -3.
  
seq 2 0 : (
  #pre /\
  load_buf Glob.mem{1} (m_ptr{1} + (of_int XMSS_SIG_BYTES)%W64) (to_uint smlen{1} - XMSS_SIG_BYTES) = m{2}
).
- sp.
  exists * m_ptr{1}, sm_ptr{1}, bytes{1}, Glob.mem{1}.
  elim * => P0 P2 P4 Pmem.
  call {1} (memcpy_mem_mem Pmem P0 (W64.of_int 4963)  P2 (W64.of_int 4963) P4).
  auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 
                   H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29.
  have E0 : to_uint (sm_len - (of_int 4963)%W64) = to_uint sm_len - 4963 by rewrite to_uintB; [rewrite uleE /# |]; rewrite of_uintK.

  (* adicionar offset ao apontador = remover offset da length *)
  have E1 : disjoint_ptr (to_uint ptr_sm) (to_uint sm_len) (to_uint ptr_m + XMSS_SIG_BYTES) (to_uint sm_len - XMSS_SIG_BYTES) by smt(). 
  rewrite H27 E0 /#. 

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
          m); 
}.

seq 2 0 : (
    #pre /\
    to_uint t64{1} = to_uint m_ptr{1} + 4963 - 32 - 3 * 32
); first by auto => /> *; have E : 0 < to_uint sm_len; [smt() | smt(@W64 pow2_64)].

seq 1 0 : (#pre /\ bytes{1} = smlen{1} - (of_int 4963)%W64); first by auto.

seq 0 0 : (
  #pre /\
  load_buf Glob.mem{1} (m_ptr{1} + (of_int (4963 - 32 - 3 * 32 + 128))%W64) (to_uint bytes{1}) = m{2}
).
- auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 
  H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29
  H30 H31 H32. 
  apply (eq_from_nth witness); rewrite !size_load_buf //; 1..3:smt(@W64 pow2_64).
  have ->: to_uint (sm_len - (of_int 4963)%W64) = to_uint sm_len - 4963 by rewrite to_uintB ?uleE of_uintK /#.
  move => i?.
  rewrite !nth_load_buf //; first by rewrite to_uintB ?uleE of_uintK /#.
  congr.
  rewrite !to_uintD !of_uintK /= /XMSS_SIG_BYTES /#. 
 
seq 1 1 : (
  #pre /\ 
  to_list root{1} = NBytes.val _M'{2}
).
- do 2! (inline {1} 1; wp; sp); exists * Glob.mem{1}, buf{1}, (init (fun (i_0 : int) => pk{1}.[0 + i_0]))%Array32, idx{1}, t64{1}, bytes{1}. 
  elim * => P0 P1 P2 P3 P4 P5.
  call {1} (hash_message_correct P0 P1 P2 P3 P4 P5) => [/# |]. 
  auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 
  H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29
  H30 H31 H32 H33.
  do split.
   + smt(@W64 pow2_64).
   + rewrite to_uintB ?uleE of_uintK /= /#. 
   + smt(@W64 pow2_64).
   + smt().
   + apply three_nbytes_eq; apply (eq_from_nth witness); rewrite !ThreeNBytesBytes.valP ?n_val // => i?. 
     rewrite !ThreeNBytesBytes.insubdK ?size_cat ?size_toByte_32 // ?n_val ?size_to_list ?size_toByte_64 //= ?NBytes.valP ?n_val //=.
     rewrite H31; do congr. 
        * apply (eq_from_nth witness); rewrite NBytes.valP n_val ?size_to_list // => j?.
          rewrite get_to_list initiE //.
          have ->: _pk.[j] = nth witness (sub _pk 0 n) j by rewrite nth_sub /#. 
          smt().
        * apply (eq_from_nth witness); first by rewrite size_toByte_64 //= NBytes.valP n_val.
          rewrite NBytes.valP n_val => j?.
          rewrite toByte_32_64 //.
          have ->: toByte_64 P3 32 = Bytes.W64toBytes_ext P3 32 by smt(Bytes.W64toBytes_ext_toByte_64). 
          rewrite /W64toBytes_ext !nth_rev ?size_mkseq ?size_mkseq 1,2:/#.
   + smt().
   + move => H35 H36 H37 H38 H39 H40 resL resR memT H41 H42 H43.
     have ->: load_sig_mem memT ptr_sm = load_sig_mem P0 ptr_sm
              by  apply (eq_from_nth witness); rewrite !size_load_buf // => i?; rewrite !nth_load_buf // H43 // /#.
     smt(). 
 
seq 2 0 : (
    #{/~sm_offset{1} = W64.zero}
     {/~to_uint t64{1} = to_uint m_ptr{1} + 4963 - 32 - 3 * 32}pre /\
    to_uint sm_offset{1} = 35
); first by auto.
 
unroll {1} 2; rcondt {1} 2; first by auto.
   
conseq />.
 
seq 28 6 : (
  #{/~ots_addr{1} = zero_address}
   {/~address{2} = zero_address}
   {/~(forall (k : int),
      0 <= k && k < 8 => k <> 3 => ltree_addr{1}.[k] = W32.zero)}
   {/~(forall (k : int),
      0 <= k && k < 8 => k <> 3 => node_addr{1}.[k] = W32.zero)}
   {/~ to_list root{1} = NBytes.val _M'{2}}pre /\
  to_uint sm_offset{1} = 35 /\
  ots_addr{1}.[3] = W32.zero /\
  ltree_addr{1}.[3] = W32.one /\
  node_addr{1}.[3] = (of_int 2)%W32 /\
  ={idx_leaf} /\
  to_uint idx{1} = to_uint idx_tree{2} /\
  to_list root{1} = NBytes.val node{2} /\
  i{1} = W32.zero /\
  sub ots_addr{1} 0 4 = sub address{2} 0 4 /\
  sub ltree_addr{1} 0 3 = sub address{2} 0 3 /\
  sub node_addr{1} 0 3 = sub address{2} 0 3 /\
  
  valid_idx (EncodeSignature (load_sig_mem Glob.mem{1} ptr_sm)).`sig_idx /\
  s{2} = EncodeSignature (load_sig_mem Glob.mem{1} ptr_sm) /\

  to_uint sm_offset{1} = 35 + j{2} * XMSS_REDUCED_SIG_BYTES /\

  to_list root{1} = NBytes.val node{2}
); last first.

(* ======================================================================================= *)
(* A prova do ciclo while comeca aqui                                                      *)
(* ======================================================================================= *)

sp.

seq 0 0 : (#pre /\ #post); first by auto => /> &1 &2 *; smt(@W64 pow2_64).  
 
wp.

while (
  1 <= j{2} <= d /\
  to_uint i{1} = j{2} /\

  ={idx_leaf} /\
  to_uint idx{1} = to_uint idx_tree{2} /\

    to_list pub_root{1} = NBytes.val root{2} /\
    to_list pub_root{1} = sub pk{1} 0 n /\
    to_list pub_seed{1} = NBytes.val seed{2} /\
    to_list pub_seed{1} = sub pk{1} n n /\


  ots_addr{1}.[3] = W32.zero /\
  ltree_addr{1}.[3] = W32.one /\
  node_addr{1}.[3] = (of_int 2)%W32 /\

  sub ots_addr{1} 0 3 = sub address{2} 0 3 /\
  sub ltree_addr{1} 0 3 = sub address{2} 0 3 /\
  sub node_addr{1} 0 3 = sub address{2} 0 3 /\

  valid_idx (EncodeSignature (load_sig_mem Glob.mem{1} ptr_sm)).`sig_idx /\
  s{2} = EncodeSignature (load_sig_mem Glob.mem{1} ptr_sm) /\

  sm_ptr{1} = ptr_sm /\
 
    0 <= to_uint ptr_sm + to_uint sm_len < 18446744073709551615 /\
    0 <= to_uint ptr_sm < 18446744073709551615 /\
    0 <= to_uint sm_len - XMSS_SIG_BYTES  < 18446744073709551615 /\
    to_uint sm_len < XMSS_SIG_BYTES /\


  to_uint sm_offset{1} = 35 + j{2} * XMSS_REDUCED_SIG_BYTES /\

  #post
); last by auto => /> /#. 

wp; conseq />.
seq 2 1 : #pre; first by auto => /> &1 &2 *; rewrite andwC h_val d_val /(`<<`) /=; congr; smt(@W32 pow2_32).

seq 1 1 : #pre.
- by auto => /> &1 &2 *; rewrite!to_uint_shr 2:/# !of_uintK 1:/# /= h_val d_val /#. 

seq 0 1 : (#pre /\ (sig_ots{2}, auth{2}) = nth witness s{2}.`r_sigs j{2}); first by auto => /> /#.

seq 3 1 : #pre.
- inline {1}; auto => /> &1 &2 *; do split; apply (eq_from_nth witness); rewrite !size_sub // => k?; rewrite !nth_sub // !get_setE //=; smt(sub_k).

seq 3 1 : #pre.
- inline {1}; auto => /> *; rewrite /set_tree_addr; do split; apply (eq_from_nth witness); rewrite !size_sub // => i?; rewrite !nth_sub // !get_setE //=.
   + case (i = 1) => [-> /= | ?].
       * rewrite to_uintEq to_uint_truncateu32 of_uintK // !to_uint_shr !of_uintK /#.
     case (i = 2) => ?; last by smt(sub_k).
       * rewrite to_uintEq to_uint_truncateu32 of_uintK /#.
   + case (i = 1) => [-> /= | ?].
       * rewrite to_uintEq to_uint_truncateu32 of_uintK // !to_uint_shr !of_uintK /#.
     case (i = 2) => ?; last by smt(sub_k).
       * rewrite to_uintEq to_uint_truncateu32 of_uintK /#.
   + case (i = 1) => [-> /= | ?].
       * rewrite to_uintEq to_uint_truncateu32 of_uintK // !to_uint_shr !of_uintK /#.
     case (i = 2) => ?; last by smt(sub_k).
       * rewrite to_uintEq to_uint_truncateu32 of_uintK /#.

inline {2} 1.

conseq />.
   
seq 1 8 : (
  #pre /\

   idx_sig0{2} = idx_leaf{2} /\
   sig_ots0{2} = sig_ots{2} /\
   auth0{2} = auth{2} /\
   M{2} = _M'{2} /\
   _seed{2} = node{2} /\
  
   sub ots_addr{1} 0 4 = sub address0{2} 0 4 /\
   sub ltree_addr{1} 0 3 = sub address0{2} 0 3 /\
   sub node_addr{1} 0 3 = sub address0{2} 0 3
); first by inline {1}; auto => /> *; do split; apply (eq_from_nth witness); rewrite !size_sub // => i?; rewrite !nth_sub // !get_setE //; smt(sub_k).

seq 3 0 : (
   #pre /\ 
   sig_ots0{2} = EncodeWotsSignature (load_sig Glob.mem{1} t64{1})
).
- auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 *.
  have ->: sig_ots{2} = (nth witness (EncodeSignature (load_sig_mem Glob.mem{1} ptr_sm)).`r_sigs (to_uint i{1})).`1 by smt().
  rewrite /EncodeSignature => />.
  rewrite /XMSS_INDEX_BYTES /XMSS_N (nth_map witness); first by rewrite size_chunk 1:/# size_sub_list size_load_sig /#.
  rewrite size_load_sig /XMSS_SIG_BYTES /=.
  rewrite nth_chunk 1:/# ?size_sub_list ?size_load_sig 1,2:/#.
  rewrite /EncodeReducedSignature => />.      
  apply len_n_bytes_eq; apply (eq_from_nth witness); rewrite !LenNBytes.valP // => j?.
  rewrite /EncodeWotsSignatureList /EncodeWotsSignature !LenNBytes.insubdK; 1,2: by rewrite /P size_map size_chunk 1:/# ?size_sub_list ?size_to_list /#.
  congr; congr; congr.
  apply (eq_from_nth witness); first by rewrite size_to_list size_sub_list /#.
  rewrite size_sub_list 1:/# => k?.
  rewrite nth_sub_list // get_to_list nth_take 1,2:/# nth_drop 1,2:/# /=.
  rewrite nth_sub_list 1:/# !nth_load_buf 1:/# /load_sig initiE 1:/# /= /loadW8.
  congr.
  rewrite to_uintD H22 (: to_uint i{1} = 1) 1:/# /=.
  smt(@W64 pow2_64).

seq 1 1 : (
  #pre /\
  wots_pk{1} = DecodeWotsPk pk_ots{2}
). 
- wp; exists * root{1}, pub_seed{1}, ots_addr{1}, address0{2}; elim * => P1 P2 P3 P4; call (pk_from_sig_correct P1 P2 P3 P4); last by auto => /> &1 &2 /#.
(do split; 3: by rewrite /log_w (: w = XMSS_WOTS_W) 1:/# /XMSS_WOTS_W /XMSS_WOTS_LOG_W  log2_16 from_int_ceil) => /#.

seq 0 0 : (
     #{/~to_uint t64{1} = to_uint sm_ptr{1} + 35}
     {/~sig_ots0{2} = EncodeWotsSignature (load_sig Glob.mem{1} t64{1})}pre /\
     sig_ots0{2} = EncodeWotsSignature (load_sig Glob.mem{1} (sm_ptr{1} + W64.of_int 35))
); first by auto => /> *; do congr; smt(@W64 pow2_64).

seq 3 0 : (#{/~to_uint sm_offset{1} = 35}pre /\ to_uint sm_offset{1} = 2179); first by auto => /> *; smt(@W64).

seq 1 2 : (
   #{/~sub ots_addr{1} 0 4 = sub address0{2} 0 4}pre /\
   sub ltree_addr{1} 0 5 = sub address0{2} 0 5
).
- inline {1}; auto => /> *; do split; apply (eq_from_nth witness); rewrite !size_sub // => i?; rewrite !nth_sub //= !get_setE //; smt(sub_k).

wp; conseq />.

seq 1 1 : (#pre /\ to_list leaf{1} = NBytes.val nodes0{2}).
- exists * wots_pk{1}, pub_seed{1}, ltree_addr{1}, address0{2}.
  elim * => P0 P1 P2 P3.
  call (ltree_correct P0 P1 P2 P3) => [/#|]. 
  auto => /> &1 &2 *; smt(@NBytes).

seq 0 2 : (#{/~sub ltree_addr{1} 0 5 = sub address0{2} 0 5}pre /\ sub node_addr{1} 0 5 = sub address0{2} 0 5).
- inline {1}; auto => /> *; do split; apply (eq_from_nth witness); rewrite !size_sub // => i?; rewrite !nth_sub //= !get_setE //; smt(sub_k).
 
seq 4 0 : (#pre /\ t64{1} = sm_ptr{1} + sm_offset{1}); first by auto.

outline {2} [1-2] by { nodes0 <@ ComputeRoot.compute_root (_seed, nodes0, address0, idx_sig0, auth0); }; 
 
conseq />.
exists * leaf{1}, pub_seed{1}, idx_leaf{1}, t64{1}, node_addr{1}, address0{2}.
elim * => P0 P1 P2 P3 P4 P5.
call (compute_root_equiv P0 P1 P2 P3 P4 P5) => [/# |].
skip => /> &1 &2.
move => H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34.
do split.
- smt(@NBytes).
- smt(@NBytes).
- have ->: auth{2} = (nth witness (EncodeSignature (load_sig_mem Glob.mem{1} ptr_sm)).`r_sigs (to_uint i{1})).`2 by smt().
  rewrite /EncodeSignature => />.
  rewrite (nth_map witness); first by rewrite size_chunk 1:/# size_sub_list size_load_sig /#.
  rewrite nth_chunk 1:/# ?size_sub_list ?size_load_sig 1,2:/#.
  rewrite /EncodeReducedSignature => />.
  congr.
  apply (eq_from_nth witness); first by rewrite size_sub_list 1:/# size_load_buf /#.
  rewrite size_sub_list 1:/# => k?.
  rewrite nth_sub_list // nth_take 1,2:/# nth_drop 1,2:/# nth_sub_list /#.
- smt(@W64 pow2_64).
- smt(@W64 pow2_64).
- smt(@W64 pow2_64).
- smt(@W64 pow2_64).
- smt().
- smt().
- smt().
- move => H36 H37 H38 H39 H40 H41 H42 H43 H44 H45.
  move => resultL resultR Hr0 Hr1.
  rewrite to_uintD; do split; 1..3,5..8: by smt().
  smt(sub_k).

(* ------------------------------------------------------------------------------- *)
(*                                                                                 *)
(* ------------------------------------------------------------------------------- *)
 
swap {2} 1 1.
seq 3 1 : (#pre /\ i{1} = W32.zero /\ ={idx_leaf}).
- auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34.
  rewrite andwC; congr; first by smt(@W32 pow2_32).
  by rewrite h_val d_val /(`<<`).

seq 1 1 : (
  #{/~to_uint idx{1} = to_uint idx_sig{2}}pre /\
  to_uint idx{1} = to_uint idx_tree{2}
).
- by auto => /> &1 &2 *; rewrite h_val d_val /= to_uint_shr ?of_uintK // /#.
  
seq 0 1 : (#pre /\ (sig_ots{2}, auth{2}) = nth witness s{2}.`r_sigs 0); first by auto => /> /#.

seq 3 1 : #pre; first by inline {1}; auto => /> *; smt(sub_k).

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
   sub node_addr{1} 0 3 = sub address{2} 0 3
); first by  inline {1}; auto => /> *; rewrite /set_tree_addr; do split; apply (eq_from_nth witness); rewrite !size_sub // => i?; rewrite !nth_sub // !get_setE //; smt(sub_k).

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
); first by auto => /> *; rewrite to_uintD /#.

seq 1 1 : (
  #pre /\
  wots_pk{1} = DecodeWotsPk pk_ots{2}
).
- wp; exists * root{1}, pub_seed{1}, ots_addr{1}, address0{2}; elim * => P1 P2 P3 P4; call (pk_from_sig_correct P1 P2 P3 P4); last by auto => /> &1 &2 /#.
(do split; 3: by rewrite /log_w (: w = XMSS_WOTS_W) 1:/# /XMSS_WOTS_W /XMSS_WOTS_LOG_W  log2_16 from_int_ceil) => /#.

seq 0 0 : (
     #{/~to_uint t64{1} = to_uint sm_ptr{1} + 35}
     {/~sig_ots0{2} = EncodeWotsSignature (load_sig Glob.mem{1} t64{1})}pre /\
     sig_ots0{2} = EncodeWotsSignature (load_sig Glob.mem{1} (sm_ptr{1} + W64.of_int 35))
); first by auto => /> *; do congr; smt(@W64 pow2_64).
 
seq 3 0 : (#{/~to_uint sm_offset{1} = 35}pre /\ to_uint sm_offset{1} = 2179); first by auto => /> *; smt(@W64).

seq 1 2 : (
   #{/~sub ots_addr{1} 0 4 = sub address0{2} 0 4}pre /\
   sub ltree_addr{1} 0 5 = sub address0{2} 0 5
).
- inline {1}; auto => /> *; do split; apply (eq_from_nth witness); rewrite !size_sub // => i?; rewrite !nth_sub //= !get_setE //; smt(sub_k).

wp; conseq />.
    
seq 1 1 : (#pre /\ to_list leaf{1} = NBytes.val nodes0{2}).
- exists * wots_pk{1}, pub_seed{1}, ltree_addr{1}, address0{2}.
  elim * => P0 P1 P2 P3.
  call (ltree_correct P0 P1 P2 P3) => [/#|]. 
  auto => /> &1 &2 21? -> ? H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18; split => [| /#].
  rewrite -enc_dec_wots_pk 1:/# //= NBytes.valKd /#.

 
seq 0 2 : (#{/~sub ltree_addr{1} 0 5 = sub address0{2} 0 5}pre /\ sub node_addr{1} 0 5 = sub address0{2} 0 5).
- inline {1}; auto => /> *; do split; apply (eq_from_nth witness); rewrite !size_sub // => i?; rewrite !nth_sub //= !get_setE //; smt(sub_k).
 
seq 4 0 : (#pre /\ t64{1} = sm_ptr{1} + sm_offset{1}); first by auto.

outline {2} [1-2] by { nodes0 <@ ComputeRoot.compute_root (_seed, nodes0, address0, idx_sig0, auth0); }.

conseq />.
exists * leaf{1}, pub_seed{1}, idx_leaf{1}, t64{1}, node_addr{1}, address0{2}.
elim * => P0 P1 P2 P3 P4 P5.
call (compute_root_equiv P0 P1 P2 P3 P4 P5) => [/# |].
skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 -> H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35
                 H36 H37 H38 H39 H40 -> H41.
rewrite !to_uintD; (do split; 4..11: by smt()); 1,2: by rewrite NBytes.valKd.
- have ->: auth{2} = (nth witness (EncodeSignature (load_sig_mem Glob.mem{1} ptr_sm)).`r_sigs (to_uint i{1})).`2 by smt().
  rewrite /EncodeSignature => />.
  rewrite (nth_map witness); first by rewrite size_chunk 1:/# size_sub_list size_load_sig /#.
  rewrite nth_chunk 1:/# ?size_sub_list ?size_load_sig 1,2:/#.
  rewrite /EncodeReducedSignature => />.
  congr.
  apply (eq_from_nth witness); first by rewrite size_sub_list 1:/# size_load_buf /#.
  rewrite size_sub_list 1:/# => k?.
  rewrite nth_sub_list // nth_take 1,2:/# nth_drop 1,2:/# nth_sub_list /#.
qed.
