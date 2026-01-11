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

import W8.
(*---*) import W8u8.Pack.
(*---*) import BitEncoding.BitChunking.

require import Array4 Array8 Array32 Array64 Array2144.
require import WArray64 WArray32.

op load_sig_mem (mem : global_mem_t) (sm_ptr : W64.t) : W8.t list =
  load_buf mem sm_ptr XMSS_SIG_BYTES.

lemma size_load_sig (mem : global_mem_t) (ptr : W64.t) :
    size (load_sig_mem mem ptr) = XMSS_SIG_BYTES.
proof.
rewrite /load_sig; by apply size_load_buf.
qed.

pred valid_idx (idx : W32.t) = 0 <= to_uint idx < 2^XMSS_FULL_HEIGHT.

lemma to_uintEq (w0 w1 : W32.t) :
    w0 = w1 <=> to_uint w0 = to_uint w1.
proof.
split; [by move => -> | smt(@W32)].
qed.

pred even (x : W32.t) = to_uint x %% 2 = 0.
pred odd (x : W32.t) = !even x.

lemma even_div :
    forall (w : W32.t), even w => to_uint (w `>>` W8.one) = to_uint w %/ 2.
proof.
move => *; by rewrite to_uint_shr.
qed.

lemma odd_div :
    forall (w :W32.t), odd w => to_uint (w `>>` W8.one) = (to_uint w - 1) %/ 2.
proof.
move => ??.
rewrite to_uint_shr //= /#.
qed.

lemma foo (x : W32.t) :
    to_uint (x `>>` W8.one) = floor ((to_uint x)%r / 2%r).
proof.
by case: (even x) => [Heven | Hodd]; [rewrite even_div // | rewrite odd_div //]; smt(@Real).
qed.

lemma foo_i (x : W32.t) (shift_amount : W8.t):
    (0 <= to_uint shift_amount < 32) =>
    to_uint (x `>>` shift_amount) = floor ((to_uint x)%r / (2 ^ (to_uint shift_amount))%r).
proof.
move => *.
rewrite to_uint_shr 1:/# /=.
case: (to_uint shift_amount = 0)  => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 1)  => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 2)  => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 3)  => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 4)  => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 5)  => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 6)  => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 7)  => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 8)  => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 9)  => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 10) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 11) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 12) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 13) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 14) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 15) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 16) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 17) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 18) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 19) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 20) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 21) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 22) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 23) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 24) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 25) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 26) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 27) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 28) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 29) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 30) => [-> /= | ?]; first by smt(@Real).
case: (to_uint shift_amount = 31) => [-> /= | /#]; by smt(@Real).
qed.

lemma odd_g0 :
    forall (w : W32.t), 0 <= to_uint w  => odd w => 1 <= to_uint w by smt(@IntDiv).

module ComputeRoot = {
proc compute_root (_seed nodes0 : nbytes, address0 : adrs, idx_sig0 : W32.t, auth0 : auth_path) : nbytes = {
        var k : int;
        var index : int;
        var auth_k, nodes1 : nbytes;

        k <- 0;
        while (k < h %/ d) {                              
            address0 <- set_tree_height address0 k;
            if (floor ((to_uint idx_sig0)%r / (2 ^ k)%r) %% 2 = 0) {                               
                index <- get_tree_index address0;         
                address0 <- set_tree_index address0 (index %/ 2);
                auth_k <- nth witness (AuthPath.val auth0) k;
                nodes1 <@ Hash.rand_hash(nodes0, auth_k, _seed, address0);
            } else {                                   
                index <- get_tree_index address0;         
                address0 <- set_tree_index address0 ((index - 1) %/ 2);
                auth_k <- nth witness (AuthPath.val auth0) k;
                nodes1 <@ Hash.rand_hash(auth_k, nodes0, _seed,  address0);
            }                                          
            nodes0 <- nodes1;
            k <- k + 1;                          
        }                                    
        return nodes0;
    }        
}.

op XMSS_AUTH_PATH_BYTES : int = XMSS_REDUCED_SIG_BYTES - XMSS_WOTS_SIG_BYTES.

lemma compute_root_equiv (_l _pub_seed : W8.t Array32.t, _idx : W32.t, path_ptr : W64.t, a1 a2 : W32.t Array8.t) :
    n = XMSS_N /\
    d = XMSS_D /\
    h = XMSS_FULL_HEIGHT /\
    padding_len = XMSS_PADDING_LEN /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    padding_len = XMSS_PADDING_LEN  =>
    equiv [
    M(Syscall).__new_compute_root_ ~  ComputeRoot.compute_root :
      arg{1}.`2 = _l /\ (* leaf *)
      arg{1}.`3 = _idx /\
      arg{1}.`4 = path_ptr /\
      arg{1}.`5 = _pub_seed /\
      arg{1}.`6 = a1 /\

      arg{2}.`1 = NBytes.insubd (to_list _pub_seed) /\
      arg{2}.`2 = NBytes.insubd (to_list _l) /\
      arg{2}.`3 = a2 /\
      arg{2}.`4 = _idx /\
      arg{2}.`5 = EncodeAuthPath (load_buf Glob.mem{1} path_ptr XMSS_AUTH_PATH_BYTES) /\

      0 <= to_uint path_ptr + XMSS_AUTH_PATH_BYTES  < W64.max_uint /\
      0 <= to_uint path_ptr < W64.max_uint /\

      sub a1 0 5 = sub a2 0 5 /\
      get_tree_index a2 = to_uint _idx /\
      0 <= to_uint _idx < 2^XMSS_FULL_HEIGHT
      ==>
      to_list res{1}.`1 = NBytes.val res{2} /\
      sub res{1}.`2 0 5 = sub a1 0 5 
    ].
proof.
rewrite /XMSS_N /XMSS_D /XMSS_FULL_HEIGHT => [#] n_val d_val h_val*.
proc => /=.  
wp; seq 6 0 : #pre; 1:auto; inline {1} 1; wp.   
seq 6 0 : (
  leaf0{1} = _l /\
  addr0{1} = a1 /\
  _seed{2} = (NBytes.insubd (to_list pub_seed0{1}))%NBytes /\
  address0{2} = a2 /\
  idx_sig0{2} = leaf_idx0{1} /\
  auth0{2} = EncodeAuthPath (load_buf Glob.mem{1} auth_path_ptr0{1} XMSS_AUTH_PATH_BYTES) /\
  sub a1 0 5 = sub a2 0 5 /\
  0 <= to_uint auth_path_ptr0{1} + XMSS_AUTH_PATH_BYTES  < W64.max_uint /\
  0 <= to_uint auth_path_ptr0{1} < W64.max_uint  /\
  auth_path_ptr0{1} = path_ptr /\
  0 <= to_uint path_ptr + XMSS_AUTH_PATH_BYTES < W64.max_uint /\
  0 <= to_uint path_ptr < W64.max_uint /\
  get_tree_index a2 = to_uint _idx /\
  0 <= to_uint _idx < 2^XMSS_FULL_HEIGHT /\
  idx_sig0{2} = _idx /\
  nodes0{2} = (NBytes.insubd (to_list leaf0{1}))%NBytes
); first by auto.

inline {1} 1.
 
seq 8 0 : (
  leaf1{1} = _l /\
  addr1{1} = a1 /\
  _seed{2} = (NBytes.insubd (to_list pub_seed1{1}))%NBytes /\
  address0{2} = a2 /\
  idx_sig0{2} = leaf_idx1{1} /\
  auth0{2} =
  EncodeAuthPath (load_buf Glob.mem{1} _auth_path_ptr{1} XMSS_AUTH_PATH_BYTES) /\
  sub a1 0 5 = sub a2 0 5 /\
  0 <= to_uint _auth_path_ptr{1} + XMSS_AUTH_PATH_BYTES  < W64.max_uint /\
  0 <= to_uint _auth_path_ptr{1}  < W64.max_uint /\
  0 <= to_uint path_ptr + XMSS_AUTH_PATH_BYTES < W64.max_uint /\
  0 <= to_uint path_ptr < W64.max_uint /\
  _auth_path_ptr{1} = path_ptr /\
  get_tree_index a2 = to_uint _idx /\
  0 <= to_uint _idx < 2^XMSS_FULL_HEIGHT /\
  idx_sig0{2} = _idx /\
  nodes0{2} = (NBytes.insubd (to_list leaf1{1}))%NBytes
); first by auto.

wp.
 
while (
  sub addr1{1} 0 5 = sub a1 0 5 /\
  sub addr1{1} 0 5 = sub address0{2} 0 5 /\
  _seed{2} = NBytes.insubd (to_list pub_seed1{1}) /\
  auth0{2} = EncodeAuthPath (load_buf Glob.mem{1} _auth_path_ptr{1} XMSS_AUTH_PATH_BYTES) /\

  0 <= to_uint _auth_path_ptr{1} + XMSS_AUTH_PATH_BYTES  < W64.max_uint /\
  0 <= to_uint _auth_path_ptr{1}  < W64.max_uint /\
  0 <= to_uint path_ptr + XMSS_AUTH_PATH_BYTES < W64.max_uint /\
  0 <= to_uint path_ptr < W64.max_uint /\

  _auth_path_ptr{1} = path_ptr /\

  0 <= to_uint _idx < 2^XMSS_FULL_HEIGHT /\
  idx_sig0{2} = _idx /\
  idx_sig0{2} = leaf_idx1{1} /\
  get_tree_index address0{2} = to_uint (idx_sig0{2} `>>` (of_int k{2})%W8) /\

  ((k{2} = 0) => nodes0{2} = (NBytes.insubd (to_list leaf1{1}))%NBytes) /\

  to_uint k{1} = k{2} /\
  0 <= to_uint k{1} <= h %/ d /\
  ((0 < to_uint k{1} < h %/d) => to_list node{1} = NBytes.val nodes0{2}) /\
  ((to_uint k{1} = h %/d) => to_list root1{1} = NBytes.val nodes0{2})
); last by auto => /> &1 H0 H1 H2 H3 H4 H5 H6 H7 H8 -> H9 H10; rewrite to_uint_shr // /#.
 
seq 2 1 : (
    #{/~sub addr1{1} 0 5 = sub address0{2} 0 5}pre /\
    sub addr1{1} 0 6 = sub address0{2} 0 6 /\
    to_uint tree_height{1} = to_uint k{1}
); first by inline {1}; auto => /> *; rewrite to_uint_truncateu32; do split; try (apply (eq_from_nth witness); rewrite !size_sub // => j?; rewrite !nth_sub // !get_setE //=; smt(sub_k)) => /#.
  
wp; conseq />.
 
if{2}.

(* ------------------------------------------------------------------------------- *)
(* EVEN CASE                                                                        *)
(* ------------------------------------------------------------------------------- *)
 
seq 6 2 : (
  #{/~sub addr1{1} 0 6 = sub address0{2} 0 6}
   {/~get_tree_index address0{2} = to_uint (idx_sig0{2} `>>` (of_int k{2})%W8)}pre /\ 
   sub addr1{1} 0 7 = sub address0{2} 0 7 /\
   get_tree_index address0{2} = to_uint (idx_sig0{2} `>>` (of_int (k{2} + 1))%W8)
).
- inline {1}; auto => /> &1 &2.
  rewrite /XMSS_FULL_HEIGHT ultE /= => H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 *; do split; 
  try (apply (eq_from_nth witness); rewrite !size_sub // => j?; rewrite !nth_sub // !get_setE //=); last first.
   * rewrite H11 /get_tree_index /set_tree_index get_setE //= !to_uint_shr !of_uintK 1,2:/# /=.
     case: (to_uint k{1} = 0) => [-> /# | ?]; case: (to_uint k{1} = 1) => [-> /# | ?]; case: (to_uint k{1} = 2) => [-> /# | ?]; 
     case: (to_uint k{1} = 3) => [-> /# | ?]; case: (to_uint k{1} = 4) => [-> /# | ?]; case: (to_uint k{1} = 5) => [-> /# | ?]; 
     case: (to_uint k{1} = 6) => [-> /# | ?]; case: (to_uint k{1} = 7) => [-> /# | ?]; case: (to_uint k{1} = 8) => [-> /# | ?]; 
     case: (to_uint k{1} = 9) => [-> /# | /#].
   * case: (j = 6) => H; last by smt(sub_k).
     rewrite wordP => i?.     
     rewrite !get_to_uint (: 0 <= i <  32) //= to_uint_shr (: 31 = 2^5 - 1) 1..3:/# and_mod //= to_uint_truncateu8 of_uintK to_uintD /=.
     rewrite H20 /#.
   * case: (j = 6) => H; last by smt(sub_k).
     rewrite H11 (: 31 = 2^5 - 1) 1:/# and_mod //=. 
     rewrite !shr_div !of_uintK /= wordP => i?.  
     rewrite !get_to_uint (: 0 <= i <  32) //= of_uintK to_uint_shr to_uint_truncateu8 to_uintD of_uintK /= 1:/# H20.  
     case: (to_uint k{1} = 0) => [-> /# | ?]; case: (to_uint k{1} = 1) => [-> /# | ?]; case: (to_uint k{1} = 2) => [-> /# | ?]; 
     case: (to_uint k{1} = 3) => [-> /# | ?].
     case: (to_uint k{1} = 4) => [-> |?]; first by smt(@IntDiv).
     case: (to_uint k{1} = 5) => [-> | ?]; first  by smt(@IntDiv).
     case: (to_uint k{1} = 6) => [-> | ?]; first  by smt(@IntDiv). 
     case: (to_uint k{1} = 7) => [-> | ?]; first  by smt(@IntDiv).
     case: (to_uint k{1} = 8) => [-> | ?]; first  by smt(@IntDiv).
     case: (to_uint k{1} = 9) => [-> | /#]; smt(@IntDiv).

rcondt{1} 5.
- auto => /> &hr.
  rewrite /XMSS_FULL_HEIGHT /= => H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20*.
  rewrite and_1_mod_2_W32_2; last first.
     * rewrite -H19 foo_i of_uintK (: 31 = 2^5 - 1) 1,3:/# and_mod 1,3:/# H18 of_uintK /#.
  rewrite shr_div !of_uintK /= ; smt(@IntDiv).
  
seq 4 1 : (#pre /\ auth_k{2} = nth witness (AuthPath.val auth0{2}) k{2}); first by auto.
   
seq 1 0 : (#pre /\ sub thash_in{1} 0 n = NBytes.val nodes0{2}).
- if{1}; conseq />; auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18.
  apply (eq_from_nth witness); rewrite ?NBytes.valP ?n_val size_sub // => i?; 
  rewrite nth_sub // initiE 1:/# /= ifT 1:/# initiE // /get8 /init64 initiE //= /copy_64 /= initiE 1:/# /= get64E bits8E wordP => w?; 
  rewrite initiE //= pack8E /= initiE 1:/# /= initiE 1:/# /= /init8 initiE 1:/#.
     * rewrite H11 NBytes.insubdK /P ?size_to_list 1:/# get_to_list /#.
     * move => H19 H20 H21 H22 *.
       have E: to_uint k{1} <> 0 by smt(@W64).
       rewrite ultE of_uintK /= in H16; rewrite -H14 1:/#. 
       apply (eq_from_nth witness); rewrite size_sub n_val // ?size_to_list // => i?.
       rewrite nth_sub //= initiE 1:/# //= ifT 1:/# initiE //= /get8 initiE //= bits8E initiE 1:/# wordP => j?.
       rewrite initiE //= get64E pack8E initiE 1:/# /= initiE 1:/# /= initiE 1:/# /#.

rcondt {1} 2; 1:auto.
  
seq 6 0 : (#pre /\ to_list thash_in{1} = NBytes.val nodes0{2} ++ NBytes.val auth_k{2}).

- wp; sp; conseq />; ecall {1} (p_memcpy_ptr_correct _ptr{1}); auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22  *.
  do split; 1..3: by rewrite to_uintD to_uint_shl of_uintK //= /#.
  move => ???; split.
    + apply (eq_from_nth witness); rewrite ?NBytes.valP size_sub ?n_val // => i?. 
      by rewrite nth_sub // initiE 1:/# /= ifF 1:/# -H22 nth_sub //= n_val.
    + apply (eq_from_nth witness); rewrite size_to_list ?size_cat ?NBytes.valP ?n_val // => i?.
      rewrite get_to_list initiE 1:/# /=.
      case (0 <= i < 32) => [Hfst | Hsnd].
        * rewrite ifF 1:/#. 
          have ->: thash_in{1}.[i] = nth witness (sub thash_in{1} 0 n) i by rewrite nth_sub /#.
          by rewrite H22 nth_cat NBytes.valP ifT 1:/# /EncodeAuthPath.
        * rewrite ifT 1:/# initiE 1:/# /= nth_cat NBytes.valP ifF 1:/# /EncodeAuthPath AuthPath.insubdK.
            - rewrite /P size_map size_chunk 1:/# size_load_buf /#.
          rewrite (nth_map witness); first by rewrite size_chunk 1:/# size_load_buf /#.
          rewrite NBytes.insubdK; first by rewrite /P nth_chunk 1:/# ?size_load_buf 1,2:/# size_take 1:/# size_drop 1:/# size_load_buf /#.
          rewrite nth_chunk 1:/# ?size_load_buf 1,2:/# nth_take 1,2:/# nth_drop 1,2:/# nth_load_buf 1:/# /loadW8.
          congr; rewrite to_uintD to_uint_shl of_uintK /#.
 
if{1}.

- do 2! (inline {1} 1; wp; sp). 
  exists * nodes0{2}, auth_k{2}, pub_seed3{1}, addr3{1}, address0{2}; elim * => P0 P1 P2 P3 P4; (call (rand_hash_results P0 P1 P2 P3 P4) => [/# |]).
  auto => /> &1 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20*.
  do split.
    * rewrite tP => i?.
      rewrite -get_to_list H20 /merge_nbytes_to_array initiE //=.
      case (0 <= i < 32) => ?; rewrite nth_cat NBytes.valP /#.
    * smt(sub_k).
    * move => *; (do split; 3..: by smt()); apply (eq_from_nth witness); rewrite !size_sub // => i?; rewrite !nth_sub //; smt(sub_k). 
  
- do 2! (inline {1} 1; wp; sp) ; exists * nodes0{2}, auth_k{2}, pub_seed3{1}, addr3{1}, address0{2}; elim * => P0 P1 P2 P3 P4; (call (rand_hash_results P0 P1 P2 P3 P4) => [/# |]).
  auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 *.
  do split.
    * rewrite tP => i?.
      rewrite -get_to_list H22 /merge_nbytes_to_array initiE //=.
      case (0 <= i < 32) => ?; rewrite nth_cat NBytes.valP /#.
    * smt(sub_k). 
    * move => H24 H25 resL resR H26 H27 ; rewrite ultE to_uintD of_uintK /=; do split; 3..6,8,9: by smt().
        - apply (eq_from_nth witness); rewrite !size_sub // => i?; rewrite !nth_sub //; smt(sub_k). 
        - apply (eq_from_nth witness); rewrite !size_sub // => i?; rewrite !nth_sub //; smt(sub_k). 
        - smt(@W64 pow2_64).

(* ------------------------------------------------------------------------------- *)
(* ODD CASE                                                                        *)
(* ------------------------------------------------------------------------------- *)

seq 6 2 : (
  #{/~sub addr1{1} 0 6 = sub address0{2} 0 6}
   {/~get_tree_index address0{2} = to_uint (idx_sig0{2} `>>` (of_int k{2})%W8)}pre /\ 
   sub addr1{1} 0 7 = sub address0{2} 0 7 /\
   get_tree_index address0{2} = to_uint (idx_sig0{2} `>>` (of_int (k{2} + 1))%W8)
).

- inline {1}; auto => /> &1 &2.
  rewrite /XMSS_FULL_HEIGHT ultE of_uintK /= => H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21  *; do split; try (apply (eq_from_nth witness); rewrite !size_sub // => j?; rewrite !nth_sub // !get_setE //=).
   * rewrite ifF 1:/#; smt(sub_k).
   * case: (j = 6) => ?; last by smt(sub_k).
     rewrite H11.
     rewrite !shr_div !of_uintK /= wordP => i?. 
     rewrite !get_to_uint (: 0 <= i <  32) //=. 
     have ->: _idx `>>` truncateu8 ((tree_height{1} + W32.one) `&` W32.of_int 31) = _idx `>>` (of_int (to_uint k{1}))%W8 `>>` W8.one.
        -  rewrite to_uintEq !shr_div /=.
           rewrite (: 31 = 2^5 - 1) 1:/# and_mod //= to_uint_truncateu8 of_uintK to_uintD H20 /=. 
           case: (to_uint k{1} = 0) => [-> /# | ?]; case: (to_uint k{1} = 1) => [-> /# | ?]; case: (to_uint k{1} = 2) => [-> /# | ?]; 
           case: (to_uint k{1} = 3) => [-> /# | ?]; case: (to_uint k{1} = 4) => [-> /# | ?]; case: (to_uint k{1} = 5) => [-> /# | ?]; 
           case: (to_uint k{1} = 6) => [-> /# | ?]; case: (to_uint k{1} = 7) => [-> /# | ?]; case: (to_uint k{1} = 8) => [-> /# | ?]; 
           case: (to_uint k{1} = 9) => [-> /# | /#].
     rewrite odd_div; first by rewrite /odd /even foo_i of_uintK /#.
     rewrite !to_uint_shr !of_uintK 1:/# /= (: to_uint k{1} %% 256 = to_uint k{1}) 1:/#.
     have E0: odd (_idx `>>` (of_int (to_uint k{1}))%W8) by rewrite /odd /even foo_i of_uintK /#.
     have Ha : 1 <= to_uint (_idx `>>` (of_int (to_uint k{1}))%W8) by (apply odd_g0; last by assumption); rewrite to_uint_shr of_uintK 1:/# /=; smt(@IntDiv).
     rewrite to_uint_shr of_uintK 1:/# (: to_uint k{1} %% W8.modulus = to_uint k{1}) 1:/# in Ha .
     have ->: (to_uint _idx %/ 2 ^ to_uint k{1} - 1) %/ 2 %% 4294967296 = (to_uint _idx %/ 2 ^ to_uint k{1} - 1) %/ 2; last by [].
     smt(@IntDiv).

   * rewrite H11 /get_tree_index /set_tree_index get_setE //=.
     have ->: to_uint (_idx `>>` W8.of_int (to_uint k{1} + 1)) = to_uint (_idx `>>` (of_int (to_uint k{1}))%W8 `>>` W8.one).
         + rewrite !to_uint_shr 2:/# !of_uintK 1,2:/#.
           case: (to_uint k{1} = 0) => [-> /# | ?]; case: (to_uint k{1} = 1) => [-> /# | ?]; case: (to_uint k{1} = 2) => [-> /# | ?]; 
           case: (to_uint k{1} = 3) => [-> /# | ?]; case: (to_uint k{1} = 4) => [-> /# | ?]; case: (to_uint k{1} = 5) => [-> /# | ?]; 
           case: (to_uint k{1} = 6) => [-> /# | ?]; case: (to_uint k{1} = 7) => [-> /# | ?]; case: (to_uint k{1} = 8) => [-> /# | ?]; 
           case: (to_uint k{1} = 9) => [-> /# | /#].
     rewrite odd_div; first by rewrite /odd /even foo_i of_uintK /#.
     rewrite !to_uint_shr !of_uintK 1:/# /= (: to_uint k{1} %% 256 = to_uint k{1}) 1:/#.
     have E0: odd (_idx `>>` (of_int (to_uint k{1}))%W8) by rewrite /odd /even foo_i of_uintK /#.
     have Ha : 1 <= to_uint (_idx `>>` (of_int (to_uint k{1}))%W8) by (apply odd_g0; last by assumption); rewrite to_uint_shr of_uintK 1:/# /=; smt(@IntDiv).
     rewrite to_uint_shr of_uintK 1:/# (: to_uint k{1} %% W8.modulus = to_uint k{1}) 1:/# in Ha .
     have ->: (to_uint _idx %/ 2 ^ to_uint k{1} - 1) %/ 2 %% 4294967296 = (to_uint _idx %/ 2 ^ to_uint k{1} - 1) %/ 2; last by [].
     smt(@IntDiv).

rcondf{1} 5.
- auto => /> &hr.
  rewrite /XMSS_FULL_HEIGHT /= => H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20*.
  rewrite and_1_mod_2_W32 foo_i of_uintK (: 31 = 2^5 - 1) 1,3:/# and_mod //= of_uintK /#.

seq 4 1 : (#pre /\ auth_k{2} = nth witness (AuthPath.val auth0{2}) k{2}); first by auto.

seq 1 0 : (#pre /\ sub thash_in{1} n n = NBytes.val nodes0{2}).
- if{1}; conseq />; auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 *; 
  apply (eq_from_nth witness); rewrite ?NBytes.valP ?n_val size_sub // => i?; 
  rewrite nth_sub // initiE 1:/# /= ifT 1:/# initiE // /get8 /init64 initiE //= /copy_64 /= initiE 1:/# /= get64E bits8E wordP => w?; 
  rewrite initiE //= pack8E /= initiE 1:/# /= initiE 1:/# /= /init8 initiE 1:/#.
    * rewrite H11 NBytes.insubdK /P ?size_to_list 1:/# get_to_list /#.
    * rewrite -H14; first by smt(@W64 pow2_64).
      rewrite get_to_list /#.

seq 6 0 : (#pre /\ to_list thash_in{1} = NBytes.val auth_k{2} ++ NBytes.val nodes0{2}).
- wp; sp; conseq />; ecall {1} (p_memcpy_ptr_correct _ptr{1}); auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22.
  do split; 1..3: by rewrite to_uintD to_uint_shl of_uintK /#.
   move => *; do split => [/# | |].
    + apply (eq_from_nth witness); rewrite ?NBytes.valP size_sub ?n_val // => i?. 
      by rewrite nth_sub // initiE 1:/# /= ifF 1:/# -H22 nth_sub //= n_val.
    + apply (eq_from_nth witness); rewrite size_to_list ?size_cat ?NBytes.valP ?n_val // => i?.
      rewrite get_to_list initiE 1:/# /=.
      case (0 <= i < 32) => [Hfst | Hsnd]; last first.
        * have ->: thash_in{1}.[i] = nth witness (sub thash_in{1} n n) (i - n) by rewrite nth_sub /#.
          by rewrite H22 nth_cat NBytes.valP ifF 1:/# /EncodeAuthPath.
        * rewrite initiE 1:/# /= nth_cat NBytes.valP ifT 1:/# /EncodeAuthPath AuthPath.insubdK.
            - rewrite /P size_map size_chunk 1:/# size_load_buf /#.
          rewrite (nth_map witness); first by rewrite size_chunk 1:/# size_load_buf /#.
          rewrite NBytes.insubdK; first by rewrite /P nth_chunk 1:/# ?size_load_buf 1,2:/# size_take 1:/# size_drop 1:/# size_load_buf /#.
          rewrite nth_chunk 1:/# ?size_load_buf 1,2:/# nth_take 1,2:/# nth_drop 1,2:/# nth_load_buf 1:/# /loadW8.
          congr; rewrite to_uintD to_uint_shl of_uintK /#.

if{1}; do 2! (inline {1} 1; wp; sp).
- exists * auth_k{2}, nodes0{2}, pub_seed3{1}, addr3{1}, address0{2}; elim * => P0 P1 P2 P3 P4; (call (rand_hash_results P0 P1 P2 P3 P4) => [/# |]).
  auto => /> &1 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20.
  do split.
    * rewrite tP => i?.
      rewrite -get_to_list H20 /merge_nbytes_to_array initiE //=.
      case (0 <= i < 32) => ?; rewrite nth_cat NBytes.valP /#.
    * smt(sub_k).
    * move => *; (do split; 3..: by smt()); apply (eq_from_nth witness); rewrite !size_sub // => i?; rewrite !nth_sub //; smt(sub_k). 

- exists * auth_k{2}, nodes0{2}, pub_seed3{1}, addr3{1}, address0{2}; elim * => P0 P1 P2 P3 P4; (call (rand_hash_results P0 P1 P2 P3 P4) => [/# |]).
  auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22*.
  do split.
    * rewrite tP => i?.
      rewrite -get_to_list H22 /merge_nbytes_to_array initiE //=.
      case (0 <= i < 32) => ?; rewrite nth_cat NBytes.valP /#.
    * smt(sub_k).
    * move => H24 H25 resL resR H26 H27 ; rewrite ultE to_uintD of_uintK /=; do split; 3..6,8,9: by smt().
        - apply (eq_from_nth witness); rewrite !size_sub // => i?; rewrite !nth_sub //; smt(sub_k). 
        - apply (eq_from_nth witness); rewrite !size_sub // => i?; rewrite !nth_sub //; smt(sub_k). 
        - smt(@W64 pow2_64).
qed.

