pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel.

require import Array3 Array32 Array64 Array128 Array2144.
require import Array352.
require import WArray32.

require import XMSS_IMPL.
require import Utils Repr.
require import Termination.

require import Params Parameters. 

require import XMSS_MT_TreeHash.

lemma copy_nbytes_eq  (i : W8.t Array32.t) :
    phoare [M(Syscall).copy_nbytes : arg.`2 = i ==> res = i] = 1%r.
proof.
proc.
rcondt 1 => //.
auto => /> &hr.
 rewrite tP => j?.
rewrite initiE // get8_set64_directE // bits8E.
case (24 <= j < 24 + 8) => ?; rewrite wordP => k?.
     * rewrite initiE //= get64E pack8E; do  (rewrite initiE 1:/# /=); smt().
rewrite /get8 !initiE //= set64E initiE //=.
case (16 <= j < 24) => ?.
     * rewrite get64E /= bits8E /= initiE //= pack8E //=; do (rewrite initiE 1:/# /=); smt().
rewrite /get8 !initiE //= set64E initiE //=. 
case (8 <= j < 16) => ?.
     * rewrite get64E /= bits8E /= initiE //= pack8E //=; do (rewrite initiE 1:/# /=); smt().
rewrite /get8 !initiE //= set64E initiE //= ifT 1:/#.
rewrite get64E /= bits8E /= initiE //= pack8E //=; do (rewrite initiE 1:/# /=); smt().
qed.

import W8u8.

lemma copy_nbytes_from_ptr_ll:  islossless M(Syscall).copy_nbytes_from_ptr.
proof.
proc.
rcondt 1; first by auto. 
unroll 2; unroll 3; unroll 4; unroll 5.
rcondf 6; first by auto.
rcondt 5; first by auto.
rcondt 4; first by auto.
rcondt 3; first by auto.
rcondt 2; auto.
qed.

lemma copy_nbytes_from_ptr_post (mem : global_mem_t) (o p : W64.t) (input : W8.t Array32.t) :
hoare [
    M(Syscall).copy_nbytes_from_ptr :
        Glob.mem = mem /\
        (* valid ptr *)
        0 <= to_uint p + to_uint o + 32 < W64.max_uint /\
        arg = (p, o, input) 
        ==>
        res = p /\
        (load_buf Glob.mem (p + o) 32 = to_list input) /\
          (* O resto da memoria mantem se inalterada *)
          forall (k : int), 0 <= k < W64.max_uint =>
             !(to_uint p + to_uint o <= k < to_uint p + to_uint o + 32) => 
                Glob.mem.[k] = mem.[k] 
	].
proof.
proc => /=.
rcondt 1; first by auto. 
unroll 2; unroll 3; unroll 4; unroll 5.
rcondf 6; first by auto.
rcondt 5; first by auto.
rcondt 4; first by auto.
rcondt 3; first by auto.
rcondt 2; first by auto.

auto => /> H0 H1.

have E0: to_uint (p + o) = to_uint p + to_uint o by smt(@W64 pow2_64).
have E1: to_uint (p + (o + W64.of_int 24)) = to_uint p + to_uint o + 24 by smt(@W64 pow2_64).
have E2: to_uint (p + (o + W64.of_int 16)) = to_uint p + to_uint o + 16 by smt(@W64 pow2_64).
have E3: to_uint (p + (o + W64.of_int 8)) = to_uint p + to_uint o + 8 by smt(@W64 pow2_64).

split; last first.

- move => k???. 
  rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64).
  rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64).
  rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64).
  rewrite /storeW64 get_storesE size_to_list ifF 1:/#.
  by [].

- apply (eq_from_nth witness); rewrite ?size_to_list size_load_buf // => i?.
  rewrite get_to_list nth_load_buf //.
  rewrite /storeW64 get_storesE size_to_list.
  case (i = 0) => ?.
       * rewrite E0 ifF; first by smt(@W64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64).
         rewrite /storeW64 get_storesE size_to_list ifT 1:/#.
         rewrite  /= !bits8E ifT 1:/# /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 1) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT 1:/#.
         rewrite  /= !bits8E ifF 1:/# ifT 1:/# /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 2) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT 1:/#.
         rewrite  /= !bits8E ifF 1:/# ifF 1:/# ifT 1:/# /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 3) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT 1:/#.
         rewrite  /= !bits8E ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 4) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT 1:/#.
         rewrite  /= !bits8E ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 5) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT 1:/#.
         rewrite  /= !bits8E ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 6) => ?.
       * rewrite E0 ifF ; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF ; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT 1:/#.
         rewrite  /= !bits8E ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 7) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT 1:/#.
         rewrite  /= !bits8E ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 8) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT; first by smt(@W64 pow2_64).
         rewrite  /= !bits8E ifT; first by smt(@W64 pow2_64).
         rewrite /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 9) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT ; first by smt(@W64 pow2_64).
         rewrite  /= !bits8E ifF; first by smt(@W64 pow2_64).  
         rewrite ifT ; first by smt(@W64 pow2_64).
         rewrite /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 10) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT ; first by smt(@W64 pow2_64).
         rewrite  /= !bits8E ifF; first by smt(@W64 pow2_64).
         rewrite ifF ; first by smt(@W64 pow2_64).
         rewrite ifT ; first by smt(@W64 pow2_64).
         rewrite /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 11) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT; first by smt(@W64 pow2_64).
         rewrite  /= !bits8E.
         do 3! (rewrite ifF; first by smt(@W64 pow2_64)).
         rewrite ifT; first by smt(@W64 pow2_64).
         rewrite /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 12) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT; first by smt(@W64 pow2_64).
         rewrite  /= !bits8E.
         do 4! (rewrite ifF; first by smt(@W64 pow2_64)).
         rewrite ifT; first by smt(@W64 pow2_64).
         rewrite /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 13) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT; first by smt(@W64 pow2_64).
         rewrite  /= !bits8E.
         do 5! (rewrite ifF; first by smt(@W64 pow2_64)).
         rewrite ifT; first by smt(@W64 pow2_64).
         rewrite /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 14) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT; first by smt(@W64 pow2_64).
         rewrite  /= !bits8E.
         do 6! (rewrite ifF; first by smt(@W64 pow2_64)).
         rewrite ifT; first by smt(@W64 pow2_64).
         rewrite /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 15) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT; first by smt(@W64 pow2_64).
         rewrite  /= !bits8E.
         do 7! (rewrite ifF; first by smt(@W64 pow2_64)).
         rewrite ifT; first by smt(@W64 pow2_64).
         rewrite /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 16) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT; first by smt(@W64 pow2_64).
         rewrite  /= !bits8E.
         rewrite ifT; first by smt(@W64 pow2_64).
         rewrite /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 17) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT; first by smt(@W64 pow2_64).
         rewrite  /= !bits8E.
         rewrite ifF; first by smt(@W64 pow2_64).
         rewrite ifT; first by smt(@W64 pow2_64).
         rewrite /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 18) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT; first by smt(@W64 pow2_64).
         rewrite  /= !bits8E.
         do 2! (rewrite ifF; first by smt(@W64 pow2_64)).
         rewrite ifT; first by smt(@W64 pow2_64).
         rewrite /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 19) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT; first by smt(@W64 pow2_64).
         rewrite  /= !bits8E.
         do 3! (rewrite ifF; first by smt(@W64 pow2_64)).
         rewrite ifT; first by smt(@W64 pow2_64).
         rewrite /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 20) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT; first by smt(@W64 pow2_64).
         rewrite  /= !bits8E.
         do 4! (rewrite ifF; first by smt(@W64 pow2_64)).
         rewrite ifT; first by smt(@W64 pow2_64).
         rewrite /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 21) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT; first by smt(@W64 pow2_64).
         rewrite  /= !bits8E.
         do 5! (rewrite ifF; first by smt(@W64 pow2_64)).
         rewrite ifT; first by smt(@W64 pow2_64).
         rewrite /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 22) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT; first by smt(@W64 pow2_64).
         rewrite  /= !bits8E.
         do 6! (rewrite ifF; first by smt(@W64 pow2_64)).
         rewrite ifT; first by smt(@W64 pow2_64).
         rewrite /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 23) => ?.
       * rewrite E0 ifF; first by smt(@W64 pow2_64).
         rewrite /storeW64 get_storesE size_to_list ifT; first by smt(@W64 pow2_64).
         rewrite  /= !bits8E.
         do 7! (rewrite ifF; first by smt(@W64 pow2_64)).
         rewrite ifT; first by smt(@W64 pow2_64).
         rewrite /= wordP => k?.
         rewrite /get64_direct pack8E initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.
  case (i = 24) => ?.
       * rewrite E0 ifT; first by smt(@W64 pow2_64).
         rewrite /get64_direct pack8E wordP => k? />. 
         rewrite /= !bits8E ifT; first by smt(@W64 pow2_64).
         rewrite initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.   
  case (i = 25) => ?.
       * rewrite E0 ifT; first by smt(@W64 pow2_64). 
         rewrite /get64_direct pack8E wordP => k? />. 
         rewrite /= !bits8E.
         rewrite ifF; first by smt(@W64 pow2_64). 
         rewrite  ifT; first by smt(@W64 pow2_64).
         rewrite initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.   
  case (i = 26) => ?.
       * rewrite E0 ifT; first by smt(@W64 pow2_64). 
         rewrite /get64_direct pack8E wordP => k? />. 
         rewrite /= !bits8E.
         do 2! (rewrite ifF; first by smt(@W64 pow2_64)). 
         rewrite  ifT; first by smt(@W64 pow2_64).
         rewrite initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.   
  case (i = 27) => ?.
       * rewrite E0 ifT; first by smt(@W64 pow2_64). 
         rewrite /get64_direct pack8E wordP => k? />. 
         rewrite /= !bits8E.
         do 3! (rewrite ifF; first by smt(@W64 pow2_64)). 
         rewrite  ifT; first by smt(@W64 pow2_64).
         rewrite initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.   
  case (i = 28) => ?.
       * rewrite E0 ifT; first by smt(@W64 pow2_64). 
         rewrite /get64_direct pack8E wordP => k? />. 
         rewrite /= !bits8E.
         do 4! (rewrite ifF; first by smt(@W64 pow2_64)). 
         rewrite  ifT; first by smt(@W64 pow2_64).
         rewrite initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.    
  case (i = 29) => ?.
       * rewrite E0 ifT; first by smt(@W64 pow2_64). 
         rewrite /get64_direct pack8E wordP => k? />. 
         rewrite /= !bits8E.
         do 5! (rewrite ifF; first by smt(@W64 pow2_64)). 
         rewrite  ifT; first by smt(@W64 pow2_64).
         rewrite initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.   
  case (i = 30) => ?.
       * rewrite E0 ifT; first by smt(@W64 pow2_64). 
         rewrite /get64_direct pack8E wordP => k? />. 
         rewrite /= !bits8E.
         do 6! (rewrite ifF; first by smt(@W64 pow2_64)). 
         rewrite  ifT; first by smt(@W64 pow2_64).
         rewrite initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.   
  case (i = 31) => ?.
       * rewrite E0 ifT; first by smt(@W64 pow2_64). 
         rewrite /get64_direct pack8E wordP => k? />. 
         rewrite /= !bits8E.
         do 7! (rewrite ifF; first by smt(@W64 pow2_64)). 
         rewrite  ifT; first by smt(@W64 pow2_64).
         rewrite initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.  
  case (i = 32) => [?|/#].
       * rewrite E0 ifT 1:/#.
         rewrite /get64_direct pack8E wordP => k? />. 
         rewrite /= !bits8E ifT 1:/#.
         rewrite initiE //= initiE 1:/# //= initiE 1:/# //= initiE /#.   
qed.

lemma p_copy_nbytes_from_ptr_post (mem : global_mem_t) (o p : W64.t) (input : W8.t Array32.t) :
phoare [
    M(Syscall).copy_nbytes_from_ptr :
        Glob.mem = mem /\
        (* valid ptr *)
        0 <= to_uint p + to_uint o + 32 < W64.max_uint /\
        arg = (p, o, input) 
        ==>
        res = p /\
        (load_buf Glob.mem (p + o) 32 = to_list input) /\
          (* O resto da memoria mantem se inalterada *)
          forall (k : int), 0 <= k < W64.max_uint =>
             !(to_uint p + to_uint o <= k < to_uint p + to_uint o + 32) => 
                Glob.mem.[k] = mem.[k]
	] = 1%r by conseq copy_nbytes_from_ptr_ll (copy_nbytes_from_ptr_post mem o p input).

lemma memcpy_mem_mem (mem : global_mem_t) (dst_ptr oo src_ptr oi len : W64.t) :
    phoare [
      M(Syscall)._x__memcpy_u8pu8p :
      (* pointers are disjoint *)
      Glob.mem = mem /\

      0 <= to_uint len /\
      
      0 <= to_uint src_ptr + to_uint oi + to_uint len < W64.max_uint /\
      0 <= to_uint dst_ptr + to_uint oo + to_uint len < W64.max_uint /\

      disjoint_ptr (to_uint src_ptr + to_uint oi) (to_uint len)
                   (to_uint dst_ptr + to_uint oo)  (to_uint len) /\

      arg = (dst_ptr, oo, src_ptr, oi, len)
      ==> 
      load_buf Glob.mem (dst_ptr + oo) (to_uint len) = 
        load_buf Glob.mem (src_ptr + oi) (to_uint len) /\
      
      (* O resto da memoria mantem se inalterada *)
      forall (k : int), 0 <= k <  W64.max_uint =>
         !(to_uint dst_ptr + to_uint oo <= k < to_uint dst_ptr+ to_uint oo + to_uint len) =>
            Glob.mem.[k] = mem.[k]
      ] = 1%r.
proof.
proc => /=; inline.
while 
(
  bytes1 = len /\ 

  0 <= to_uint i <= to_uint bytes1 /\ 
  in_offset1 = oi + i /\
  out_offset1 = oo + i  /\
  out_ptr1 = dst_ptr /\ 
  in_ptr1 = in_ptr /\
  in_ptr = src_ptr /\
 
  0 <= to_uint len /\

      0 <= to_uint src_ptr + to_uint oi + to_uint len < W64.max_uint /\
      0 <= to_uint dst_ptr + to_uint oo + to_uint len < W64.max_uint /\



  disjoint_ptr (to_uint src_ptr + to_uint oi) (to_uint len)
               (to_uint dst_ptr + to_uint oo) (to_uint len) /\

  load_buf Glob.mem (dst_ptr + oo) (to_uint i) = 
  load_buf Glob.mem (src_ptr + oi) (to_uint i) /\

  forall (k : int),
    0 <= k < W64.max_uint =>
    ! (to_uint dst_ptr + to_uint oo <= k &&
       k < to_uint dst_ptr + to_uint oo + to_uint i) =>
    Glob.mem.[k] = mem.[k]
)
(to_uint bytes1 - to_uint i); last first.
  + auto => /> H0 H1 *.
    split.
      - apply (eq_from_nth witness); by rewrite !size_load_buf /#.
      - move => mem0 i0.
        split => [* |]; first by rewrite ultE /#.
        rewrite ultE => H2 H3 H4.
        have E: to_uint i0 = to_uint len by smt().
        rewrite E => H5 H6.
        split => [| /#]; by apply H5.
  + auto => /> &hr H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
    rewrite ultE to_uintD => H10 *.   
    (do split; 1,2,7: by smt()); 1,2: by ring.
    - apply (eq_from_nth witness); rewrite size_load_buf /= 1:/# ?size_load_buf // => [/# | j?].
      rewrite /load_buf !nth_mkseq //= !load_store_mem. 
      rewrite /valid_ptr in H5.
      have ->: to_uint (dst_ptr + oo) = to_uint dst_ptr + to_uint oo by rewrite to_uintD_small /#.
      have ->: to_uint (dst_ptr + (oo + i{hr})) = to_uint dst_ptr + to_uint oo + to_uint i{hr} by smt(@W64 pow2_64).
      have ->: to_uint (src_ptr + oi) = to_uint src_ptr + to_uint oi by rewrite to_uintD_small /#.
      have ->: (to_uint (src_ptr + (oi + i{hr}))) =
                to_uint src_ptr + to_uint oi + to_uint i{hr} by smt(@W64 pow2_64). 
      case (j = to_uint i{hr}) => [/# | Hb].
      rewrite ifF 1:/#. 
      case (
            to_uint src_ptr + to_uint oi + j =
            to_uint dst_ptr + to_uint oo + to_uint i{hr}
      ) => ?.
           * have ->: loadW8 Glob.mem{hr} (to_uint src_ptr + to_uint oi + to_uint i{hr}) = 
                       nth witness (load_buf Glob.mem{hr} (src_ptr + oi) (to_uint i{hr})) (to_uint i{hr})
                       by rewrite nth_load_buf /#.
              by rewrite -H8 nth_load_buf /#.
            * have ->: Glob.mem{hr}.[to_uint src_ptr + to_uint oi + j] = 
                       nth witness (load_buf Glob.mem{hr} (src_ptr + oi) (to_uint i{hr})) j
                       by rewrite nth_load_buf 1:/#; congr; rewrite to_uintD_small /#.
              rewrite -H8 nth_load_buf 1:/#; congr; rewrite to_uintD_small /#.
    - move => /= k??Hk.
      rewrite /storeW8 /loadW8 get_setE.
      have ->: to_uint (dst_ptr + (oo + i{hr})) = to_uint dst_ptr + to_uint oo + to_uint i{hr} by smt(@W64 pow2_64).
          have ->: (to_uint (src_ptr + (oi + i{hr}))) =
                   to_uint src_ptr + to_uint oi + to_uint i{hr} by smt(@W64 pow2_64). 
          case (k = to_uint dst_ptr + to_uint oo + to_uint i{hr}) => [Ha | Hb]; last first.
            * rewrite H9 1:/#; smt(@W64 pow2_64).
          rewrite -H9 1,2:/# Ha; smt(@W64 pow2_64).
qed.


(*
    `nbytes_witness` is a witness value of type `nbytes`.

    MOTIVATION: Reading outside the bounds of an array (arrays come the jasmin 
                implementation) evaluates to witness, but reading outside the bounds
                of a list (lists come from the EasyCrypt specification) evaluates to 
                the default value passed to nth (usually witness, but it this case it 
                cannot be witness).

                Problem: The EasyCrypt spec uses nbytes list, while on the implementation
                         side we have W8.t Arrayx.t.
                         Reading outside the bounds of the array evaluates to witness, 
                         and reading outside the bounds of the list evaluates to the 
                         default value passed to nth. If the default value is nth, we end
                         up with 
                         
                         nth witness (val witness) i = witness.
                              ^
                              |
                              |
                          This witness comes from applying the lemma
                          eq_from_nth with the default value witness,
                          not from the witness used in nth

                         We cannot simplify this any further. This means that the default
                         value of nth cannot be witness. Instead, it needs to be a value such
                         that forall (i : int), nth witness (THAT VALUE) i = witnes.
  
                         In this case, THAT VALUE = NBytes.insubd (nseq n witness), that we 
                         will call nbytes_witness for brevity. The previously mentioned
                         property is proved in the lemma lemma nth_nbytes_witness.
   
                   
                         Now, if the default value of nth is nbytes_witness, and we apply 
                         the lemma eq_from_nth with witness as the default value, we end up 
                         with 

                         nth witness (val nbytes_witness) i, that we know evaluates to witness.

op nbytes_witness : nbytes = NBytes.insubd (nseq n witness).
*)

lemma nth_nbytes_witness : 
    forall (k : int), nth witness (NBytes.val nbytes_witness) k = witness.
proof.
move => k.
case (0 <= k < n) => [k_in | k_out].
  + rewrite /nbytes_witness.
    rewrite NBytes.insubdK; first by rewrite /P size_nseq /#.
    rewrite nth_nseq //.
rewrite nth_out // NBytes.valP /#.
qed.


(* Obs: Este lema precisa de ser phoare p ser usado na prova do treehash *)     
lemma memcpy_treehash_node_2 (_stack_impl : W8.t Array352.t, o : W64.t) (stack_spec : nbytes list) :
    n = XMSS_N /\
    h = XMSS_FULL_HEIGHT =>
    phoare [
      M(Syscall).memcpy_u8u8_2_treehash____memcpy_u8u8_2:

      size stack_spec = 11 /\ 

      2 <= to_uint o <= 2^h /\

      sub _stack_impl 0 (XMSS_N * min (to_uint o) (size stack_spec)) = 
      sub_list (nbytes_flatten stack_spec) 0 (XMSS_N * min (to_uint o) (size stack_spec)) /\

      arg.`2 = _stack_impl /\
      arg.`3 = (o - W64.of_int 2) * (W64.of_int 32) /\
      arg.`4 = (W64.of_int 64)
      ==>
      to_list res.`1 = 
           NBytes.val (nth nbytes_witness stack_spec (to_uint (o - (of_int 2)%W64))) ++ 
           NBytes.val (nth nbytes_witness stack_spec (to_uint (o - (of_int 1)%W64)))
    ] = 1%r.
proof.
rewrite /XMSS_N /XMSS_FULL_HEIGHT => [#] n_val h_val.
proc => /=.
conseq (: _ ==> 
  to_list out = sub_list (nbytes_flatten stack_spec) (n * (to_uint o - 2)) (2 * n)
).
    + auto => /> &hr H0 H1 H2 out; split => Hout; rewrite Hout. 
(** -------------------------------------------------------------------------------------------- **)
      have ->: (to_uint (o - W64.one)) = to_uint o - 1 by rewrite to_uintB // uleE /=/#.
      have ->: (to_uint (o - (of_int 2)%W64)) = to_uint o - 2 by rewrite to_uintB // uleE /=/#.
      case (0 <= to_uint o - 1 < size stack_spec) => [H_o_m_1_in | H_o_m_1_out].
         (* Cenario normal => tudo in bounds => todos os acessos sao validos *)
         - apply (eq_from_nth witness).
               + by rewrite size_sub_list 1:/# size_cat !NBytes.valP n_val.
           rewrite size_cat !NBytes.valP n_val /= => i?.
           (case (0 <= i < 32) => [Hfst | Hsnd]; rewrite nth_cat NBytes.valP n_val; [rewrite ifT 1:/# | rewrite ifF 1:/#]);
           rewrite nth_sub_list 1:/# nth_nbytes_flatten 1:/# ;smt(nth_change_dfl).

      (* Daqui para a frente, stack_spec[o - 1] = witness *)     
      have ->: nth nbytes_witness stack_spec (to_uint o - 1) = nbytes_witness 
      by rewrite nth_out /#.
      case (0 <= to_uint o - 2 < size stack_spec) => [H_o_m_2_in | H_o_m_2_out].
         - apply (eq_from_nth witness). 
               + by rewrite size_cat !NBytes.valP n_val /= size_sub_list /#.
           rewrite size_cat !NBytes.valP n_val /= => i?.
           case (0 <= i < 32) => [Hfst | Hsnd];
               rewrite nth_cat NBytes.valP n_val; [rewrite ifT 1:/# | rewrite ifF 1:/#].
               + rewrite nth_sub_list 1:/# nth_nbytes_flatten 1:/#. 
                 smt(nth_change_dfl).                 
               + rewrite nth_nbytes_witness.
                 rewrite nth_sub_list 1:/#. 
                 rewrite nth_out // size_nbytes_flatten /#.
         - have ->: nth nbytes_witness stack_spec (to_uint o - 2) = nbytes_witness
           by rewrite nth_out /#.
           apply (eq_from_nth witness). 
               + by rewrite size_cat !NBytes.valP n_val /= size_sub_list /#.
           rewrite size_cat NBytes.valP n_val /= => i?.
           case (0 <= i < 32) => [Hfst | Hsnd];
               rewrite nth_cat NBytes.valP n_val; [rewrite ifT 1:/# | rewrite ifF 1:/#].
               + rewrite nth_nbytes_witness.
                 rewrite nth_sub_list //.
                 rewrite nth_out // size_nbytes_flatten /#.
               + rewrite nth_nbytes_witness.
                 rewrite nth_sub_list //.
                 rewrite nth_out // size_nbytes_flatten /#.
(** -------------------------------------------------------------------------------------------- **)
      have ->: (to_uint (o - W64.one)) = to_uint o - 1 by rewrite to_uintB // uleE /#.
      have ->: (to_uint (o - (of_int 2)%W64)) = to_uint o - 2 by rewrite to_uintB // uleE /#.
      case (0 <= to_uint o - 1 < size stack_spec) => [H_o_m_1_in | H_o_m_1_out].
         (* Cenario normal => tudo in bounds => todos os acessos sao validos *)
         - apply (eq_from_nth witness).
               + by rewrite size_sub_list 1:/# size_cat !NBytes.valP n_val.
           rewrite size_sub_list 1:/# n_val /= => i?.
           case (0 <= i < 32) => [Hfst | Hsnd];
               rewrite nth_cat NBytes.valP n_val; [rewrite ifT 1:/# | rewrite ifF 1:/#].
               + rewrite nth_sub_list 1:/# nth_nbytes_flatten 1:/#.
                 smt(nth_change_dfl).
               + rewrite nth_sub_list 1:/# nth_nbytes_flatten 1:/#.
                 smt(nth_change_dfl).
      (* Daqui para a frente, stack_spec[o - 1] = witness *)     
      have ->: nth nbytes_witness stack_spec (to_uint o - 1) = nbytes_witness 
      by rewrite nth_out /#.
      case (0 <= to_uint o - 2 < size stack_spec) => [H_o_m_2_in | H_o_m_2_out].
         - apply (eq_from_nth witness). 
               + by rewrite size_cat !NBytes.valP n_val /= size_sub_list /#.
           rewrite size_sub_list 1:/# n_val /= => i?.
           case (0 <= i < 32) => [Hfst | Hsnd];
               rewrite nth_cat NBytes.valP n_val; [rewrite ifT 1:/# | rewrite ifF 1:/#].
               + rewrite nth_sub_list 1:/# nth_nbytes_flatten 1:/#. 
                 smt(nth_change_dfl).                 
               + rewrite nth_nbytes_witness.
                 rewrite nth_sub_list 1:/#. 
                 rewrite nth_out // size_nbytes_flatten /#.
         - have ->: nth nbytes_witness stack_spec (to_uint o - 2) = nbytes_witness
           by rewrite nth_out /#.
           apply (eq_from_nth witness). 
               + by rewrite size_cat !NBytes.valP n_val /= size_sub_list /#.
           rewrite size_sub_list 1:/# n_val /= => i?.
           case (0 <= i < 32) => [Hfst | Hsnd];
               rewrite nth_cat NBytes.valP n_val; [rewrite ifT 1:/# | rewrite ifF 1:/#].
               + rewrite nth_nbytes_witness.
                 rewrite nth_sub_list //.
                 rewrite nth_out // size_nbytes_flatten /#.
               + rewrite nth_nbytes_witness.
                 rewrite nth_sub_list //.
                 rewrite nth_out // size_nbytes_flatten /#.

(** -------------------------------------------------------------------------------------------- **)

while (
  size stack_spec = 11 /\

  0 <= to_uint i <= 64 /\ 
  2 <= to_uint o <= 2^h /\

  in_offset = (o - (of_int 2)%W64) * (of_int 32)%W64 + i /\
  in_0 = _stack_impl /\
  bytes = (of_int 64)%W64 /\
 
  sub _stack_impl 0 (32 * min (to_uint o) (size stack_spec)) = 
  sub_list (nbytes_flatten stack_spec) 0 (32 * min (to_uint o) (size stack_spec)) /\

  forall (k : int), 0 <= k < to_uint i => 
     out.[k] = in_0.[to_uint ((o - (of_int 2)%W64) * (of_int 32)%W64) + k]

)
(64 - to_uint i); last first.

(* ------------------------------------------------------------------------------- *)
(* last subgoal of while                                                           *)
(* ------------------------------------------------------------------------------- *)


auto => /> &hr H0 H1 H2 H3.
split => [/# | i0 out0].
rewrite ultE of_uintK /=.
split => [/# | H4 H5 H6].
have ->: to_uint i0 = 64 by smt().
have E: to_uint i0 = 64 by smt().
move => H7.
apply (eq_from_nth witness); first by rewrite size_to_list size_sub_list /#.
rewrite size_to_list => j?.
rewrite get_to_list H7 //.
case (0 <= to_uint o < size stack_spec) => [H_in | H_out].
  + have Ho : min (to_uint o) (size stack_spec) = to_uint o by smt().
    rewrite nth_sub_list 1:/# nth_nbytes_flatten 1:/#.
    have ->: to_uint ((o - (of_int 2)%W64) * (of_int 32)%W64) = (to_uint o - 2) * 32. 
      - rewrite to_uintM of_uintK /= to_uintB; first by rewrite uleE of_uintK /#.
        rewrite of_uintK /= /#. 
    have ->: _stack_impl.[(to_uint o - 2) * 32 + j] = 
             nth witness (sub _stack_impl 0 (32 * min (to_uint o) (size stack_spec))) 
             ((to_uint o - 2) * 32 + j) by rewrite nth_sub /#.
    rewrite H3 Ho nth_sub_list 1:/# nth_nbytes_flatten 1:/# n_val /#.

have Ho : min (to_uint o) (size stack_spec) = 11 by smt().
have E1: 2^h = 1048576 by rewrite h_val /#. 

have ->: to_uint ((o - (of_int 2)%W64) * (of_int 32)%W64) =  (to_uint o - 2) * 32.  
 + rewrite to_uintM of_uintK /= to_uintB; first by rewrite uleE of_uintK /#.
   rewrite of_uintK /= /#. 
rewrite nth_sub_list 1:/#.
case (0 <= to_uint o - 2 < 11) => [H_o_m_2_in | H_o_m_2_out]; last first.
 + rewrite get_out 1:/# nth_out // size_nbytes_flatten /#. 
case (0 <= j < 32) => [Hfst | Hsnd].
 + have ->: _stack_impl.[(to_uint o - 2) * 32 + j] = 
            nth witness 
            (sub _stack_impl 0 (32 * min (to_uint o) (size stack_spec)))
            ((to_uint o - 2) * 32 + j) by rewrite Ho /= nth_sub // /#.
   by rewrite H3 nth_sub_list /#.
case (0 <= to_uint o - 1 < 11) => [H_o_m_1_in | H_o_m_1_out]; last first.
 + rewrite get_out 1:/# nth_out // size_nbytes_flatten /#. 
case (0 <= j < 32) => [Hfst_2 | Hsnd_2].
 + have ->: _stack_impl.[(to_uint o - 2) * 32 + j] = 
            nth witness 
            (sub _stack_impl 0 (32 * min (to_uint o) (size stack_spec)))
            ((to_uint o - 2) * 32 + j) by rewrite Ho /= nth_sub // /#.
   by rewrite H3 nth_sub_list /#.
 + have ->: _stack_impl.[(to_uint o - 2) * 32 + j] = 
            nth witness 
            (sub _stack_impl 0 (32 * min (to_uint o) (size stack_spec)))
            ((to_uint o - 2) * 32 + j) by rewrite Ho /= nth_sub // /#.
   by rewrite H3 nth_sub_list /#.

(* ------------------------------------------------------------------------------- *)
(* first subgoal of while                                                          *)
(* ------------------------------------------------------------------------------- *)

auto => /> &hr H0 H1 H2 H3 H4 H5 H6.
rewrite ultE of_uintK /= => H7.
have E: 2^h = 1048576 by rewrite h_val /#. 
do split; 1,2,5: by smt(@W64 pow2_64).
 + ring.
 + have ->: to_uint (i{hr} + W64.one) = to_uint i{hr} + 1 by rewrite to_uintD_small /#.
   move => k??.
   rewrite get_setE 1:/#. 
   have E2: to_uint ((o - (of_int 2)%W64) * (of_int 32)%W64) = 
            (to_uint o - 2) * 32.
      - rewrite to_uintM of_uintK /= to_uintB; first by rewrite uleE of_uintK /#.
        rewrite of_uintK /= /#.
   have ->: to_uint ((o - (of_int 2)%W64) * (of_int 32)%W64 + i{hr}) =
            (to_uint o - 2) * 32 + to_uint i{hr}.
      - rewrite to_uintD E2 /#. 
   rewrite E2.
   case (k = to_uint i{hr}) => [-> // | ?]. (* trivial solves the first goal *)
   rewrite H6 1:/#; congr; rewrite to_uintM of_uintK /= to_uintB ?of_uintK 2:/# uleE of_uintK /#.
qed.

lemma p_treehash_memcpy_0 (node : W8.t Array32.t) (stack : nbytes list) (_stack : W8.t Array352.t) (offset : W64.t) : 
    n = XMSS_N => 
    phoare [
      M(Syscall).memcpy_u8u8_3_treehash____memcpy_u8u8_3 :
      0 <= to_uint offset <= 2^20 /\
      size stack = 11 /\
      
      sub _stack 0 (XMSS_N * min (to_uint offset) (size stack)) = 
      sub_list (nbytes_flatten stack) 0  (XMSS_N * min (to_uint offset) (size stack)) /\

      arg = (_stack, node, offset * (W64.of_int 32), 32) 
      ==> 
      sub res 0 (XMSS_N * min (to_uint offset + 1) (size stack)) =
      sub_list
          (nbytes_flatten
             (put stack (to_uint offset) ((NBytes.insubd (to_list node)))%NBytes)) 
          0
          (XMSS_N * min (to_uint offset + 1) (size stack))
    ] = 1%r.
proof.
rewrite /XMSS_N => n_val. 
proc => /=. 
sp.
while (
  bytes = 32 /\ 
  inc = bytes /\ 
  (0 <= to_uint offset <= 1048576) /\
  size stack = 11 /\
  out_offset = offset * (of_int 32)%W64 /\
  in_0 = node /\
  
  0 <= i <= 32 /\
 
  sub _stack 0 (32 * min (to_uint offset) (size stack)) =
  sub_list (nbytes_flatten stack) 0 (32 * min (to_uint offset) (size stack)) /\
 
  (forall (k : int), 
       0 <= k < i => 
        out.[to_uint out_offset + k] = 

if 0 <= to_uint out_offset + k < 352 then in_0.[k] else witness) /\

  forall (k : int), 0 <= k < 352 =>
      !(to_uint out_offset <= k < to_uint out_offset + i) =>
         out.[k]  = _stack.[k]
)
(32 - i); last first.
(** -------------------------------------------------------------------------------------------- **)
  + auto => /> H0 H1 H2 H3.
    split => [/# |].
    move => i0 out.
    split => [/# |].
    move => H4 H5 H6.
    have ->: i0 = 32 by smt().
    have ->: to_uint (offset * (of_int 32)%W64) = to_uint offset * 32 by rewrite to_uintM /=/#.
    move => H7 H8.
    apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list // /#.
    rewrite size_sub 1:/# H2 => i Hi.
    rewrite nth_sub 1:/# /= nth_sub_list //.
    rewrite nth_nbytes_flatten; first by rewrite size_put /#.
    case (0 <= to_uint offset + 1 < size stack) => [H_in_bounds | H_out_of_bounds].
       - rewrite nth_put 1:/# /=.
         case (to_uint offset = i %/ n) => [Ha | Hb].
           * rewrite NBytes.insubdK; first by rewrite /P size_to_list /#.

             have E7: forall (k : int),
                0 <= k && k < 32 =>
                    out.[to_uint offset * 32 + k] =
                       node.[k] by smt().

             rewrite get_to_list -E7 1,2:/#. 
           * rewrite H8 1,2:/#. 
             rewrite -nth_nbytes_flatten 1:/#.
             have ->: nth witness (nbytes_flatten stack) i = 
                      nth witness (
                           sub_list (nbytes_flatten stack) 0
                           (32 * min (to_uint offset) (size stack))
                      ) i by rewrite nth_sub_list 1:/#; do congr.
             rewrite -H3.
             by rewrite nth_sub 1:/#.
       - (* offset + 1  esta out of bounds *)      
         have E1: min (to_uint offset + 1) (size stack) = size stack by smt().
         case (0 <= to_uint offset < size stack) => [Ha | Hb].
           * rewrite nth_put 1:/# /=.
             case (to_uint offset = i %/ n) => [Haa | Hbb].
              + rewrite NBytes.insubdK; first by rewrite /P size_to_list /#.

             have E7: forall (k : int),
                0 <= k && k < 32 =>
                    out.[to_uint offset * 32 + k] =
                       node.[k] by smt().

                rewrite get_to_list -E7 1,2:/#.
              + rewrite H8 1,2:/#. 
                rewrite -nth_nbytes_flatten 1:/#.
                have ->: nth witness (nbytes_flatten stack) i = 
                         nth witness (
                              sub_list (nbytes_flatten stack) 0
                              (32 * min (to_uint offset) (size stack))
                         ) i by rewrite nth_sub_list 1:/#; do congr.
                rewrite -H3.
                by rewrite nth_sub 1:/#.
           * rewrite put_out 1:/# /=.
             rewrite -(nth_nbytes_flatten) 1:/#.
             rewrite H8 1,2:/#. 
             have ->: nth witness (nbytes_flatten stack) i = 
                      nth witness (
                           sub_list (nbytes_flatten stack) 0
                           (32 * min (to_uint offset) (size stack))
                      ) i by rewrite nth_sub_list 1:/#; do congr.
             rewrite -H3.
             by rewrite nth_sub 1:/#.

(** -------------------------------------------------------------------------------------------- **)
auto => /> &hr H0 H1 H2 H3 H4 H5 H6 H7 H8.

have E: to_uint (offset * (of_int 32)%W64) = to_uint offset * 32 by rewrite to_uintM /=/#.
do split; 1,2,5: by smt().
  + move => k??.
    have ->: to_uint (offset * (of_int 32)%W64 + (of_int i{hr})%W64) = 
             (to_uint offset * 32) + i{hr} by rewrite to_uintD to_uintM /= of_uintK /#.
    case (0 <= to_uint offset * 32 + i{hr} < 352) => ?; first by rewrite get_setE /#.
    by rewrite ifF 1:/# get_out 1:/#.
  + rewrite E => k???.
    rewrite -H7 1,2:/# get_set_if ifF // to_uintD to_uintM of_uintK /=; smt(@W64 pow2_64).
qed.



lemma p_treehash_memcpy (_node : W8.t Array32.t) (stackSpec : nbytes list) 
                        (stackImpl : W8.t Array352.t) (o : W64.t) : 
    n = XMSS_N => 
    phoare [
      M(Syscall).memcpy_u8u8_3_treehash____memcpy_u8u8_3 :

      0 <= to_uint o <= 2^20 /\
      size stackSpec = 11 /\

      
      sub stackImpl 0 (XMSS_N * (min (to_uint o + 2) (size stackSpec))) = 
      sub_list (nbytes_flatten stackSpec) 0  (XMSS_N * min (to_uint o + 2) (size stackSpec)) /\

      arg = (stackImpl, _node, o * (W64.of_int 32), 32) 
      ==> 
      sub res 0 (XMSS_N * min (to_uint o + 2) (size stackSpec)) =
      sub_list
          (nbytes_flatten
             (put stackSpec (to_uint o) ((NBytes.insubd (to_list _node)))%NBytes)) 
          0
          (XMSS_N * min (to_uint o + 2) (size stackSpec))
    ] = 1%r.
proof.
rewrite /XMSS_N => n_val.
proc => /=.
while ( 
  inc = 32 /\
  bytes = 32 /\
  0 <= to_uint o <= 2^20 /\
  size stackSpec = 11 /\
  out_offset = o * (of_int 32)%W64 /\
  in_0 = _node /\

  sub stackImpl 0 (XMSS_N * (min (to_uint o + 2) (size stackSpec))) = 
     sub_list (nbytes_flatten stackSpec) 0  (XMSS_N * min (to_uint o + 2) (size stackSpec)) /\
 
  0 <= i <= inc /\

  (forall (k : int), 
       0 <= k < i => 
        out.[to_uint out_offset + k] = 
             if 0 <= to_uint out_offset + k < 352 then in_0.[k] else witness) /\

  forall (k : int), 0 <= k < 352 =>
      !(to_uint out_offset <= k < to_uint out_offset + i) =>
         out.[k]  = stackImpl.[k]

) 
(32 -  i); last first.
  + auto => /> H0 H1 H2 H3.
    split => [/# |].
    move => i0 out.
    split => [/# |].
    move => H4 H5 H6 H7.
    have ->: i0 = 32 by smt().
    have ->: to_uint (o * (of_int 32)%W64) = to_uint o * 32 by smt(@W64 pow2_64).
    move => H8 H9.
    apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list // /#.
    rewrite size_sub 1:/# H2 => i Hi.
    rewrite nth_sub 1:/# /= nth_sub_list //.
    rewrite nth_nbytes_flatten /=; first by rewrite size_put /#.
    case (0 <= to_uint o < size stackSpec) => [H_in | H_out]; last first.
       * rewrite put_out 1:/#.
         rewrite H9 1,2:/#. 
         have ->: stackImpl.[i] = 
                  nth witness (
                      sub stackImpl 0 (XMSS_N * min (to_uint o + 2) (size stackSpec))
                  ) i by rewrite nth_sub /#.
         rewrite H5 nth_sub_list 1:/# nth_nbytes_flatten /#.
       * rewrite nth_put 1:/#.       
         case (to_uint o = i %/ n) => [Ha | Hb]; last first.
             - rewrite H9 1,2:/#. 
               have ->: stackImpl.[i] = 
                         nth witness (
                            sub stackImpl 0 (XMSS_N * min (to_uint o + 2) (size stackSpec))
                        ) i by rewrite nth_sub /#.
               rewrite H5 nth_sub_list 1:/# nth_nbytes_flatten /#.
             - rewrite NBytes.insubdK; first by rewrite /P size_to_list /#.
               rewrite get_to_list; smt(@List).

  + auto => /> &hr H0 H1 H2 H3 H4 H5 H6 H7 H8 *; do split; 1,2,5: by smt().            
       * move => k??.
         have E0: to_uint (o * (of_int 32)%W64 + (of_int i{hr})%W64) = 
                 (to_uint o * 32) + i{hr} by smt(@W64 pow2_64).
         have E1: to_uint (o * (of_int 32)%W64) =
                  to_uint o * 32 by smt(@W64 pow2_64).
         case (0 <= to_uint o * 32 + i{hr} < 352) => [Ha | Hb]; last first.
             - rewrite E0 get_set_if ifF 1:/#.
               rewrite ifF; first by smt(@W64 pow2_64).
               rewrite get_out; first by smt(@W64 pow2_64).
               reflexivity.
         rewrite E0 get_setE // E1.
         case (k = i{hr}) => [-> //= /# | Hy].
         rewrite ifF 1:/# ifT 1:/#; smt(@List).
       * move => k???. 
         have ->: to_uint (o * (of_int 32)%W64 + (of_int i{hr})%W64) = 
                 (to_uint o * 32) + i{hr} by smt(@W64 pow2_64).
         case (0 <= to_uint o * 32 + i{hr} < 352) => [Ha | Hb]; last first.
             - rewrite get_set_if ifF 1:/# H7 // /#.  
         rewrite get_setE //; case (k = to_uint o * 32 + i{hr}) => [Hc | Hd]; last first.
             - rewrite H7 /#.
               have E: to_uint (o * (of_int 32)%W64) = to_uint o * 32 by smt(@W64 pow2_64).
               have := H6.               
               rewrite E /#.
qed. 

lemma memcpy_u8u8_2_64_2144_post (_in : W8.t Array2144.t, oi : W64.t):
    phoare [
      M(Syscall).memcpy_u8u8_2_ltree____memcpy_u8u8_2 : 
      arg.`2 = _in /\
      arg.`3 = oi /\
      arg.`4 = W64.of_int 64 /\
      0 <= to_uint oi < W32.max_uint /\
      0 <= to_uint (oi + W64.of_int 64) < 2144
      ==>
      to_list res.`1 = sub _in (to_uint oi) 64
    ] = 1%r.
proof.
proc => /=. 
while (
  #{/~in_offset = oi}pre /\ 
  to_uint in_offset = to_uint oi + to_uint i /\  
  0 <= to_uint i <= to_uint bytes /\
  sub out 0 (to_uint i) = sub _in (to_uint oi) (to_uint i)
)
(to_uint bytes - to_uint i); last first.
  + auto => /> &hr H0 H1 H2 H3. 
    split.
      - apply (eq_from_nth witness); first by rewrite !size_sub.    
        rewrite size_sub /#.
      - move => i0 out0. 
        rewrite ultE of_uintK /=.
        move => out0_0.
        split => [/# |].
        move => H4 H5 H6 H7.
        have ->: to_uint i0 = 64 by smt().
        move => <-.
        apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
        rewrite size_to_list => ??.
        by rewrite get_to_list nth_sub. 
    + auto => /> &hr.
      rewrite ultE of_uintK /= => H0 H1 H2 H3 H4 H5 H6 H7 H8. 
      do split; 2,3,5: by rewrite to_uintD /#.
          - rewrite !to_uintD_small 1,2:/# H4 /#.
          - apply (eq_from_nth witness); first by rewrite !size_sub to_uintD /#.
            rewrite size_sub to_uintD_small 1..3:/# /= => j?.
            rewrite !nth_sub //= get_setE //.
            case (j = to_uint i{hr}) => [-> /# |?]. 
            have ->: out{hr}.[j] = nth witness (sub out{hr} 0 (to_uint i{hr})) j by rewrite nth_sub /#.
            rewrite H7.
            rewrite nth_sub // /#.
qed.

(** -------------------------------------------------------------------------------------------- **)

lemma or_zero(w0 w1 : W8.t) : 
    (w0 `|` w1 = W8.zero) <=> (w0 = W8.zero /\ w1 = W8.zero).
proof.
split; last first.
  + move => [-> ->].
    by rewrite or0w.
  + rewrite !wordP => H.
    case (w0 = W8.zero).
      * move => -> /= k kb. move : (H k kb) => /= /#. 
      * move => *. have Hk : exists k, 0 <= k < 8 /\ w0.[k]. 
         - move : (W8.wordP w0 W8.zero); smt(W8.zerowE W8.get_out).
        elim Hk => k [kb kval]. move : (H k kb). by rewrite orwE kval.
qed.

lemma xor_eq (w0 w1 : W8.t) :
    w0 `^` w1 = W8.zero => w0 = w1 by smt(@W8). 
    
(** -------------------------------------------------------------------------------------------- **)

(******************************************************************************)
(******************               MEMSET                          *************)
(******************************************************************************)

lemma memset_4_post (input : W8.t Array3.t, v : W8.t) :
    hoare [M(Syscall).memset_idx_bytes____memset_u8 : arg=(input, v) ==> 
     (forall (k : int), 0 <= k < 3 => (res.[k] = v))].
proof.
proc.
while (
  0 <= to_uint i <= 3 /\ 
  value = v /\
  (forall (k : int), 0 <= k < to_uint i => (a.[k] = value))
); auto => /> *.
- do split; 1,2: by smt(@W64). 
  move => ???. 
  rewrite get_setE #smt:(@W64).
- split => [/# |]. 
  move => ?i0???.   
  (have ->: to_uint i0 = 3 by smt(@W64 pow2_64)) => /#. 
qed.

lemma p_memset_4_post (input : W8.t Array3.t, v : W8.t) :
    phoare [M(Syscall).memset_idx_bytes____memset_u8 : arg=(input, v) ==> 
     (forall (k : int), 0 <= k < 3 => (res.[k] = v))] = 1%r.
proof.
by conseq memset_4_ll (memset_4_post input v); auto => />.
qed.

lemma memset_128_post (input : W8.t Array128.t, v : W8.t) :
    hoare [M(Syscall).memset_i____memset_u8 : arg=(input, v) ==> 
     (forall (k : int), 0 <= k < 128 => (res.[k] = v))].
proof.
proc.
while (
  0 <= to_uint i <= 128 /\ 
  value = v /\
  (forall (k : int), 0 <= k < to_uint i => (a.[k] = value))
); auto => /> *.
- do split ; 1,2: by smt(@W64). 
  move => ???. 
  rewrite get_setE #smt:(@W64).
- split => [/# |]. 
  move => ?i0???.   
  (have ->: to_uint i0 = 128 by smt(@W64 pow2_64)) => /#.
qed.

lemma p_memset_128_post (input : W8.t Array128.t, v : W8.t) :
    phoare [M(Syscall).memset_i____memset_u8 : arg=(input, v) ==> 
     (forall (k : int), 0 <= k < 128 => (res.[k] = v))] = 1%r.
proof.
conseq memset_128_ll (memset_128_post input v); auto => />.
qed.

lemma memset_zero_post :
    hoare [M(Syscall).__memset_zero_u8 : true ==> forall (k : int), 0 <= k < 3 => (res.[k] = W8.zero)].
proof.
proc.
do 2! (rcondf 1 => //).
while (
  0 <= to_uint i <= 3 /\   
  (forall (k : int), 0 <= k < to_uint i => (a.[k] = W8.zero))
); (auto => /> &hr; rewrite ?ultE ?to_uintD /= => *; split => [/# |??]); rewrite ?get_setE ?ultE /#.
qed.

lemma p_memset_zero_post :
    phoare[M(Syscall).__memset_zero_u8 : true ==> 
      forall (k : int), 0 <= k < 3 => (res.[k] = W8.zero)] = 1%r.
proof.
conseq memset_zero_ll memset_zero_post.
auto => />.
qed.

lemma _memset_nseq : 
    hoare [
      M(Syscall).__memset_zero_u8 :
      true
      ==>
      to_list res = nseq 3 W8.zero
    ].
proof.
proc.
do 2! (rcondf 1 => //).
while (
  0 <= to_uint i <= 3 /\
  forall (k : int), 0 <= k < to_uint i => a.[k] = W8.zero
). 
    + auto => /> *.
      do split; 1,2:smt(@W64).
      move => ???. 
      rewrite get_setE #smt:(@W64).
    + auto => /> &hr ; split => [/# |]. 
      move => ? i???. 
      have ->: to_uint i = 3 by smt(@W64 pow2_64).
      move => ?. 
      apply (eq_from_nth witness); [ rewrite size_to_list size_nseq //= |].
      rewrite size_to_list => *. 
      rewrite nth_nseq 1:/# get_to_list /#.
qed.

lemma memset_nseq : 
    phoare [ M(Syscall).__memset_zero_u8 : true ==>
       to_list res = nseq 3 W8.zero] = 1%r
          by conseq memset_zero_ll _memset_nseq; auto.

lemma memset_ptr_post (ptr : W64.t, len : W64.t, v : W8.t) :
    hoare [M(Syscall).__memset_u8_ptr : 
      0 <= to_uint len < W64.modulus /\
      0 <= to_uint ptr /\ to_uint ptr + to_uint len < W64.modulus /\ 
      arg=(ptr, len, v) ==>
        forall (k:int), 0 <= k < to_uint len => (loadW8 Glob.mem (W64.to_uint (ptr  + (W64.of_int k)))) = v].
proof.
proc => /=.
while (
  #pre /\
  0 <= to_uint i <= to_uint inlen /\
  (forall (k : int), 0 <= k < to_uint i => loadW8 Glob.mem ((W64.to_uint _ptr) + k) = v )
); last first.
    + auto => /> &hr H0 H1 H2 H3.
      split => [/# |].
      move => mem j.
      rewrite ultE => H4 H5 H6.
      have ->: j = len by smt(@W64 pow2_64).
      move => H7 k??.
      rewrite /loadW8 to_uintD_small of_uintK /#. 
    + auto => /> &hr H0 H1 H2 H3 H4 H5 H6.
      rewrite ultE => H7.
      do split; 1,2: by rewrite to_uintD /#.
      rewrite to_uintD_small 1:/# => k??.
      rewrite /loadW8 /storeW8 get_setE. 
      case (k = to_uint i{hr}) => [-> |?].
        - rewrite ifT // to_uintD /#.
        - rewrite ifF; [rewrite to_uintD /# |].
          rewrite /loadW8 in H6.
          apply H6.
          smt(@W64 pow2_64).
qed.

(******************************************************************************)
(******************               MEMCPY                          *************)
(******************************************************************************)

lemma memcpy_ptr_correct (ptr : W64.t):
    hoare [M(Syscall)._x_memcpy_u8u8p : 
      arg.`2 = ptr /\  
      0 <= (to_uint ptr) + 32 <= W64.modulus /\
      0 <= to_uint ptr ==>
        res = Array32.init (fun (i : int) => loadW8 Glob.mem (to_uint ptr + i))].
proof.
proc.
inline * ; wp ; sp.
unroll 1; (rcondt 1; first by auto). 
unroll 3; (rcondt 3; first by auto).
unroll 5; (rcondt 5; first by auto).
unroll 7; (rcondt 7; first by auto).
rcondf 9; first by auto.
auto => /> &hr H0 H1 H2.
rewrite tP => j?.
rewrite !initiE // get8_set64_directE //.
case (24 <= j < 24 + 8) => ?.
  * rewrite bits8E wordP => k?.
    rewrite initiE //= /loadW8 /loadW64 pack8E initiE 1:/# /= initiE 1:/# /=; smt(@W64 pow2_64).
rewrite /get8/init8 initiE // initiE //= /set64_direct initiE //=.
case (16 <= j < 24) => ?.
  * rewrite bits8E wordP => k?.
    rewrite initiE //= /loadW8 /loadW64 pack8E initiE 1:/# /= initiE 1:/# /=; smt(@W64 pow2_64).
rewrite /get8/init8 initiE // initiE //= /set64_direct initiE //=.
case (8 <= j < 16) => ?.
  * rewrite bits8E wordP => k?.
    rewrite initiE //= /loadW8 /loadW64 pack8E initiE 1:/# /= initiE 1:/# /=; smt(@W64 pow2_64).
rewrite /get8/init8 initiE // initiE //= /set64_direct initiE //=.
rewrite ifT 1:/# bits8E //= /loadW8 wordP => k?.
rewrite initiE //= /loadW64 pack8E initiE 1:/# /= initiE /#.
qed.

lemma memcpy_ptr_ll :
    phoare [
      M(Syscall)._x_memcpy_u8u8p : 
      0 <= (to_uint arg.`2) + 32 <= W64.modulus /\
      0 <= to_uint arg.`2 
      ==>
      true
    ] = 1%r.
proof.
proc.
inline; wp; sp.
while (true) (32 - i); auto => /> /#. 
qed.

lemma p_memcpy_ptr_correct (ptr : W64.t):
    phoare [M(Syscall)._x_memcpy_u8u8p : 
      arg.`2 = ptr /\  
      0 <= (to_uint ptr) + 32 <= W64.modulus /\
      0 <= to_uint ptr ==>
        res = Array32.init (fun (i : int) => loadW8 Glob.mem (to_uint ptr + i))] = 1%r.
proof.
by conseq memcpy_ptr_ll (memcpy_ptr_correct ptr).
qed.

lemma _x_memcpy_u8u8_p (x : W8.t Array32.t) :
hoare [M(Syscall).memcpy_u8u8_N___x_memcpy_u8u8 : arg.`2 = x ==> res = x].
proof.
proc.
inline.
wp; sp.
while (
  0 <= to_uint i <= 32 /\ 
  (forall (k : int), 0 <= k < to_uint i => (out1.[k] = in_01.[k])) /\
  in_01 = x
).
    + auto => /> &hr H0 H1 H2 H3. 
      do split; 1,2: by smt(@W64).
      move => k??.
      rewrite get_setE 1:#smt:(@W64).
      case (k = to_uint i{hr}) => [/# | *].
      apply H2.
      smt(@W64).
    + skip => /> &hr.
      split => [/# | i0 out10 ???].
      have ->: to_uint i0 = 32 by smt(@W64 pow2_64).
      by rewrite tP.
qed.


lemma _x_memcpy_u8u8_post (x : W8.t Array32.t) :
    phoare [
        M(Syscall).memcpy_u8u8_N___x_memcpy_u8u8 : 
          arg.`2 = x ==> res = x] = 1%r
            by conseq _x_memcpy_u8u8_32_32_ll (_x_memcpy_u8u8_p x).

lemma _x_memcpy_u8u8_64_ (x : W8.t Array64.t) :
    hoare [M(Syscall).memcpy_u8u8_2N___x_memcpy_u8u8 : arg.`2 = x ==> res = x].
proof.
proc. 
inline; wp; sp. 
while (
  in_01 = x /\
  0 <= to_uint i <= 64 /\
  (forall (k : int), 0 <= k < to_uint i => (out1.[k] = x.[k]))
).
    + auto => /> &hr H0 H1 H2 H3.
      do split; 1,2: by smt(@W64). 
      move => k??. 
      rewrite get_setE 1:#smt:(@W64).
      case (k = to_uint i{hr}) => [/# | *].
      apply H2.
      smt(@W64).
    + auto => /> &hr.
      split => [/# | i0 out10 ???].
      have ->: to_uint i0 = 64 by smt(@W64 pow2_64).
      by rewrite tP.
qed.


lemma _x_memcpy_u8u8_64_post (x : W8.t Array64.t) :
    phoare [M(Syscall).memcpy_u8u8_2N___x_memcpy_u8u8 : arg.`2 = x ==> res = x] = 1%r
      by conseq _x_memcpy_u8u8_64_64_ll (_x_memcpy_u8u8_64_ x).


(******************************************************************************)
(******************               MEMCMP                          *************)
(******************************************************************************)

(* conseq is not working here so i wrote the proof twice *)
lemma p_memcmp_true (x y : W8.t Array32.t) :
        phoare[M(Syscall).__memcmp : x = y /\ arg = (x, y) ==> res = W8.zero] = 1%r.
proof.
proc.
while(0 <= to_uint i <= 32 /\ a = b /\ acc = W8.zero) (32 - to_uint i); auto => /> *; smt(@W64).
qed.

lemma p_memcmp_false (x y : W8.t Array32.t) :
        phoare[M(Syscall).__memcmp : x<>y /\ arg = (x, y) ==> res <> W8.zero] = 1%r.
proof.
have E : exists (i : int), 0 <= i < 32 => x.[i] <> y.[i] by smt(@Array32). 
proc.
while (
  #pre /\
  (exists (i : int), 0 <= i && i < 32 => x.[i] <> y.[i]) /\
  0 <= to_uint i <= 32 /\ 
  (acc = W8.zero <=> forall (k : int),  k < to_uint i => x.[k] = y.[k])
)
(32 - to_uint i). 
    + auto => /> &hr i0????H0. 
      rewrite ultE of_uintK (: 32 %% W64.modulus = 32) 1:/# => ?. 
      do split; 1,2: smt(@W64).       
         * move => ?. 
           have E1 : acc{hr} = W8.zero by smt(or_zero). 
           have E2 : x.[to_uint i{hr}] `^` y.[to_uint i{hr}] = W8.zero by smt(or_zero).
           have E3 : x.[to_uint i{hr}] = y.[to_uint i{hr}] by smt(xor_eq).
           have E4 : forall (k : int), 0 <= k && k < to_uint i{hr} => x.[k] = y.[k] by smt(). 
           rewrite to_uintD_small /#.
         * rewrite to_uintD_small 1:/# (: to_uint W64.one = 1) 1:/# => H.
           rewrite or_zero; split; [rewrite H0 | rewrite H ] => /#.
         * smt(@W64 pow2_64).
    + auto => /> *.
      split => [| ?i0]; first by smt(@Array32).
      rewrite ultE -lezNgt of_uintK //=; split => [|????? ->]; first by smt(@W64 pow2_64).
      have ->: to_uint i0 = 32 by smt(). 
      smt(@Array32). 
qed.

lemma memcpy_offset_1 (_offset_ : W64.t, _in_ : W8.t Array32.t) :
    phoare [
      M(Syscall).__memcpy_u8u8_offset : 
      arg.`2=_offset_ /\ 
      arg.`3=_in_ /\  
      0 <= to_uint _offset_ < (2144 - 32)
      ==>
      (forall (k : int), 0 <= k < 32 => (res.[to_uint _offset_ + k] = _in_.[k]))
    ] = 1%r.
proof.

conseq (: _ ==> sub res (to_uint _offset_) 32 = sub _in_ 0 32).
  + auto => /> &hr H0 H1 result.
    split => H.
        * apply (eq_from_nth witness); rewrite !size_sub // => j?.
          rewrite !nth_sub // /#.
        * move => k??.
          have ->: in_0{hr}.[k] = nth witness (sub in_0{hr} 0 32) k by rewrite nth_sub.
          by rewrite -H nth_sub.

proc => /=.

while (
  #{/~offset = _offset_}pre /\
  0 <= to_uint i <= 32 /\
  offset = _offset_ + i /\
  sub out (to_uint _offset_) (to_uint i) = sub _in_ 0 (to_uint i)  
)
(32 - to_uint i); last first.
    + auto => /> &hr H0 H1. 
      do split.
         - apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // /#.
         - move => i0 out0.
           split; rewrite ultE of_uintK /= => H2 H3 H4; first by smt().
           have ->: to_uint i0 = 32 by smt().
           by move => ->.
    + auto => /> &hr H0 H1 H2 H3 H4.
      rewrite ultE of_uintK /= => H5.
      do split. 
          - rewrite to_uintD /#.
          - rewrite to_uintD /#.
          - by ring.
          - apply (eq_from_nth witness); first by rewrite !size_sub to_uintD /#.
            rewrite size_sub to_uintD 1:/# /= => j?.
            rewrite !nth_sub //= get_setE //; [rewrite to_uintD /# |].
            case (j = to_uint i{hr}) => [-> |?].
                - by rewrite ifT // to_uintD /#.
                - rewrite ifF; first rewrite to_uintD /#.
                  have ->: _in_.[j] = nth witness (sub _in_ 0 (to_uint i{hr})) j by rewrite nth_sub // /#. 
                  rewrite -H4 nth_sub /#.
          - rewrite to_uintD /#.
qed.

(** ----------------- nbytes copy ------------------ **)

lemma nbytes_copy_64_32 (o : W8.t Array64.t, _in : W8.t Array32.t)  : 
    hoare[
      M(Syscall).memcpy_u8u8_2N_N____nbytes_copy_offset :
      arg = (o, W64.zero, _in, W64.zero) 
      ==> 
      sub res 0  32 = to_list _in /\
      sub res 32 32 = sub o 32 32 
    ].
proof.
proc => /=.
while (
  #{/~out = o}pre /\
  0 <= i <= 32 /\
  (forall (k : int), 0 <= k < i => out.[to_uint offset_out + k] = in_0.[to_uint offset_in + k]) /\
  (forall (k : int), 0 <= k < 32 => out.[32 + k] = o.[32 + k])
); last first.
    + auto => /> *.
      split => [/# | i????].
      have ->: i = 32 by smt(). 
      move => H0 H1.
      split.
         * apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
           rewrite size_sub // => j?.
           by rewrite nth_sub // get_to_list H0.
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => j?.
           by rewrite !nth_sub // H1.
auto => /> &hr ?? H0 H1 ?.
split => [/# |].
split => k??.
    + rewrite get_setE 1:#smt:(@W64 pow2_64).
      case (i{hr} = k) => H2; last first.
         * rewrite ifF; [ rewrite of_uintK |] => /#.
         * rewrite ifT; first by rewrite of_uintK /#.
           rewrite of_uintK H2 /#.
    + rewrite get_setE 1:#smt:(@W64 pow2_64).
      rewrite ifF; first by rewrite of_uintK /= /#.
      by apply H1.   
qed.

      
lemma nbytes_copy_64_32_ll : islossless M(Syscall).memcpy_u8u8_2N_N____nbytes_copy_offset
    by proc; while (true) (32 - i); auto => /> /#.

lemma nbytes_copy_64_32_p (o : W8.t Array64.t, _in : W8.t Array32.t)  : 
    phoare[
      M(Syscall).memcpy_u8u8_2N_N____nbytes_copy_offset :
      arg = (o, W64.zero, _in, W64.zero) 
      ==> 
      sub res 0  32 = to_list _in /\
      sub res 32 32 = sub o 32 32 
    ] = 1%r
        by conseq nbytes_copy_64_32_ll (nbytes_copy_64_32 o _in).

(* ================================================================================= *)

require import Array131.

lemma nbytes_copy_131_32 (o : W8.t Array131.t, _in : W8.t Array32.t)  : 
    hoare[
      M(Syscall).nbytes_copy_offset_sk____nbytes_copy_offset :
      arg = (o, (W64.of_int 67), _in, W64.zero) 
      ==> 
      sub res 67 32 = to_list _in /\
      sub res 0 67 = sub o 0 67 /\ 
      sub res 99 32 = sub o 99 32 
    ].
proof.
proc => /=.
while (
  #{/~out = o}pre /\
  0 <= i <= 32 /\
  (forall (k : int), 0 <= k < i => out.[67 + k] = in_0.[k]) /\
  sub out 0 67 = sub o 0 67 /\ 
  sub out 99 32 = sub o 99 32 
); last first.
    + auto => />; split => [/# | i out???].
      rewrite (: i = 32) 1:/# => H0 H1 H2.
      apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
      rewrite size_sub // => j?.
      rewrite nth_sub // H0 // get_to_list.

auto => /> &hr ??? H0  H1*; split => [/# |].
do split.
    + move => k??.
      rewrite get_setE; [rewrite of_uintK /# |].
      case (k = i{hr}) => [-> | ?].
          * rewrite ifT; rewrite of_uintK /#.
          * rewrite ifF; [rewrite of_uintK /# | smt()]. 
    + apply (eq_from_nth witness); first by rewrite !size_sub.
      rewrite size_sub // => j?.
      rewrite nth_sub //.
      rewrite get_setE; [rewrite of_uintK /# |].
      rewrite ifF; [rewrite of_uintK /# |].
      have ->: out{hr}.[0 + j] = nth witness (sub out{hr} 0 67) j by rewrite nth_sub.
      congr; apply H0.     
    + apply (eq_from_nth witness); first by rewrite !size_sub.
      rewrite size_sub // => j?.
      rewrite nth_sub //.
      rewrite get_setE; [rewrite of_uintK /# |].
      rewrite ifF; [rewrite of_uintK /# |].
      have ->: out{hr}.[99 + j] = nth witness (sub out{hr} 99 32) j by rewrite nth_sub.
      congr; apply H1.
qed.
      
lemma nbytes_copy_131_32_ll : islossless M(Syscall).nbytes_copy_offset_sk____nbytes_copy_offset
    by proc; while (true) (32 - i); auto => /> /#.

lemma nbytes_copy_131_32_p (o : W8.t Array131.t, _in : W8.t Array32.t)  : 
    phoare[
      M(Syscall).nbytes_copy_offset_sk____nbytes_copy_offset :
      arg = (o, W64.of_int 67, _in, W64.zero) 
      ==> 
      sub res 67 32 = to_list _in /\
      sub res 0 67 = sub o 0 67 /\ 
      sub res 99 32 = sub o 99 32 
    ] = 1%r
        by conseq nbytes_copy_131_32_ll (nbytes_copy_131_32 o _in).
 
 (* ================================================================================= *)

lemma memcpy_u8u8_2_64_352_post (o : W8.t Array64.t) (_in : W8.t Array352.t) (off : W64.t):
    phoare [
       M(Syscall).memcpy_u8u8_2_treehash____memcpy_u8u8_2 :
       arg = (o, _in, off, W64.of_int 64) /\
       0 <= to_uint off < 353 - 64      
       ==>
       to_list res.`1 = sub _in (to_uint off) 64
       ] = 1%r.
proof.
proc => /=.
conseq (: _ ==>
  forall (k : int), 0 <= k < 64 => out.[k] = _in.[to_uint off + k]
).
- auto => /> ?? out0; split => [H k?? | H].
    + have ->: out0.[k] = nth witness (to_list out0) k by rewrite get_to_list.
      by rewrite H nth_sub.
    + apply (eq_from_nth witness); first by rewrite size_to_list size_sub.  
      rewrite size_to_list => j?.
      by rewrite get_to_list H // nth_sub.

while (
  in_0 = _in /\ 
  in_offset = off + i /\
  bytes = (of_int 64)%W64 /\
  0 <= to_uint i <= 64 /\
  0 <= to_uint off < 289 /\
  forall (k : int), 0 <= k && k < to_uint i => out.[k] = _in.[to_uint off + k]
)
(64 - to_uint i); last first.     

- auto => /> ??.
  split => [/# |].
  move => i0 out0.
  split; by rewrite ultE /#.

- auto => /> &hr H0 H1 H2 H3 H4.
  rewrite ultE to_uintD_small 1:/# of_uintK /= => H5.
  do split; 2,3,5: by smt().
  * ring.
  * move => k??.
    rewrite get_setE 1:/#.
    case (k = to_uint i{hr}) => [-> | /#].
    by congr; rewrite to_uintD_small //#.
qed.

