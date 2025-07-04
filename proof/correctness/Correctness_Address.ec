pragma Goals : printall.

require import AllCore List Distr RealExp IntDiv.

from Jasmin require import JModel.

require import BitEncoding.
(*---*) import BitChunking.
(*---*) import StdBigop.Bigint.
(*---*) import W4u8.Pack.

require import Array4 Array8 Array32.
require import WArray4 WArray32.

require import Params Address Repr Utils Bytes.
require import XMSS_IMPL.

lemma in_nth ['a] (x : 'a list) (P : 'a -> bool) :
    (forall (x0 : 'a ), x0 \in x => P x0) <=>
    forall (k : int), 0 <= k < size x => P (nth witness x k).
proof.
split ; smt(@List). (* Without the split, smt doesnt work *)
qed.

lemma zero_addr_res (address : adrs) :
    phoare[M(Syscall)._zero_address : true ==> res = zero_addr] = 1%r.
proof.
proc.
unroll for 2; auto => /> &hr; rewrite tP => i?. 
rewrite initiE //= !set64E zero_addr_i //= get32E pack4E /= wordP => k?. 
rewrite initiE //=; do (rewrite initiE 1:/# /=); rewrite bits8E.
case (24 <= 4 * i + k %/ 8 < 32) => H; first by rewrite initiE 1:/#.
rewrite get32E pack4E bits8E; do (rewrite initiE 1:/# /=); rewrite bits8E.
case (
    16 <=
    4 * ((4 * i + k %/ 8) %/ 4) + ((4 * i + k %/ 8) %% 4 * 8 + k %% 8) %/ 8 <
    24
) => ?; first by rewrite initiE 1:/#.
rewrite get32E pack4E bits8E; do (rewrite initiE 1:/# /=); rewrite bits8E.
case (
8 <=
    4 *
    ((4 * ((4 * i + k %/ 8) %/ 4) + ((4 * i + k %/ 8) %% 4 * 8 + k %% 8) %/ 8) %/
     4) +
    ((4 * ((4 * i + k %/ 8) %/ 4) + ((4 * i + k %/ 8) %% 4 * 8 + k %% 8) %/ 8) %%
     4 * 8 + ((4 * i + k %/ 8) %% 4 * 8 + k %% 8) %% 8) %/
    8 < 16
) =>?; first by rewrite initiE 1:/#.
rewrite get32E pack4E bits8E; do (rewrite initiE 1:/# /=); rewrite bits8E ifT 1:/# initiE /#.
qed.

lemma u32_to_bytes_correct (x : W32.t) :
    phoare [
      M(Syscall).__u32_to_bytes : 
      arg.`2 = x 
      ==>  
      to_list res = W32toBytes x
    ] = 1%r.
proof.
proc.
auto => /> &hr.
apply (eq_from_nth witness).
  + by rewrite size_to_list size_rev size_to_list.
rewrite size_to_list // => i?.
rewrite !get_to_list initiE //.
rewrite /get8 /set32_direct initiE //= ifT 1:/# bits8E /=.
rewrite wordP => j?.
rewrite initiE //= /BSWAP_32 /(\o) pack4E initiE 1:/# /= get_of_list 1:/#.
rewrite nth_rev.
  + rewrite size_to_list /#.
congr => [| /#].
rewrite !get_to_list !size_to_list.
rewrite nth_rev.
  + rewrite size_to_list /#.
rewrite size_to_list.
rewrite /to_list nth_mkseq 1:/# /=.
congr => /#.
qed.

lemma addr_to_bytes_correctness (x : W32.t Array8.t) : 
    n = 32 =>
    phoare[
        M(Syscall).__addr_to_bytes : 
        arg.`2 = x 
        ==> 
        to_list res = flatten (map W32toBytes (to_list x))
] = 1%r.
proof.
move => n_val.
proc.
sp.
while ( 
  addr = x /\
  0 <= to_uint i <= 8 /\
  sub addr_as_bytes 0 (4 * to_uint i) = 
  sub_list (flatten (map W32toBytes (to_list x))) 0 (4 * to_uint i)
)
(8 - to_uint i); auto => /> *; last first.
- split => [| addr_as_bytes i].
   + apply (eq_from_nth witness); rewrite size_sub // ?size_sub_list /#.
  rewrite ultE; split => [/# |]. 
  rewrite of_uintK /= => H0 H1 H2.
  have ->: to_uint i = 8 by smt().
  simplify; move => H3.
  apply (eq_from_nth witness); rewrite size_to_list => [| j?].
   + rewrite size_flatten sumzE BIA.big_map /(\o) //=.
     rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 4)) /=; last by rewrite big_constz count_predT size_map size_to_list /#.
     rewrite in_nth size_map size_to_list /= => j?.
     rewrite (nth_map witness); first by rewrite size_to_list /#.
     rewrite /W32toBytes size_rev /#.
  rewrite get_to_list.
  have ->: addr_as_bytes.[j] =nth witness (sub addr_as_bytes 0 32) j by rewrite nth_sub /#.
  by rewrite H3 nth_sub_list.
- exists * addr.[to_uint i]; elim * => P; call (u32_to_bytes_correct P).
  (auto => /> &hr; rewrite ultE of_uintK /= => H0 H1 H2 H3 result Hr *; do split; rewrite to_uintD /= => *; 1,4: by smt()); first by smt(@W64).
  apply (eq_from_nth witness); first by rewrite size_sub_list 1:/# size_sub 1,2:/#.
  rewrite size_sub 1:/# => j?.
  rewrite nth_sub_list 1:/# (nth_flatten witness 4).
       + pose X := (fun (s : W8.t list) => size s = 4).
         pose Y := (map W32toBytes (to_list x)).
         rewrite -(all_nthP X Y witness) /X /Y size_map => k?. 
         by rewrite (nth_map witness) // /W32toBytes size_rev size_to_list.
  rewrite nth_sub 1:/# initiE 1:/#.
  rewrite (nth_map witness); first by rewrite size_to_list /#.
  rewrite /W32toBytes nth_rev; first by rewrite size_to_list /#.
  rewrite get_to_list size_to_list /to_list nth_mkseq 1:/# /=.
  case (4 * to_uint i{hr} <= j < 4 * to_uint i{hr} + 4) => ?; rewrite !to_uint_shl !of_uintK //=; [rewrite ifT 1:/# | rewrite ifF 1:/#].
       + have ->: result.[j - to_uint i{hr} * 4 %% 18446744073709551616] = nth witness (to_list result) (j - to_uint i{hr} * 4 %% 18446744073709551616) by done.
         rewrite Hr /W32toBytes nth_rev; first by rewrite size_to_list /#.
         rewrite size_to_list /to_list nth_mkseq 1:/# /= /#.  
       + have ->: addr_as_bytes{hr}.[j] = nth witness (sub addr_as_bytes{hr} 0 (4 * to_uint i{hr})) j by rewrite nth_sub /#.
         rewrite H2 nth_sub_list 1:/# (nth_flatten witness 4).
           * pose X := (fun (s : W8.t list) => size s = 4).
             pose Y := (map W32toBytes (to_list x)).
             rewrite -(all_nthP X Y witness) /X /Y size_map => k?. 
             by rewrite (nth_map witness) // /W32toBytes size_rev size_to_list.
         rewrite (nth_map witness); first by rewrite size_to_list /#.
         rewrite /W32toBytes nth_rev; first by rewrite size_to_list /#.
         by rewrite get_to_list size_to_list /to_list nth_mkseq 1:/# /=.
qed.
