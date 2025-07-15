pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList.
from Jasmin require import JModel JArray.

require import BitEncoding.
(*---*) import BitChunking.

require import StdBigop. 
(*---*) import Bigint.

require import Params XMSS_MT_Params Types XMSS_MT_Types Address Hash BaseW WOTS LTree XMSS_MT_TreeHash XMSS_MT_PRF.
require import XMSS_IMPL Parameters.
require import Repr Utils.

import AuthPath.

require import Array4 Array8 Array11 Array32 Array131 Array320 Array352 Array2144 Array2464.

require import Correctness_Address.
require import Correctness_WOTS.
require import Correctness_Mem.
require import Correctness_TreehashCondition.
require import TreeHashProof.

require import WArray32.

lemma lsb_even_64 (w : W64.t) : 
    to_uint w %% 2 = 0 => w.[0] = false.
proof.
move => ?.
rewrite get_to_uint (: (0 <= 0 && 0 < 64)) //= /#.
qed.

lemma W64_oneE : 
    forall (k : int), 0 < k < 64 => W64.onew.[k] = true by smt(onewE). 


lemma onew_one_64 k:
    0 < k < 64 => W64.onew.[k] = !W64.one.[k].
 proof.
move=>i.
rewrite /W64.onew.
rewrite !get_to_uint (: 0 <= k < 64) 1:/# /=. 
case (k = 1) => [-> //=|?]; 
case (k = 2) => [-> //=|?]; 
case (k = 3) => [-> //=|?]; 
case (k = 4) => [-> //=|?]; 
case (k = 5) => [-> //=|?]; 
case (k = 6) => [-> //=|?]; 
case (k = 7) => [-> //=|?]; 
case (k = 8) => [-> //=|?]; 
case (k = 9) => [-> //=|?]; 
case (k = 10) => [-> //=|?]; 
case (k = 11) => [-> //=|?]; 
case (k = 12) => [-> //=|?]; 
case (k = 13) => [-> //=|?]; 
case (k = 14) => [-> //=|?]; 
case (k = 15) => [-> //=|?]; 
case (k = 16) => [-> //=|?]; 
case (k = 17) => [-> //=|?]; 
case (k = 18) => [-> //=|?]; 
case (k = 19) => [-> //=|?]; 
case (k = 20) => [-> //=|?]; 
case (k = 21) => [-> //=|?]; 
case (k = 22) => [-> //=|?]; 
case (k = 23) => [-> //=|?]; 
case (k = 24) => [-> //=|?]; 
case (k = 25) => [-> //=|?]; 
case (k = 26) => [-> //=|?]; 
case (k = 27) => [-> //=|?]; 
case (k = 28) => [-> //=|?]; 
case (k = 29) => [-> //=|?]; 
case (k = 30) => [-> //=|?]; 
case (k = 31) => [-> //=|?]; 
case (k = 32) => [-> //=|?]; 
case (k = 33) => [-> //=|?]; 
case (k = 34) => [-> //=|?]; 
case (k = 35) => [-> //=|?]; 
case (k = 36) => [-> //=|?]; 
case (k = 37) => [-> //=|?]; 
case (k = 38) => [-> //=|?]; 
case (k = 39) => [-> //=|?]; 
case (k = 40) => [-> //=|?]; 
case (k = 41) => [-> //=|?]; 
case (k = 42) => [-> //=|?]; 
case (k = 43) => [-> //=|?]; 
case (k = 44) => [-> //=|?]; 
case (k = 45) => [-> //=|?]; 
case (k = 46) => [-> //=|?]; 
case (k = 47) => [-> //=|?]; 
case (k = 48) => [-> //=|?]; 
case (k = 49) => [-> //=|?]; 
case (k = 50) => [-> //=|?]; 
case (k = 51) => [-> //=|?]; 
case (k = 52) => [-> //=|?]; 
case (k = 53) => [-> //=|?]; 
case (k = 54) => [-> //=|?]; 
case (k = 55) => [-> //=|?]; 
case (k = 56) => [-> //=|?]; 
case (k = 57) => [-> //=|?]; 
case (k = 58) => [-> //=|?]; 
case (k = 59) => [-> //=|?]; 
case (k = 60) => [-> //=|?]; 
case (k = 61) => [-> //=|?]; 
case (k = 62) => [-> //=|?]; 
case (k = 63) => [-> //=|/#].
qed.

lemma xor1_even_64 (x : W64.t) :
    0 <= to_uint x <= W64.max_uint => 
    to_uint x %% 2 = 0 => 
    x `^` W64.one = x + W64.one.
proof.
move => /= ??.
have w0E : x.[0] = false by apply lsb_even_64.
rewrite wordP => j?.
rewrite xorwE.
have E0: W64.one.[0] by rewrite /W64.one bits2wE initiE //= /int2bs nth_mkseq.
case (j = 0) => [-> | ?].
  + rewrite E0 /=.
    rewrite eq_sym !get_to_uint.
    rewrite (: (0 <= 0 && 0 < 32)) 1:/# /=.
    rewrite to_uintD_small 1:/# /= /#.
rewrite eq_sym get_to_uint.
have E: (0 <= j && j < 64) by smt().
rewrite to_uintD_small 1:/# E /=.
rewrite get_to_uint E /=.
have ->: 2^j = 2 * 2^(j - 1) by rewrite -exprS 1:/#. 
rewrite !divzMr 1?IntOrder.expr_ge0 ~-1://; 1,2: smt(@IntDiv).
rewrite divzDl //.
rewrite/(^^) /=.
rewrite -onew_one_64 1:/# W64_oneE /#.
qed.

lemma xor1_odd_64 (x : W64.t) :
    0 <= to_uint x <= W64.max_uint => 
    to_uint x %% 2 <> 0 => 
    (x `^` W64.one) = x - W64.one.
proof.
move => /= ??.
have E0: W64.one.[0] by rewrite /W64.one bits2wE initiE //= /int2bs nth_mkseq.
rewrite wordP => i?.
rewrite xorwE.
case (i = 0) => [-> | ?]; [rewrite E0 |] => /=. 
  + rewrite !get_to_uint (: (0 <= 0 && 0 < 32)) 1:/# /=.
    rewrite to_uintB 2:/# uleE /#.
rewrite/(^^) /=.
rewrite -onew_one_64 1:/# W64_oneE 1:/# /=.
rewrite !get_to_uint (: (0 <= i && i < 64)) 1:/# /=.
rewrite to_uintB /=; first by rewrite uleE /#.
have ->: 2^i = 2 * 2^(i - 1) by rewrite -exprS 1:/#. 
rewrite !divzMr 1?IntOrder.expr_ge0 ~-1://; 1,2: smt(@IntDiv).
smt(@IntDiv).
qed.

lemma build_auth_path_correct (_pub_seed _sk_seed : W8.t Array32.t, _idx : W32.t, a1 a2 : adrs) :
    n = XMSS_N /\
    d = XMSS_D /\
    h = XMSS_FULL_HEIGHT /\
    h %/ d = XMSS_TREE_HEIGHT /\
    w = XMSS_WOTS_W /\
    len = XMSS_WOTS_LEN /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    prf_kg_padding_val = XMSS_HASH_PADDING_PRF_KEYGEN /\
    padding_len = XMSS_PADDING_LEN /\ F_padding_val = XMSS_HASH_PADDING_F =>
    equiv[
      M(Syscall).__build_auth_path ~ TreeSig.buildAuthPath :
      arg{1}.`2 = _sk_seed /\
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = _idx /\
      arg{1}.`5 = a1 /\

      arg{2}.`1 = NBytes.insubd (to_list _pub_seed) /\
      arg{2}.`2 = NBytes.insubd (to_list _sk_seed) /\
      arg{2}.`3 = _idx /\
      arg{2}.`4 = a2 /\

      a1.[4] = W32.zero /\

      sub a1 0 3 = sub a2 0 3 /\

      0 <= to_uint _idx < 2 ^ XMSS_FULL_HEIGHT
      ==>
      res{2} = EncodeAuthPath (to_list res{1})
    ].
proof. 
rewrite /XMSS_WOTS_LEN /XMSS_N /XMSS_D /XMSS_FULL_HEIGHT /XMSS_TREE_HEIGHT => [#] n_val d_val h_val *.
proc => /=.
seq 1 3 : (
  #pre /\ 
  j{2} = to_uint j{1} /\ to_uint j{1} = 0 /\ 
  size authentication_path{2} = h %/ d
); first by auto => />; rewrite size_nseq /#.

conseq (
:  _ ==> 
  to_list auth_path{1} = nbytes_flatten authentication_path{2} /\
  size authentication_path{2} = h %/ d 
).
- auto => /> &1 &2 H0 H1 H2 H3 H4 H5 authPathL authPathR H6 H7.
      apply auth_path_eq.
      rewrite insubdK //.
      rewrite /EncodeAuthPath insubdK.
         * rewrite /P size_map n_val size_chunk // size_to_list  /#.
      apply (eq_from_nth witness).
         * rewrite n_val size_map size_chunk // size_to_list /#.
      rewrite H7 d_val h_val /= => j?.
      rewrite (nth_map witness).
         * rewrite n_val size_chunk // size_to_list /#.      
      rewrite /chunk nth_mkseq /=.
         * rewrite size_to_list /#.        
      apply nbytes_eq.
      rewrite NBytes.insubdK.
         * rewrite n_val /P size_take // size_drop 1:/# size_to_list /#.
      apply (eq_from_nth witness).
         * rewrite NBytes.valP n_val size_take // size_drop 1:/# size_to_list /#. 
      rewrite NBytes.valP n_val => i?.
      rewrite nth_take // 1:/# nth_drop 1,2:/# H6 nth_nbytes_flatten /#.
    
 
conseq ( :
  to_list sk_seed{1} = NBytes.val sk_seed{2} /\
  to_list pub_seed{1} = NBytes.val pub_seed{2} /\
  sub addr{1} 0 3 = sub address{2} 0 3 /\
  addr{1}.[4] = W32.zero /\
  j{2} = to_uint j{1} /\ to_uint j{1} = 0 /\
  i{1} = idx{2} /\ 
  0 <= to_uint idx{2} < 2 ^ XMSS_FULL_HEIGHT /\
  size authentication_path{2} = h %/ d 
  ==> 
  _
).
    + auto => /> *; split.
        * apply (eq_from_nth witness); first by rewrite NBytes.valP size_to_list n_val.
          rewrite size_to_list => j?.
          by rewrite NBytes.insubdK // /P size_to_list n_val.
        * apply (eq_from_nth witness); first by rewrite NBytes.valP size_to_list n_val.
          rewrite size_to_list => j?.
          by rewrite NBytes.insubdK // /P size_to_list n_val.
 
while (
  to_list sk_seed{1} = NBytes.val sk_seed{2} /\
  to_list pub_seed{1} = NBytes.val pub_seed{2} /\
  sub addr{1} 0 3 = sub address{2} 0 3 /\
  i{1} = idx{2} /\
  j{2} = to_uint j{1} /\ 0 <= j{2} <= h %/ d /\ 
  size authentication_path{2} = h %/ d /\
  
  addr{1}.[4] = W32.zero /\

  (0 <= to_uint idx{2} < 2 ^ XMSS_FULL_HEIGHT) /\

  forall (k : int), 0 <= k < n * to_uint j{1} => auth_path{1}.[k] = nth witness (nbytes_flatten authentication_path{2}) k
); last first.
    + auto => /> &1 &2 *.
      rewrite ultE; split => [/# | authL jL authR].
      rewrite ultE of_uintK /= => ?_ ???H.
      apply (eq_from_nth witness); rewrite ?size_to_list ?size_nbytes_flatten /#.

seq 2 0 : (#pre /\ to_uint k{1} = to_uint (i{1} `>>` truncateu8 j{1})).
- auto => /> &1 &2; rewrite ultE of_uintK /XMSS_FULL_HEIGHT /= => *. 
  rewrite to_uint_shr to_uint_truncateu8 (: 63 = 2^6 - 1) 1:/# ?and_mod //= of_uintK 1:/#.
  rewrite of_uintK to_uint_shr to_uint_truncateu8 /#.

seq 1 1 : (
    #{/~to_uint k{1} = to_uint (i{1} `>>` truncateu8 j{1})}pre /\
    to_uint k{1} = k{2} /\
    k{2} = to_uint ((idx{2} `>>` (of_int j{2})%W8) `^` W32.one) /\
    0 <= k{2} < 1048576
). 
- auto => /> &1 &2; rewrite ultE of_uintK /= => H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12*.
  rewrite /XMSS_FULL_HEIGHT /= in H8.
  pose X := (idx{2} `>>` (of_int (to_uint j{1}))%W8).
  have E1 : 0 <= to_uint idx{2} < 1048576 by smt().
  have E2 : 0 <= to_uint (idx{2} `>>` (of_int (to_uint j{1}))%W8) < 1048576 by rewrite to_uint_shr of_uintK //= 1:/#; smt(@IntDiv).
  have := E2; rewrite to_uint_shr of_uintK 1:/# (: (to_uint j{1} %% W8.modulus) = to_uint j{1}) 1:/# => T.
  case (to_uint X %% 2 = 0) => [Heven | Hodd]; [rewrite xor1_even // 1:/# xor1_even_64 1,2:/# | rewrite xor1_odd // 1:/# xor1_odd_64 1,2:/#].
        * have := Heven; rewrite /X  to_uint_shr of_uintK 1:/# (: (to_uint j{1} %% W8.modulus) = to_uint j{1}) 1:/# => Teven.
          rewrite !to_uintD !to_uint_shr !of_uintK 1:/# (: (to_uint j{1} %% W8.modulus) = to_uint j{1}) 1:/# /=; do split => [| /# | /#]. 
          have ->: (to_uint idx{2} %/ 2 ^ to_uint j{1} + 1) %% 4294967296 = (to_uint idx{2} %/ 2 ^ to_uint j{1} + 1) by smt(). 
          have ->: k{1} = zeroextu64 (idx{2} `>>` truncateu8 j{1}).
             - rewrite wordP => i?.
               by rewrite !get_to_uint (: 0 <= i < 64) //= to_uint_zeroextu64 to_uint_shr to_uint_truncateu8 1:/# H12 to_uint_shr to_uint_truncateu8 1:/#.
         rewrite ?to_uint_zeroextu64 ?to_uint_shr ?to_uint_truncateu8 /= /#.
       * rewrite !to_uintB ?uleE /#.

seq 1 0 : (
  #{/~to_uint k{1} = k{2}}pre /\
  to_uint k{1} = k{2} * 2^j{2}
).
- auto => /> &1 &2 *.
  rewrite to_uint_shl of_uintK 1:/# /=.
  rewrite (: 63 = 2^6 - 1) 1:/# and_mod // of_uintK.
  case (to_uint j{1} = 0) => [-> /# | ?]; case (to_uint j{1} = 1) => [-> /# | ?]; case (to_uint j{1} = 2) => [-> /# | ?]; case (to_uint j{1} = 3) => [-> /# | ?];
  case (to_uint j{1} = 4) => [-> /# | ?]; case (to_uint j{1} = 5) => [-> /# | ?]; case (to_uint j{1} = 6) => [-> /# | ?]; case (to_uint j{1} = 7) => [-> /# | ?];
  case (to_uint j{1} = 8) => [-> /# | ?]; case (to_uint j{1} = 9) => [-> /# | /#].

rcondt {1} 1; 1:auto.

conseq /> => [/# |]. 
 
seq 6 1 : (
    #pre /\ 
    to_list (Array32.init (fun (i_0 : int) => auth_path{1}.[to_uint subarray_start_index{1} + i_0])) = NBytes.val t{2} /\
    to_uint subarray_start_index{1} = n * to_uint j{1}
).  
    + wp; sp. 
      exists * pub_seed{1}, sk_seed{1}, k{1}, j32{1}, addr{1}, address{2}.
      elim * => P0 P1 P2 P3 P4 P5.
      call {1} (treehash_correct P1 P0 (truncateu32 P2) P3 P4 P5) => [/# |].  
      skip => /> &1 &2 ; rewrite ultE of_uintK /= => -> -> H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
      rewrite /XMSS_FULL_HEIGHT /= in H8.  
      rewrite !NBytes.valKd /= !to_uint_truncateu32 /=; do split; 2..4: by smt().
           - pose X := (idx{2} `>>` W8.of_int (to_uint j{1})).
             case (to_uint X %% 2 = 0) => [Heven | Hodd].
                   * have := Heven; rewrite /X to_uint_shr of_uintK 1:/# (:to_uint j{1} %% W8.modulus = to_uint j{1}) 1:/# => Teven.
                     rewrite H14 xor1_even; 1,2: rewrite to_uint_shr of_uintK 1:/#.
                          - case (to_uint j{1} = 0) => [-> /# | ?]; case (to_uint j{1} = 1) => [-> /# | ?]; case (to_uint j{1} = 2) => [-> /# | ?]; 
                            case (to_uint j{1} = 3) => [-> /# | ?]; case (to_uint j{1} = 4) => [-> /# | ?]; case (to_uint j{1} = 5) => [-> /# | ?]; 
                            case (to_uint j{1} = 6) => [-> /# | ?]; case (to_uint j{1} = 7) => [-> /# | ?]; case (to_uint j{1} = 8) => [-> /# | ?]; 
                            case (to_uint j{1} = 9) => [-> /# | /#].  
                          - smt().
                    rewrite to_uintD of_uintK to_uint_shr of_uintK 1:/#. 
                    case (to_uint j{1} = 0) => [-> /# | ?]; case (to_uint j{1} = 1) => [-> /# | ?]; case (to_uint j{1} = 2) => [-> /# | ?]; 
                    case (to_uint j{1} = 3) => [-> /# | ?]; case (to_uint j{1} = 4) => [-> /# | ?]; case (to_uint j{1} = 5) => [-> /# | ?]; 
                    case (to_uint j{1} = 6) => [-> /# | ?]; case (to_uint j{1} = 7) => [-> /# | ?]; case (to_uint j{1} = 8) => [-> /# | ?]; 
                    case (to_uint j{1} = 9) => [-> /# | /#].  

                   * have := Hodd; rewrite /X to_uint_shr of_uintK 1:/# (:to_uint j{1} %% W8.modulus = to_uint j{1}) 1:/# => Todd.
                     rewrite H14 xor1_odd; 1,2: rewrite to_uint_shr of_uintK 1:/#.
                          - case (to_uint j{1} = 0) => [-> /# | ?]; case (to_uint j{1} = 1) => [-> /# | ?]; case (to_uint j{1} = 2) => [-> /# | ?]; 
                            case (to_uint j{1} = 3) => [-> /# | ?]; case (to_uint j{1} = 4) => [-> /# | ?]; case (to_uint j{1} = 5) => [-> /# | ?]; 
                            case (to_uint j{1} = 6) => [-> /# | ?]; case (to_uint j{1} = 7) => [-> /# | ?]; case (to_uint j{1} = 8) => [-> /# | ?]; 
                            case (to_uint j{1} = 9) => [-> /# | /#].  
                          - smt().
                    rewrite to_uintB /=; first by rewrite uleE to_uint_shr of_uintK 1:/#; smt(@W32 pow2_32 @IntDiv).
                    have E: to_uint ((idx{2} `>>` W8.of_int (to_uint j{1})) `^` W32.one) = (to_uint (idx{2} `>>` W8.of_int (to_uint j{1})) - 1).
                          - rewrite xor1_odd.
                             + rewrite to_uint_shr of_uintK 1:/#.
                               case (to_uint j{1} = 0) => [-> /# | ?]; case (to_uint j{1} = 1) => [-> /# | ?]; case (to_uint j{1} = 2) => [-> /# | ?]; 
                               case (to_uint j{1} = 3) => [-> /# | ?]; case (to_uint j{1} = 4) => [-> /# | ?]; case (to_uint j{1} = 5) => [-> /# | ?]; 
                               case (to_uint j{1} = 6) => [-> /# | ?]; case (to_uint j{1} = 7) => [-> /# | ?]; case (to_uint j{1} = 8) => [-> /# | ?]; 
                               case (to_uint j{1} = 9) => [-> /# | /#].  
                             + rewrite to_uint_shr of_uintK 1:/# (: to_uint j{1} %% W8.modulus = to_uint j{1}) 1:/#; assumption.
                            rewrite to_uintB; first by rewrite uleE to_uint_shr of_uintK 1:/# of_uintK; smt(@W32 pow2_32 @IntDiv).
                            by [].
                    have := H12; have := H13; rewrite E !to_uint_shr of_uintK 1:/# (: to_uint j{1} %% W8.modulus = to_uint j{1}) /#. 


           - case (to_uint j{1} = 0) => [-> /# | ?]; case (to_uint j{1} = 1) => [-> /# | ?]; case (to_uint j{1} = 2) => [-> /# | ?]; 
             case (to_uint j{1} = 3) => [-> /# | ?]; case (to_uint j{1} = 4) => [-> /# | ?]; case (to_uint j{1} = 5) => [-> /# | ?]; 
             case (to_uint j{1} = 6) => [-> /# | ?]; case (to_uint j{1} = 7) => [-> /# | ?]; case (to_uint j{1} = 8) => [-> /# | ?]; 
             case (to_uint j{1} = 9) => [-> /# | /#].


           - rewrite H14.
             pose X := (idx{2} `>>` (truncateu8 j{1})%W8); case (to_uint X %% 2 = 0) => [Heven | Hodd].

                   * have Teven: to_uint ((idx{2} `>>` W8.of_int (to_uint j{1})) `^` W32.one) = to_uint ((idx{2} `>>` W8.of_int (to_uint j{1})) + W32.one).
                       + rewrite xor1_even // to_uint_shr of_uintK 1:/#.
                         case (to_uint j{1} = 0) => [-> /# | ?]; case (to_uint j{1} = 1) => [-> /# | ?]; case (to_uint j{1} = 2) => [-> /# | ?]; 
                         case (to_uint j{1} = 3) => [-> /# | ?]; case (to_uint j{1} = 4) => [-> /# | ?]; case (to_uint j{1} = 5) => [-> /# | ?]; 
                         case (to_uint j{1} = 6) => [-> /# | ?]; case (to_uint j{1} = 7) => [-> /# | ?]; case (to_uint j{1} = 8) => [-> /# | ?]; 
                         case (to_uint j{1} = 9) => [-> /# | /#].
                     rewrite xor1_even.
                       + rewrite to_uint_shr of_uintK 1:/#.
                         case (to_uint j{1} = 0) => [-> /# | ?]; case (to_uint j{1} = 1) => [-> /# | ?]; case (to_uint j{1} = 2) => [-> /# | ?]; 
                         case (to_uint j{1} = 3) => [-> /# | ?]; case (to_uint j{1} = 4) => [-> /# | ?]; case (to_uint j{1} = 5) => [-> /# | ?]; 
                         case (to_uint j{1} = 6) => [-> /# | ?]; case (to_uint j{1} = 7) => [-> /# | ?]; case (to_uint j{1} = 8) => [-> /# | ?]; 
                         case (to_uint j{1} = 9) => [-> /# | /#]. 
                       + rewrite to_uint_shr of_uintK 1:/#.
                       + have := Heven; rewrite /X to_uint_shr of_uintK /#. 
                       + have := Heven; rewrite /X to_uint_shr of_uintK 1:/# => F.
                         rewrite to_uintD to_uint_shr of_uintK /= 1:/#.
                         case (to_uint j{1} = 0) => [-> /# | ?]; case (to_uint j{1} = 1) => [-> /# | ?]; case (to_uint j{1} = 2) => [-> /# | ?]; 
                         case (to_uint j{1} = 3) => [-> /# | ?]; case (to_uint j{1} = 4) => [-> /# | ?]; case (to_uint j{1} = 5) => [-> /# | ?]; 
                         case (to_uint j{1} = 6) => [-> /# | ?]; case (to_uint j{1} = 7) => [-> /# | ?]; case (to_uint j{1} = 8) => [-> /# | ?]; 
                         case (to_uint j{1} = 9) => [-> /# | /#]. 

                   * have Todd: to_uint ((idx{2} `>>` W8.of_int (to_uint j{1})) `^` W32.one) = to_uint ((idx{2} `>>` W8.of_int (to_uint j{1})) - W32.one). 
                       + rewrite xor1_odd // to_uint_shr of_uintK 1:/#.
                         case (to_uint j{1} = 0) => [-> /# | ?]; case (to_uint j{1} = 1) => [-> /# | ?]; case (to_uint j{1} = 2) => [-> /# | ?]; 
                         case (to_uint j{1} = 3) => [-> /# | ?]; case (to_uint j{1} = 4) => [-> /# | ?]; case (to_uint j{1} = 5) => [-> /# | ?]; 
                         case (to_uint j{1} = 6) => [-> /# | ?]; case (to_uint j{1} = 7) => [-> /# | ?]; case (to_uint j{1} = 8) => [-> /# | ?]; 
                         case (to_uint j{1} = 9) => [-> /# | /#].

                     rewrite (: to_uint j{1} %% 4294967296 = to_uint j{1}) 1:/#.
                     rewrite xor1_odd.
                       + rewrite to_uint_shr of_uintK 1:/#.
                         case (to_uint j{1} = 0) => [-> /# | ?]; case (to_uint j{1} = 1) => [-> /# | ?]; case (to_uint j{1} = 2) => [-> /# | ?]; 
                         case (to_uint j{1} = 3) => [-> /# | ?]; case (to_uint j{1} = 4) => [-> /# | ?]; case (to_uint j{1} = 5) => [-> /# | ?]; 
                         case (to_uint j{1} = 6) => [-> /# | ?]; case (to_uint j{1} = 7) => [-> /# | ?]; case (to_uint j{1} = 8) => [-> /# | ?]; 
                         case (to_uint j{1} = 9) => [-> /# | /#]. 
                       + rewrite to_uint_shr of_uintK 1:/#.
                         have := Hodd; rewrite /X to_uint_shr of_uintK /#. 
                     rewrite to_uintB; first by rewrite uleE to_uint_shr of_uintK 1:/# of_uintK (: (to_uint j{1} %% W8.modulus) = to_uint j{1}) 1:/#; smt(@W32 pow2_32 @IntDiv).
                     have := H13; have := H12.
                     rewrite Todd !to_uint_shr !of_uintK 1:/# to_uintB.
                               - rewrite uleE to_uint_shr of_uintK 1:/# of_uintK (: (to_uint j{1} %% W8.modulus) = to_uint j{1}) 1:/#; smt(@W32 pow2_32 @IntDiv).
                     rewrite !to_uint_shr !of_uintK (: to_uint j{1} %% W8.modulus = to_uint j{1}) 1..3:/# /=. 
                     case (to_uint j{1} = 0) => [-> /# | ?]; case (to_uint j{1} = 1) => [-> /# | ?]; case (to_uint j{1} = 2) => [-> /# | ?]; 
                     case (to_uint j{1} = 3) => [-> /# | ?]; case (to_uint j{1} = 4) => [-> /# | ?]; case (to_uint j{1} = 5) => [-> /# | ?]; 
                     case (to_uint j{1} = 6) => [-> /# | ?]; case (to_uint j{1} = 7) => [-> /# | ?]; case (to_uint j{1} = 8) => [-> /# | ?]; 
                     case (to_uint j{1} = 9) => [-> /# | /#]. 

       - move => H15 H16 H17 H18 H19 H20 H21 resL resR <-; do split.
          * rewrite n_val /= => k??.
            by rewrite initiE 1:/# /= H9 1:/# ifF; first by rewrite to_uint_shl of_uintK /#.
          * congr; rewrite tP => k?.
            rewrite initiE 1:/# /= initiE /=; first by rewrite to_uint_shl of_uintK /#.
            rewrite ifT; first by rewrite to_uint_shl of_uintK /#.
            by congr; ring.
          * rewrite to_uint_shl of_uintK /#.


auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15*; rewrite size_put ultE to_uintD of_uintK; do split; 1..4,6,7: by smt().
have ->: n * ((to_uint j{1} + 1 %% W64.modulus) %% W64.modulus) = n * (to_uint j{1} + 1) by smt().
move => k??.
rewrite nth_nbytes_flatten; first by rewrite size_put /#.
rewrite nth_put 1:/#.
case (to_uint j{1} = k %/ n) => ?.
- rewrite -H15 get_to_list initiE 1:/# /= /#.
- rewrite H9 1:/# nth_nbytes_flatten /#.
qed.


lemma treesig_correct (_m : W8.t Array32.t, _sk : xmss_sk, _idx_sig : W32.t)
                      (a1 a2 : W32.t Array8.t) :
    n = XMSS_N /\
    d = XMSS_D /\
    h = XMSS_FULL_HEIGHT /\
    h %/ d = XMSS_TREE_HEIGHT /\
    w = XMSS_WOTS_W /\
    len = XMSS_WOTS_LEN /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    prf_kg_padding_val = XMSS_HASH_PADDING_PRF_KEYGEN /\
    padding_len = XMSS_PADDING_LEN /\ 
    F_padding_val = XMSS_HASH_PADDING_F /\
    floor (log2 w%r) = XMSS_WOTS_LOG_W /\ 
    len1 = XMSS_WOTS_LEN1 /\
    len2 = XMSS_WOTS_LEN2 => 
    equiv [
      M(Syscall).__tree_sig ~ TreeSig.treesig:
      arg{1}.`2 = _m /\
      arg{1}.`3 = DecodeSkNoOID _sk /\
      arg{1}.`4 = _idx_sig /\
      arg{1}.`5 = a1 /\
      
      arg{2}.`1 = NBytes.insubd (to_list _m) /\
      arg{2}.`2 = _sk /\
      arg{2}.`3 = _idx_sig /\
      arg{2}.`4 = a2 /\

      sub a1 0 3 = sub a2 0 3 /\

      0 <= to_uint _idx_sig < 2 ^ XMSS_FULL_HEIGHT

      ==>
      res{2} = EncodeReducedSignature (to_list res{1}.`1) /\
      sub res{1}.`2 0 3 = sub a1 0 3 
    ].
proof.
rewrite /XMSS_WOTS_LEN /XMSS_N /XMSS_D /XMSS_FULL_HEIGHT => [#] n_val d_val h_val *.
proc => /=.
seq 8 0 : (
  #pre /\
  to_list pub_seed{1} = sub sk{1} (XMSS_INDEX_BYTES + 3*32) 32 /\
  to_list sk_seed{1} = sub sk{1} XMSS_INDEX_BYTES 32
); first  by auto => /> *; split; apply (eq_from_nth witness); rewrite size_to_list ?size_sub // => i?; rewrite get_to_list initiE // nth_sub.

seq 1 0 : (
  #{/~addr{1} = a1}pre /\
  addr{1}.[4] = W32.zero /\
  sub addr{1} 0 3 = sub a1 0 3
).
    + auto => /> *; apply (eq_from_nth witness); rewrite !size_sub // => *.
      rewrite !nth_sub // get_setE // ifF 1:/#; smt(sub_k).

seq 0 2 : (
  #pre /\
  NBytes.val sk_seed{2} = to_list sk_seed{1} /\
  NBytes.val pub_seed{2} = to_list pub_seed{1}
).
    + auto => /> &1 ??? -> -> *; split; rewrite /DecodeSkNoOID.
       * apply (eq_from_nth witness); first by rewrite NBytes.valP size_sub.
         rewrite NBytes.valP n_val => i?.
         rewrite nth_sub // get_of_list 1:/#.
         rewrite nth_cat ifT.
             - rewrite !size_cat !NBytes.valP n_val size_EncodeIdx /#. 
         rewrite nth_cat ifT.
             - rewrite !size_cat !NBytes.valP n_val size_EncodeIdx /#. 
         rewrite nth_cat ifT.
             - rewrite !size_cat NBytes.valP n_val size_EncodeIdx /#.
         rewrite nth_cat ifF size_EncodeIdx /#.
       * apply (eq_from_nth witness); first by rewrite NBytes.valP n_val size_sub.
         rewrite NBytes.valP n_val => i?.
         rewrite nth_sub // get_of_list 1:/# nth_cat ifF.
             - rewrite !size_cat !NBytes.valP n_val size_EncodeIdx /#.
         rewrite !size_cat !NBytes.valP n_val size_EncodeIdx. 
         congr => /#.
 
(* Rewrite #pre *)
conseq (:
  M{2} = (NBytes.insubd (to_list m{1}))%NBytes /\
  idx{2} = idx_sig{1} /\
  sub address{2} 0 3 = sub addr{1} 0 3 /\
  NBytes.val sk_seed{2} = to_list sk_seed{1} /\
  NBytes.val pub_seed{2} = to_list pub_seed{1} /\
  addr{1}.[4] = W32.zero /\
  sub addr{1} 0 3 = sub a1 0 3 /\
  0 <= to_uint idx_sig{1} < 2 ^ XMSS_FULL_HEIGHT 
  ==>
  _
); first by auto => /> *; apply (eq_from_nth witness); rewrite !size_sub // => j?; rewrite !nth_sub //; smt(sub_k).
 
seq 1 1 : (#pre /\ auth{2} = EncodeAuthPath (to_list auth_path{1})).
    + exists * pub_seed{1}, sk_seed{1}, idx_sig{1}, addr{1}, address{2}.
      elim * => P0 P1 P2 P3 P4.
      call (build_auth_path_correct P0 P1 P2 P3 P4) => [/# |].
      skip => /> &2 <- <- <- ???? //=; by rewrite !NBytes.valKd.
   
seq 2 2 : (
    #{/~addr{1}.[4] = W32.zero}pre /\
    sub addr{1} 0 5 = sub address{2} 0 5
).
    + inline {1}; auto => /> &1 &2 *.
      rewrite /set_type /set_ots_addr; do split; apply (eq_from_nth witness); rewrite !size_sub // => j?; rewrite !nth_sub // !get_setE //; smt(sub_k).
 
seq 1 1 : ( 
  sub addr{1} 0 3 = sub a1 0 3 /\
  sig_ots{2} = EncodeWotsSignature sig_ots{1} /\ 
  auth{2} = EncodeAuthPath (to_list auth_path{1})
).
    + sp; wp.
      exists * m{1}, sk_seed{1}, pub_seed{1}, addr{1}, address{2}.
      elim * => P0 P1 P2 P3 P4.
      call {1} (wots_sign_seed_addr P0 P1 P2 P3 P4).
      (do split; 3: by rewrite /log_w (: w = XMSS_WOTS_W) 1:/# /XMSS_WOTS_W /XMSS_WOTS_LOG_W) => /#.
      skip => /> &1 &2 H0 <- <- H1 H2 *; rewrite !NBytes.valKd /= NBytes.insubdK /P // ?size_to_list ?n_val //= => *.
      apply (eq_from_nth witness); rewrite !size_sub // => ??; rewrite !nth_sub //; smt(sub_k).

auto => /> &1 H; rewrite /EncodeReducedSignature ?encodewotssig_list_array; do 2! congr; 
apply (eq_from_nth witness); 1,3: (by rewrite size_to_list size_sub_list /#); 
rewrite size_to_list => i?; rewrite get_to_list nth_sub_list 1:/# /= initiE 1:/# /=;
[rewrite ifF 1:/# initiE | rewrite ifT] => /#.
qed.
