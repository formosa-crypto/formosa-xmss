pragma Goals : printall.

require import AllCore List RealExp IntDiv.

require import Address.
import BitEncoding.BitChunking.

from Jasmin require import JModel.

require import XMSS_IMPL Parameters.
require import Params Address BaseW Hash LTree Bytes.
require import Correctness_Bytes Correctness_Mem Correctness_Address.
require import Utils Repr.

require import Array4 Array8 Array32 Array64 Array96 Array128.

require import WArray32 WArray64.

(*---*) import StdBigop.Bigint.

axiom hash_96 (x : W8.t Array96.t) :
  phoare[
      M(Syscall).hash_plen_2n____sha256 : 
      arg.`2 = x 
      ==>  
      to_list res = NBytes.val (Hash (to_list x))
    ] = 1%r.

axiom hash_96_ (x : W8.t Array96.t) :
  phoare[M(Syscall).hash_plen_n_32____sha256 : arg.`2 = x ==> to_list res = NBytes.val (Hash (to_list x))] = 1%r.

axiom hash_128 (x : W8.t Array128.t) :
  phoare[
      M(Syscall).hash_plen_2n_32____sha256 : 
      arg.`2 = x 
      ==> 
      to_list res = NBytes.val (Hash (to_list x))
    ] = 1%r.

axiom hash_128_ (x : W8.t Array128.t) :
  phoare[
      M(Syscall).hash_plen_3n____sha256 : 
      arg.`2 = x 
      ==> 
      to_list res = NBytes.val (Hash (to_list x))
    ] = 1%r.

axiom hash_ptr_ll (ptr len : W64.t) :
  phoare[
      M(Syscall).__core_hash_in_ptr_ :
      valid_ptr_i ptr (to_uint len) 
      ==>
      true
    ]= 1%r.

axiom hash_ptr_correct (ptr len : W64.t) :
  phoare[
      M(Syscall).__core_hash_in_ptr_ :
      valid_ptr_i ptr (to_uint len) /\
      arg.`2 = ptr /\
      arg.`3 = len 
      ==>
      to_list res = NBytes.val (Hash (load_buf Glob.mem ptr (to_uint len)))
  ] = 1%r.

lemma size_toByte_64 w l : 
    0 <= l =>
    size (toByte_64 w l) = l.
proof.
by move => ?; rewrite /toByte_64 size_rev size_mkseq /#.
qed.

lemma prf_correctness (a b : W8.t Array32.t) :
    n = XMSS_N /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\ 
    padding_len = XMSS_PADDING_LEN =>
    equiv [
    M(Syscall).__prf ~ Hash.prf : 
    arg{1}.`2 = a /\ 
    arg{1}.`3 = b /\ 
    arg{2} = (NBytes.insubd (to_list a), NBytes.insubd (to_list b)) 
    ==>
    NBytes.val res{2} = to_list res{1}
    ].
proof.
rewrite /XMSS_N /XMSS_HASH_PADDING_PRF /XMSS_PADDING_LEN => [#] n_val pval plen.
proc => /=.
seq 7 2 : (buf{2} = to_list buf{1}); last by ecall {1} (hash_96_ buf{1}); auto => /> /#.
seq 3 0 : #pre; 1:auto. 
seq 1 1 : (#pre /\ padding{2} = to_list padding_buf{1}).
  + outline {1} [1] { padding_buf <@ M(Syscall).bytes_32__ull_to_bytes (padding_buf, W64.of_int 3); }.
    call {1} (ull_to_bytes_32_correct (of_int 3)%W64). 
    auto => /> ? ->. 
    by rewrite /toByte_64 /W64toBytes_ext pval plen.

seq 1 0 : (
  NBytes.val key{2} = to_list key{1} /\
  NBytes.val in_0{2} = to_list in_0{1} /\
  padding{2} = to_list padding_buf{1} /\ 
  forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k
).
    + auto => /> &1; do split; 1,2: by rewrite NBytes.insubdK /P //= size_to_list n_val.  
      move => k??.
      rewrite initiE 1:/# => />.  
      by rewrite ifT. 

auto => /> &1 &2 H0 H1 H2 *; apply (eq_from_nth witness); rewrite !size_cat !size_to_list !NBytes.valP n_val //= => j?.

case (0 <= j < 32).
    + move => ?.
      rewrite nth_cat size_cat !size_to_list NBytes.valP ifT 1:/# nth_cat !size_to_list ifT 1:/# get_to_list. 
      by rewrite -H2 // initiE //= ifF 1:/# initiE //= ifF 1:/#.

case (32 <= j < 64).
    + move => ?_.
      rewrite nth_cat size_cat !size_to_list NBytes.valP n_val //= ifT 1:/#.
      rewrite nth_cat size_to_list ifF 1:/#.
      by rewrite H0 get_to_list initiE //= ifF 1:/# initiE //= ifT 1:/# /copy_8. 
move => ??.
rewrite nth_cat size_cat !size_to_list NBytes.valP ifF 1:/# H1 get_to_list initiE //= ifT 1:/# //=.
rewrite initiE 1:/# /get8 /init64 /= /copy_64 initiE 1:/# /=.
rewrite initiE 1:/# /=.
rewrite bits8E wordP => i?.
rewrite initiE //=.
rewrite/init8 get64E pack8E //= initiE 1:/# /= initiE 1:/# /= initiE /#.
qed.

lemma prf_keygen_correctness (a : W8.t Array64.t, b : W8.t Array32.t) :
    n = XMSS_N /\
    prf_kg_padding_val = XMSS_HASH_PADDING_PRF_KEYGEN /\ 
    padding_len = XMSS_PADDING_LEN =>
    equiv [
      M(Syscall).__prf_keygen ~ Hash.prf_keygen : 
      arg{1}.`2 = a /\ 
      arg{1}.`3 = b /\ 
      arg{2} = (to_list a, NBytes.insubd (to_list b))
      ==>
      NBytes.val res{2} = to_list res{1}
    ].
proof.
rewrite /XMSS_N /XMSS_HASH_PADDING_PRF_KEYGEN /XMSS_PADDING_LEN => [#] n_val pval plen.
proc => //=.
seq 7 2 : (buf{2} = to_list buf{1}); last by ecall {1} (hash_128 buf{1}); auto => /> /#.

seq 3 0 : #pre; 1:auto.

seq 1 1 : (#pre /\ padding{2} = to_list padding_buf{1}).
  + outline {1} [1] { padding_buf <@ M(Syscall).bytes_32__ull_to_bytes (padding_buf, W64.of_int 4); }.
    call {1} (ull_to_bytes_32_correct (of_int 4)%W64). 
    auto => /> ? ->. 
    by rewrite /toByte_64 /W64toBytes_ext pval plen.

seq 1 0 : (
  NBytes.val key{2} = to_list key{1} /\
  in_0{2} = to_list in_0{1} /\
  padding{2} = to_list padding_buf{1} /\ 
  forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k
).
    + auto => /> &1; split.
         * rewrite NBytes.insubdK // /P size_to_list n_val //.
         * move => k??.
           rewrite initiE 1:/# => />. 
           by rewrite ifT.

auto => /> &1 &2 H0 H1; apply (eq_from_nth witness); rewrite !size_cat H0 !size_to_list //= => i?.
case (0 <= i < 32).
    + move => ?.
      rewrite nth_cat !size_cat !size_to_list ifT 1:/#.
      by rewrite nth_cat !size_to_list //= ifT 1:/# initiE //= ifF 1:/# initiE //= ifF 1:/# H1.
case (32 <= i < 64). 
    + move => ?_.
      rewrite nth_cat !size_cat !size_to_list //= ifT 1:/#.
      rewrite nth_cat !size_to_list //= ifF 1:/#.
      rewrite initiE //= ifF 1:/# initiE /#.
move => ??.
rewrite nth_cat !size_cat !size_to_list //= ifF 1:/# initiE //= ifT 1:/#.
rewrite initiE 1:/# /get8 initiE 1:/# /= /copy_64 initiE 1:/# /= bits8E /= wordP => j?.
rewrite initiE //= get64E pack8E initiE 1:/# /= initiE 1:/# /= initiE /#.
qed.

op merge_nbytes_to_array (a b : nbytes) : W8.t Array64.t = 
  Array64.init (fun i => if 0 <= i < 32 
                         then nth witness (NBytes.val a) i 
                         else nth witness (NBytes.val b) (i - 32)).

lemma rand_hash_results (i0 i1: nbytes, _pub_seed : W8.t Array32.t) (a1 a2 : W32.t Array8.t) :
    padding_len = XMSS_PADDING_LEN /\ 
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    padding_len = XMSS_PADDING_LEN /\ 
    n = XMSS_N  =>
    equiv [
      M(Syscall).__thash_h ~ Hash.rand_hash :
      arg{1}.`2 = (merge_nbytes_to_array i0 i1) /\
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = a1 /\

      arg{2}.`1 = i0 /\
      arg{2}.`2 = i1 /\
      arg{2}.`3 = NBytes.insubd(to_list _pub_seed) /\
      arg{2}.`4 = a2 /\
      
      forall (k : int), 0 <= k < 7 => a1.[k] = a2.[k] (* Os addresses so precisam de coincidir nos primeiros 6 indices *)
      ==>
      to_list res{1}.`1 = NBytes.val res{2} /\
      forall (k : int), 0 <= k < 7 => res{1}.`2.[k] = a1.[k] (* Os addresses so precisam de coincidir nos primeiros 6 indices *)
    ].
proof.
rewrite /XMSS_PADDING_LEN /XMSS_HASH_PADDING_PRF /XMSS_PADDING_LEN /XMSS_N => [#] plen pval pprfval nval.
proc => /=.

seq 3 0 : #pre; first by auto. 

seq 1 1 : (#pre /\ padding{2} = to_list aux{1} /\ size padding{2} = 32).
  + outline {1} [1] { aux <@ M(Syscall).bytes_32__ull_to_bytes (Array32.init (fun (i_0 : int) => buf.[0 + i_0]), W64.one); }.
    call {1} (ull_to_bytes_32_correct (of_int 1)%W64). 
    auto => /> ??->; smt(W64toBytes_ext_toByte_64 size_toByte_64).

swap {1} [2..3] -1.

seq 1 1 :( 
  addr{1} = address{2} /\
  sub addr{1} 0 7 = sub a1 0 7 /\
  to_list in_0{1} = (NBytes.val _left{2}) ++ (NBytes.val _right{2}) /\
  NBytes.val _seed{2} = to_list pub_seed{1} /\ 
  padding{2} = to_list aux{1} /\   
  size padding{2} = 32
).
    + inline {1}.
      auto => /> &1 ?_.
      do split.
          * rewrite /set_key_and_mask tP => j?.
            case (j = 7) => [-> | ?].
               - rewrite get_setE //.
               - rewrite !get_setE // !ifF /#.
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => i?.
           by rewrite !nth_sub //= get_setE // ifF 1:/#.
         * apply (eq_from_nth witness); first by rewrite size_to_list size_cat !NBytes.valP nval.
           rewrite size_to_list => j?. 
           rewrite get_to_list /merge_nbytes_to_array initiE 1:/# => />. 
           case (0 <= j < 32) => ?. 
             - by rewrite nth_cat NBytes.valP nval ifT 1:/#.
           by rewrite nth_cat NBytes.valP nval ifF 1:/#. 
         * by rewrite NBytes.insubdK //= /P size_to_list nval.


seq 1 1 : (#pre /\ NBytes.val addr_bytes{2} = to_list addr_as_bytes{1}).
    + inline {1} M(Syscall).__set_key_and_mask.
      exists * addr{1}; elim * => P.
      call {1} (addr_to_bytes_correctness P).
      auto => /> &1 &2 ????? ->.
      apply (eq_from_nth witness).
          * rewrite NBytes.valP size_flatten sumzE BIA.big_map /(\o) //=.
            rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 4)) /=; last first.
                +  rewrite big_constz count_predT size_map size_to_list /#.
            rewrite in_nth size_map size_to_list /= => j?.
            rewrite (nth_map witness); first by rewrite size_to_list /#.
            rewrite /W32toBytes size_rev; first by rewrite size_to_list /#.
      rewrite NBytes.valP nval => j?.
      rewrite /addr_to_bytes => />.
      rewrite NBytes.insubdK /= 2:/# /P size_flatten sumzE BIA.big_map /(\o) //=.
      rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 4)) /=; last first.
          * rewrite big_constz count_predT size_map size_to_list /#.
      rewrite in_nth size_map size_to_list /= => ??.
      rewrite (nth_map witness); first by rewrite size_to_list /#.
      rewrite /W32toBytes size_rev; first by rewrite size_to_list /#.

seq 1 0 : (
  #pre /\
  forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k
); first by auto => /> *; rewrite initE ifT 1:/#; auto => /> /#.

seq 1 1 : (
  #{/~padding{2} = to_list aux{1}}pre /\ 
  NBytes.val key{2} = to_list aux{1} 
).
    + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
      exists * in_01{1}, key0{1}; elim * => _P1 _P2.
      call {1} (prf_correctness _P1 _P2) => [/# |].  
      skip => /> &1 &2 ?? <- ? <- ?.
      smt(@NBytes).

seq 11 6 : ( 
  addr{1} = address{2} /\
  sub addr{1} 0 7 = sub a1 0 7 /\
  to_list buf{1} = padding{2} ++ (NBytes.val key{2}) ++ bytexor ((NBytes.val _left{2}) ++ (NBytes.val _right{2})) ((NBytes.val bitmask_0{2}) ++ (NBytes.val bitmask_1{2}))
); last first. 
    + wp. 
      ecall {1} (hash_128_ buf{1}). 
      auto => /> &1 &2 ??? ->. 
      split; last by smt(sub_k).
      apply nbytes_eq.
      by congr.

seq 1 0 : (
    #pre /\
    forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = nth witness (NBytes.val key{2}) k
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 ->. 
      split => k??; rewrite initiE 1:/# /=; [by rewrite ifF /# | by rewrite ifT 1:/#]. 

seq 1 1 : #pre.
    + inline {1}; auto => /> *; apply (eq_from_nth witness); rewrite !size_sub // => j?; rewrite !nth_sub //= get_setE //; smt(sub_k).
       

seq 1 1 : (
  sub addr{1} 0 7 = sub a1 0 7 /\
  to_list in_0{1} = NBytes.val _left{2} ++ NBytes.val _right{2} /\
  NBytes.val _seed{2} = to_list pub_seed{1} /\
  address{2} = addr{1} /\
  NBytes.val addr_bytes{2} = to_list addr_as_bytes{1} /\
  size padding{2} = 32 /\
  NBytes.val key{2} = to_list aux{1} /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = nth witness (NBytes.val key{2}) k)
).
    + inline {1} M(Syscall).__set_key_and_mask.
      exists * addr{1}; elim * => P.
      call {1} (addr_to_bytes_correctness P).
      auto => /> &1 &2 ?????????->.
      apply (eq_from_nth witness).
          - rewrite NBytes.valP size_flatten sumzE BIA.big_map /(\o) //=.
            rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 4)) /=; last first.
                *  rewrite big_constz count_predT size_map size_to_list /#.
            rewrite in_nth size_map size_to_list /= => j?.
            rewrite (nth_map witness); first by rewrite size_to_list /#.
            rewrite /W32toBytes size_rev; first by rewrite size_to_list /#.
      rewrite NBytes.valP nval => j?.
      rewrite /addr_to_bytes => />. 
      rewrite NBytes.insubdK /= 2:/# /P size_flatten sumzE BIA.big_map /(\o) //=.
      rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 4)) /=; last first.
          - rewrite big_constz count_predT size_map size_to_list /#.
      rewrite in_nth size_map size_to_list /= => ??.
      rewrite (nth_map witness); first by rewrite size_to_list /#.
      rewrite /W32toBytes size_rev; first by rewrite size_to_list /#.

seq 2 1 : (
  to_list in_0{1} = NBytes.val _left{2} ++ NBytes.val _right{2} /\
  NBytes.val _seed{2} = to_list pub_seed{1} /\ 
  address{2} = addr{1} /\
  NBytes.val addr_bytes{2} = to_list addr_as_bytes{1} /\
  size padding{2} = 32 /\
  (forall (k : int), 0 <= k < 32 => bitmask{1}.[k] = nth witness (NBytes.val bitmask_0{2}) k) /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = nth witness (NBytes.val key{2}) k) /\ 
  sub addr{1} 0 7 = sub a1 0 7
).
    + inline {1} M(Syscall).__prf_ M(Syscall)._prf.
      wp; sp.
      exists * in_01{1}, key0{1}.
      elim * => _P1 _P2.
      call {1} (prf_correctness _P1 _P2) => [/# |]. 
      skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7. 
      split; [rewrite -H3 #smt:(@NBytes) |]. 
      move => ???? -> ???. 
      by rewrite initE ifT 1:/# /= ifT.

seq 1 1 : #pre.
    + inline {1}; auto => /> *; apply (eq_from_nth witness); rewrite !size_sub // => j?; rewrite !nth_sub //= get_setE //; smt(sub_k).

seq 1 1 : (
  to_list in_0{1} = NBytes.val _left{2} ++ NBytes.val _right{2} /\
  NBytes.val _seed{2} = to_list pub_seed{1} /\
  address{2} = addr{1} /\
  NBytes.val addr_bytes{2} = to_list addr_as_bytes{1} /\
  size padding{2} = 32 /\
  (forall (k : int), 0 <= k < 32 => bitmask{1}.[k] = nth witness (NBytes.val bitmask_0{2}) k) /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = nth witness (NBytes.val key{2}) k) /\
  sub addr{1} 0 7 = sub a1 0 7
).
    + exists * addr{1}; elim * => P.
      call {1} (addr_to_bytes_correctness P).
      auto => /> &1 &2 ????????? ->.
      apply (eq_from_nth witness).
          * rewrite NBytes.valP size_flatten sumzE BIA.big_map /(\o) //=.
            rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 4)) /=; last first.
                +  rewrite big_constz count_predT size_map size_to_list /#.
            rewrite in_nth size_map size_to_list /= => j?.
            rewrite (nth_map witness); first by rewrite size_to_list /#.
            rewrite /W32toBytes size_rev; first by rewrite size_to_list /#.
      rewrite NBytes.valP nval => j?.
      rewrite /addr_to_bytes => />.
      rewrite NBytes.insubdK /= 2:/# /P size_flatten sumzE BIA.big_map /(\o) //=.
      rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 4)) /=; last first.
          * rewrite big_constz count_predT size_map size_to_list /#.
      rewrite in_nth size_map size_to_list /= => ??.
      rewrite (nth_map witness); first by rewrite size_to_list /#.
      rewrite /W32toBytes size_rev; first by rewrite size_to_list /#.

seq 2 1 : (
  #pre /\ 
  (forall (k : int), 0 <= k < 32 => bitmask{1}.[32 + k] = nth witness (NBytes.val bitmask_1{2}) k)
). 
    + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
      exists * in_01{1}, key0{1}; elim * => _P1 _P2; call {1} (prf_correctness _P1 _P2) => [/# |].
      skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7. 
      do split.
         * rewrite -H2 #smt:(@NBytes). 
         * rewrite -H1 #smt:(@NBytes). 
         * move => H8 H9 resultL resultR ->.
           split => k??; rewrite initiE 1:/# /=; [by rewrite ifF 1:/# H4 | by rewrite ifT 1:/# ].

conseq (: _ ==>
  size padding{2} = 32 /\
  addr{1} = address{2} /\ 
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = nth witness (NBytes.val key{2}) k) /\
  (forall (k : int), 0 <= k < 64 => buf{1}.[64 + k] = nth witness (bytexor (NBytes.val _left{2} ++ NBytes.val _right{2}) (NBytes.val bitmask_0{2} ++ NBytes.val bitmask_1{2})) k) /\
  sub addr{1} 0 7 = sub a1 0 7
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 bufL H9 H10 H11. 
      apply (eq_from_nth witness); first by rewrite !size_cat H3 /bytexor !size_map size_zip !size_cat !NBytes.valP size_iota nval //=.
      rewrite size_to_list => i?.
      rewrite get_to_list.
      case (0 <= i < 32) => ?.
        * by rewrite nth_cat size_cat H3 NBytes.valP nval /= ifT 1:/# nth_cat H3 ifT 1:/# H9.
      case (32 <= i < 64) => ?.
        * rewrite nth_cat size_cat NBytes.valP H3 nval /= ifT 1:/# nth_cat ifF /#. 
          rewrite nth_cat size_cat NBytes.valP H3 nval /= ifF 1:/# -H11 /#.

while {1}
( 
  0 <= to_uint i{1} <= 64 /\
  size padding{2} = 32 /\ 
  addr{1} = address{2} /\
  sub addr{1} 0 7 = sub a1 0 7 /\
  to_list in_0{1} = NBytes.val _left{2} ++ NBytes.val _right{2} /\
  to_list bitmask{1} = NBytes.val bitmask_0{2} ++ NBytes.val bitmask_1{2} /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = nth witness (NBytes.val key{2}) k) /\
  (forall (k : int), 0 <= k < to_uint i{1} => 
    buf{1}.[64 + k] = 
      nth witness (NBytes.val _left{2} ++ NBytes.val _right{2}) (k) `^` nth witness (NBytes.val bitmask_0{2} ++ NBytes.val bitmask_1{2}) (k))
) 
(64 - to_uint i{1}).
  + auto => /> &hr H0 H1 H2 H3 H4 H5 H6 H7 H8 H9. 
    do split.
       - rewrite to_uintD_small /#.
       - smt(@W64 pow2_64).
       - move => k??.
         rewrite get_setE 1:#smt:(@W64) ifF 1:#smt:(@W64 pow2_64) /#.       
       - move => k??.
         rewrite get_setE 1:#smt:(@W64) ifF 1:#smt:(@W64 pow2_64) /#.       
       - move => k??.
         rewrite to_uintD_small 1:/# of_uintK /=. 
         have E0: forall (k : int), 0 <= k < 32 => in_0{hr}.[k] = nth witness (NBytes.val _left{m}) k by smt(@List @Array64 @NBytes). 
         have E1: forall (k : int), 0 <= k < 32 => in_0{hr}.[32 + k] = nth witness (NBytes.val _right{m}) k by smt(@List @Array64 @NBytes). 
         have E2: forall (k : int), 0 <= k < 32 => bitmask{hr}.[k] = nth witness (NBytes.val bitmask_0{m}) k by smt(@List @Array64 @NBytes). 
         have E3: forall (k : int), 0 <= k < 32 => bitmask{hr}.[32 + k] = nth witness (NBytes.val bitmask_1{m}) k by smt(@List @Array64 @NBytes).
         rewrite get_setE 1:#smt:(@W64).
         case (64 + k = 64 + to_uint i{hr}) => ?; last by apply H8; smt(@W64 pow2_64).
         congr; [smt(@List @Array64) |].
         rewrite nth_cat NBytes.valP nval.
         case (0 <= k < 32) => ?.
            * rewrite ifT /#.
            * rewrite ifF 1:/# -E3 #smt:(@W64 pow2_64).
       - rewrite to_uintD /#.
  + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8. 
    do split; 2: by smt().
       - apply (eq_from_nth witness); first by rewrite size_to_list size_cat !NBytes.valP nval. 
         rewrite size_to_list => i?.
         rewrite get_to_list nth_cat NBytes.valP nval.
         case (0 <= i < 32) => ?; [rewrite ifT | rewrite ifF] => /#.
       - move => bufL iL. 
         split; first by rewrite ultE /#.
         rewrite ultE => H9 H10 H11 H12 H13 H14 H15 k??.
         rewrite H15 1:#smt:(@W64 pow2_64) /bytexor. 
         case (0 <= k < 32) => ?.
             - rewrite !nth_cat !NBytes.valP ifT 1:/# ifT 1:/# (nth_map witness) /=.
                 * rewrite size_zip !size_cat !NBytes.valP /#.
               have ->: (nth witness (zip (NBytes.val _left{2} ++ NBytes.val _right{2}) (NBytes.val bitmask_0{2} ++ NBytes.val bitmask_1{2})) k).`1 = nth witness (NBytes.val _left{2} ++ NBytes.val _right{2}) k by smt(@List @NBytes). 
               have ->: (nth witness (zip (NBytes.val _left{2} ++ NBytes.val _right{2}) (NBytes.val bitmask_0{2} ++ NBytes.val bitmask_1{2})) k).`2 = nth witness (NBytes.val bitmask_0{2} ++ NBytes.val bitmask_1{2}) k by smt(@List @NBytes). 
               rewrite nth_cat NBytes.valP ifT 1:/#.
               congr.
               by rewrite nth_cat NBytes.valP ifT 1:/#.
         rewrite (nth_map witness) .
               - rewrite size_zip !size_cat !NBytes.valP /#.
         rewrite nth_cat NBytes.valP ifF 1:/#.
         rewrite nth_cat NBytes.valP ifF 1:/# /=.
         have ->: (nth witness (zip (NBytes.val _left{2} ++ NBytes.val _right{2}) (NBytes.val bitmask_0{2} ++ NBytes.val bitmask_1{2})) k).`1 = nth witness (NBytes.val _left{2} ++ NBytes.val _right{2}) k by smt(@List @NBytes). 
         have ->: (nth witness (zip (NBytes.val _left{2} ++ NBytes.val _right{2}) (NBytes.val bitmask_0{2} ++ NBytes.val bitmask_1{2})) k).`2 = nth witness (NBytes.val bitmask_0{2} ++ NBytes.val bitmask_1{2}) k by smt(@List @NBytes). 
         congr; rewrite nth_cat NBytes.valP nval ifF /#.
qed.


(* OBS: proving correctness for mhash is now an equiv instead of a phoare *)
module M_Hash = {
  proc hash (t : threen_bytes, M : W8.t list) : nbytes = {
    var padding : W8.t list <- toByte_64 H_msg_padding_val n;
    var r : nbytes <- (Hash (padding ++ ThreeNBytesBytes.val t ++ M));    
    return r;
  }
}.

require import Bytes.

lemma p_write_buf_ptr mem (ptr o : W64.t) (buf : W8.t Array32.t) :
    phoare [
      M(Syscall).memcpy_u8pu8_n____memcpy_u8pu8 :
      0 <= to_uint ptr + to_uint o + 32 < W64.max_uint /\
      Glob.mem = mem /\ 
      arg = (ptr, o, buf)  

      ==>
      
      res.`1 = ptr /\ (* No fim, o apontaodor aponta para o mm sitio *)

      load_buf Glob.mem (ptr + o) 32 = to_list buf /\

      (* O resto da memoria fica igual *)
      forall (k : int), 0 <= k < W64.max_uint => 
         !(to_uint ptr + to_uint o <= k < to_uint ptr + to_uint o + 32) => 
             Glob.mem.[k] = mem.[k]
    ] = 1%r.
proof.
proc => /=.
while (
  0 <= to_uint ptr + to_uint o + 32 < W64.max_uint /\ 
  out = ptr  /\
  offset = o + i /\
  in_0 = buf /\ 
  
  0 <= to_uint i <= 32 /\

  load_buf Glob.mem (ptr + o) (to_uint i) = sub buf 0 (to_uint i) /\
  
  forall (k : int),
    0 <= k < W64.max_uint  =>
      ! (to_uint ptr + to_uint o <= k < to_uint ptr + to_uint o + to_uint i) =>
         Glob.mem.[k] = mem.[k]
)
(32 - to_uint i); last first.
  + auto => /> H0 H1; split.
       - apply (eq_from_nth witness); first by rewrite size_load_buf // size_sub.
         rewrite size_load_buf // /#.
    move => mem0 i0; split => [* |]; first by rewrite ultE /#.
    rewrite ultE of_uintK /= => H2 H3 H4.
    have ->: to_uint i0 = 32 by smt().
    move => H5 H6.
    split => [| /#].
    apply (eq_from_nth witness); first by rewrite size_load_buf // size_to_list.
    rewrite size_load_buf // => j?. 
    by rewrite H5 nth_sub.

  + auto => /> &hr H0 H1 H2 H3 H4 H5 H6.
    do split; 2,3,6: by smt(@W64 pow2_64).
      - ring.
      - apply (eq_from_nth witness). 
          * rewrite size_load_buf; first by smt(@W64 pow2_64).
            rewrite size_sub; first by smt(@W64 pow2_64).
            reflexivity.
        rewrite size_load_buf; first by smt(@W64 pow2_64).
        move => j?.
        rewrite nth_load_buf // storeW8E get_setE.
        rewrite ultE of_uintK /= in H6.
        case (j = to_uint i{hr}) => [Ha | Hb].
          * rewrite ifT; first by smt(@W64 pow2_64).
            by rewrite nth_sub //=; congr; rewrite Ha.
          * rewrite ifF; first by smt(@W64 pow2_64).        
            rewrite nth_sub //=.
            have ->: buf.[j] = nth witness (sub buf 0 (to_uint i{hr})) j by rewrite nth_sub // ; smt(@W64 pow2_64).
            rewrite -H4 nth_load_buf //; smt(@W64 pow2_64).
      - move => k???.
        rewrite storeW8E get_setE ifF; first by smt(@W64 pow2_64).
        rewrite H5 1:/# // ; smt(@W64 pow2_64).
qed.


lemma hash_message_correct (mem : global_mem_t) 
                           (R _root : W8.t Array32.t) (_idx msg_ptr _mlen : W64.t) :
    n = XMSS_N /\
    padding_len = XMSS_PADDING_LEN /\
    H_msg_padding_val = XMSS_HASH_PADDING_HASH =>
    equiv [
      M(Syscall).__hash_message ~ M_Hash.hash :

      valid_ptr_i msg_ptr (4*n + to_uint _mlen) /\
      0 < to_uint _mlen /\
      
      0 <= to_uint _idx < 2^XMSS_FULL_HEIGHT /\

      arg{1}.`2 = R /\
      arg{1}.`3 = _root /\
      arg{1}.`4 = _idx /\
      arg{1}.`5 = msg_ptr /\
      arg{1}.`6 = _mlen /\

       Glob.mem{1} = mem /\

      arg{2}.`1 = (ThreeNBytesBytes.insubd (to_list R ++ 
                                      to_list _root ++ 
                                      (toByte_64 (W64.of_int (to_uint _idx)) 32))
                                     ) /\
      arg{2}.`2 = load_buf mem (msg_ptr + (of_int 128)%W64) (to_uint _mlen)

      ==>
      to_list res{1} = NBytes.val res{2} /\

        load_buf Glob.mem{1} msg_ptr 128 = 
            toByte_64 H_msg_padding_val n ++ 
            to_list R ++ 
            to_list _root ++             
            (toByte_64  _idx 32) /\

      forall (k : int), 0 <= k < W64.max_uint => 
            !(to_uint msg_ptr <= k < to_uint msg_ptr + 128) => 
               mem.[k] = Glob.mem{1}.[k]
    ].
proof.
rewrite /XMSS_N /XMSS_PADDING_LEN /XMSS_HASH_PADDING_HASH  => [#] n_val pad_len pad_val *.
proc => /=. 
seq 2 0 : #pre; first by auto.
seq 1 1 : (
  #pre /\ 
  to_list buf{1} = padding{2} /\
  padding{2} = toByte_64 H_msg_padding_val n
).
  + outline {1} [1] { buf <@ M(Syscall).bytes_32__ull_to_bytes (buf, W64.of_int 2); }.
    call {1} (ull_to_bytes_32_correct ((of_int 2)%W64)); auto => /> ?????->.
    apply (eq_from_nth witness); first by rewrite !size_toByte_64 //#. 
    rewrite size_W64toBytes_ext // => j?. 
    rewrite /toByte_64 /W64toBytes_ext; do congr => /#.

(* toByte(X, 32) || R || root || index || M */ *) 
seq 2 0 : (
  #{/~Glob.mem{1} = mem}pre /\ 
  load_buf Glob.mem{1} m_with_prefix_ptr{1} 32 = padding{2} /\

      forall (k : int), 0 <= k < W64.max_uint => 
            !(to_uint msg_ptr <= k < to_uint msg_ptr + 32) => 
               mem.[k] = Glob.mem{1}.[k]

).
    + inline {1} 2; inline {1} 8.
      sp; wp.
      outline {1} [1] { (out0, offset1) <@ M(Syscall).memcpy_u8pu8_n____memcpy_u8pu8 (out0, offset1, in_00); }. 
      ecall {1} (p_write_buf_ptr Glob.mem{1} out0{1} offset1{1} in_00{1}).
      skip => /> &hr H0 H1 H2 H3 H4*; smt(@W64 pow2_64).

(* toByte(X, 32) || R || root || index || M */ *) 
seq 2 0 : (
  #{/~forall (k : int),
    0 <= k && k < W64.max_uint =>
    ! (to_uint msg_ptr <= k && k < to_uint msg_ptr + 32) =>
    mem.[k] = Glob.mem{1}.[k]}pre /\ 

    load_buf Glob.mem{1} (m_with_prefix_ptr{1} + W64.of_int 32) 32 = to_list R /\
       forall (k : int),
          0 <= k && k < W64.max_uint =>
           ! (to_uint msg_ptr <= k && k < to_uint msg_ptr + 64) =>
               mem.[k] = Glob.mem{1}.[k]

).
    + inline {1} 2; inline {1} 8.
      sp; wp.
      ecall {1} (p_write_buf_ptr Glob.mem{1} out0{1} offset1{1} in_00{1}).
      skip => /> &hr H0 H1 H2 H3 H4 H5 H9*.
      do split.
       - smt().
       - smt(@W64 pow2_64).
       - move => ?? result mem0 H6 H7 H8*; split.
            * rewrite -H5; apply (eq_from_nth witness); rewrite !size_load_buf // => j?.
              by rewrite !nth_load_buf // H8 1,2:/# H6.
            * move => k???. 
              rewrite H9 1:/#; first by smt(@W64 pow2_64).
              rewrite H8 // 1:/#.

seq 2 0 : (
  #{/~forall (k : int),
    0 <= k && k < W64.max_uint =>
    ! (to_uint msg_ptr <= k && k < to_uint msg_ptr + 64) =>
    mem.[k] = Glob.mem{1}.[k]}pre /\ 

  load_buf Glob.mem{1} (m_with_prefix_ptr{1} + W64.of_int 64) 32 = to_list root{1} /\

  forall (k : int),
    0 <= k && k < W64.max_uint =>
    ! (to_uint msg_ptr <= k && k < to_uint msg_ptr + 96) =>
    mem.[k] = Glob.mem{1}.[k]
).
    + inline {1} 2; inline {1} 8.
      sp; wp.
      ecall {1} (p_write_buf_ptr Glob.mem{1} out0{1} offset1{1} in_00{1}).
      skip => /> &hr H0 H1 H2 H3 H4 H5 H6 H10*; do split.
       - smt().
       - smt(@W64 pow2_64).
       - move => ?? result mem0 H7 H8 H9.
         do split.
             * apply (eq_from_nth witness); first by rewrite size_load_buf // size_to_list.
               rewrite size_load_buf // => j?.
               rewrite nth_load_buf // -H5 H7 H9 1,2:/# nth_load_buf //.
             * apply (eq_from_nth witness); first by rewrite size_load_buf // size_to_list.
               rewrite size_load_buf // => j?.
               rewrite nth_load_buf // -H6 H7 H9; 1,2: by smt(@W64 pow2_64). 
               rewrite nth_load_buf //.
             * move => k???. 
              rewrite H10 1:/#; first by smt(@W64 pow2_64).
              rewrite H9 // 1:/#.

seq 0 0 : (
    #pre /\
    load_buf Glob.mem{1} m_with_prefix_ptr{1} 96 = 
    padding{2} ++ to_list R ++ to_list root{1} 
).
    + auto => /> &hr H0 H1 H2 H3 H4 H5 H6 H7 H8.
      apply (eq_from_nth witness); first by rewrite size_load_buf // !size_cat !size_to_list.
      rewrite size_load_buf // => j?.
      case (0 <= j < 32) => Ha.
        - rewrite nth_cat.
            * rewrite !size_cat !size_to_list ifT 1:/#.
          rewrite nth_cat.
            * rewrite size_to_list // ifT 1:/#. 
          rewrite -H5 !nth_load_buf //.
      case (32 <= j < 64) => Hb.
        - rewrite nth_cat.
            * rewrite !size_cat !size_to_list // ifT 1:/#.
          rewrite nth_cat.
            * rewrite size_to_list // ifF 1:/#. 
          rewrite -H6 /load_buf !nth_mkseq //= 1:/#.
          congr.
          smt(@W64 pow2_64).
      rewrite nth_cat.
        - rewrite !size_cat !size_to_list // ifF 1:/#.
      rewrite -H7.
      rewrite /load_buf !nth_mkseq 1,2:/# /=.
      congr.
      smt(@W64 pow2_64).

seq 1 0 : (#pre /\ to_list buf_n{1} = toByte_64 idx{1} 32).
    + outline {1} [1] { buf_n <@ M(Syscall).bytes_32__ull_to_bytes(buf_n, idx); }.
      ecall {1} (ull_to_bytes_32_correct idx{1}); auto => /> ????H*.
      rewrite /XMSS_FULL_HEIGHT /= in H; smt().

seq 2 0 : (
  #{/~forall (k : int),
    0 <= k && k < W64.max_uint =>
    ! (to_uint msg_ptr <= k && k < to_uint msg_ptr + 96) =>
    mem.[k] = Glob.mem{1}.[k]}pre /\ 

  load_buf Glob.mem{1} (m_with_prefix_ptr{1} + W64.of_int 96) 32 = toByte_64 idx{1} 32 /\
  
    forall (k : int),
    0 <= k && k < W64.max_uint =>
    ! (to_uint msg_ptr <= k && k < to_uint msg_ptr + 128) =>
    mem.[k] = Glob.mem{1}.[k]
).
    + inline {1} 2; inline {1} 8.
      sp; wp.
      ecall {1} (p_write_buf_ptr Glob.mem{1} out0{1} offset1{1} in_00{1}).
      skip => /> &hr H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
      do split.
       - smt().
       - smt(@W64 pow2_64).
       - move => H11 H12 result memL -> H13 H14.
         do split.
            * apply (eq_from_nth witness); first by rewrite size_load_buf // size_to_list.
              rewrite size_load_buf // => j?; rewrite -H5 !nth_load_buf // H14 1,2:/# //.
            * apply (eq_from_nth witness); first by rewrite size_load_buf // size_to_list.
              rewrite size_load_buf // => j?; rewrite -H6 !nth_load_buf // H14; smt(@W64 pow2_64).
            * apply (eq_from_nth witness); first by rewrite size_load_buf // size_to_list.
              rewrite size_load_buf // => j?; rewrite -H7 !nth_load_buf // H14; smt(@W64 pow2_64)
.
            * apply (eq_from_nth witness).
                + by rewrite size_load_buf // !size_cat !size_to_list.
              rewrite size_load_buf // => j?.
              case (0 <= j < 32) => [Hfst | ?].
                + rewrite nth_cat !size_cat !size_to_list ifT 1:/#.
                  rewrite nth_cat !size_to_list ifT 1:/#.
                  rewrite -H5 !nth_load_buf // H14 /#.
              case (32 <= j < 64) => [Hsnd | Hthrd].
                + rewrite nth_cat !size_cat !size_to_list ifT 1:/#.
                  rewrite nth_cat !size_to_list ifF 1:/#.
                  rewrite -H6 !nth_load_buf // 1:/# H14; smt(@W64 pow2_64).
              rewrite nth_cat size_cat !size_to_list ifF 1:/#.
              rewrite -H7 !nth_load_buf // 1:/# H14 1,2:/#; smt(@W64 pow2_64).
            * apply (eq_from_nth witness); first by rewrite size_load_buf // size_toByte_64.
              by rewrite size_load_buf // => j?; rewrite H13 H10.
       - smt().

seq 0 0 : (
  #pre /\
  load_buf Glob.mem{1} m_with_prefix_ptr{1} 128 = padding{2} ++ ThreeNBytesBytes.val t{2}
).
    + auto => /> &1 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 *.
      apply (eq_from_nth witness); first by  rewrite !size_cat ThreeNBytesBytes.valP size_to_list size_load_buf /#.
      rewrite size_load_buf // => j?.
      rewrite nth_load_buf //.
      case (0 <= j < 32) => [H_1 | ?].
         * by rewrite nth_cat size_to_list ifT 1:/# -H5 nth_load_buf.
      case (32 <= j < 64) => [H_2 | ?].
         * rewrite nth_cat size_to_list ifF 1:/# ThreeNBytesBytes.insubdK.
             - rewrite /P !size_cat !size_to_list size_toByte_64 /#.
           rewrite nth_cat !size_cat !size_to_list ifT 1:/#.
           rewrite nth_cat !size_to_list ifT 1:/#.
           rewrite -H6 nth_load_buf 1:/#; congr; smt(@W64 pow2_64).
      case (64 <= j < 96) => [H_3 | H_4].
         * rewrite nth_cat size_to_list ifF 1:/# ThreeNBytesBytes.insubdK.
             - rewrite /P !size_cat !size_to_list size_toByte_64 /#.
           rewrite nth_cat !size_cat !size_to_list ifT 1:/#.
           rewrite nth_cat !size_to_list ifF 1:/#.
           rewrite -H7 nth_load_buf 1:/#; congr; smt(@W64 pow2_64).
         * rewrite nth_cat size_to_list ifF 1:/# ThreeNBytesBytes.insubdK.
             - rewrite /P !size_cat !size_to_list size_toByte_64 /#.
           rewrite nth_cat !size_cat !size_to_list ifF 1:/# /=.
           rewrite -H10 nth_load_buf 1:/#; congr; smt(@W64 pow2_64).

seq 2 0 : (#pre /\ len{1} = mlen{1} + W64.of_int 128); first by auto => />. 

exists * m_with_prefix_ptr{1}, len{1}; elim * => P0 P1.
ecall {1} (hash_ptr_correct P0 P1). 
auto => /> &1 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12*.
do split.
    + rewrite /valid_ptr_i; smt(@W64 pow2_64).
move => H13 result ->; split; last first. 
    + rewrite H12; apply (eq_from_nth witness); first by rewrite !size_cat ThreeNBytesBytes.valP !size_to_list !size_toByte_64 /#.
      rewrite !size_cat size_to_list ThreeNBytesBytes.valP n_val /= => j?.
      case (0 <= j < 32) => [H_1 | ?].
         * rewrite nth_cat size_to_list ifT 1:/#.
           rewrite nth_cat !size_cat size_toByte_64 // !size_to_list /= ifT 1:/#.
           rewrite nth_cat !size_cat size_toByte_64 // !size_to_list /= ifT 1:/#.
           rewrite nth_cat size_toByte_64 // /= ifT 1:/#.
           by rewrite -get_to_list H4 n_val.
      case (32 <= j < 64) => [H_2 | ?].
         * rewrite nth_cat size_to_list ifF 1:/#.
           rewrite nth_cat !size_cat size_toByte_64 // !size_to_list /= ifT 1:/#.
           rewrite nth_cat !size_cat size_toByte_64 // !size_to_list /= ifT 1:/#.
           rewrite nth_cat size_toByte_64 // /= ifF 1:/#.
           rewrite ThreeNBytesBytes.insubdK.
             - rewrite /P !size_cat !size_to_list size_toByte_64 /#.
           rewrite nth_cat !size_cat !size_to_list /= ifT 1:/#.
           rewrite nth_cat !size_to_list /= ifT 1:/#.
           reflexivity.
      case (64 <= j < 96) => [H_3 | H_4].
         * rewrite nth_cat size_to_list ifF 1:/#.
           rewrite nth_cat !size_cat size_toByte_64 // !size_to_list /= ifT 1:/#.
           rewrite nth_cat !size_cat size_toByte_64 // !size_to_list /= ifF 1:/#.
           rewrite ThreeNBytesBytes.insubdK.
             - rewrite /P !size_cat !size_to_list size_toByte_64 /#.
           rewrite nth_cat !size_cat !size_to_list /= ifT 1:/#.
           rewrite nth_cat !size_to_list /= ifF 1:/#.
           reflexivity.
         * rewrite nth_cat size_to_list ifF 1:/#.
           rewrite nth_cat !size_cat size_toByte_64 // !size_to_list /= ifF 1:/#.
           rewrite ThreeNBytesBytes.insubdK.
             - rewrite /P !size_cat !size_to_list size_toByte_64 /#.
           rewrite nth_cat !size_cat !size_to_list /= ifF 1:/#.
           reflexivity.
 
congr; congr. 
apply (eq_from_nth witness).
    + rewrite size_load_buf; first by smt(@W64 pow2_64).
      rewrite !size_cat ThreeNBytesBytes.valP !size_to_list n_val /= size_load_buf; smt(@W64 pow2_64).
rewrite size_load_buf; first by smt(@W64 pow2_64).
have ->: to_uint (_mlen + (of_int 128)%W64) = to_uint _mlen + 128 by smt(@W64 pow2_64).
move => j?.
rewrite nth_load_buf //.
case (0 <= j < 32) => [H_1 | ?].
    + rewrite nth_cat !size_cat size_to_list ThreeNBytesBytes.valP ifT 1:/#.
      rewrite nth_cat size_to_list ifT 1:/#.
      by rewrite -H5 nth_load_buf.
case (32 <= j < 64) => [H_2 | ?].
    + rewrite nth_cat !size_cat size_to_list ThreeNBytesBytes.valP ifT 1:/#.
      rewrite nth_cat size_to_list ifF 1:/#.
      rewrite ThreeNBytesBytes.insubdK.
         * rewrite /P !size_cat !size_to_list size_toByte_64 /#.
      rewrite nth_cat !size_cat !size_to_list ifT 1:/#.
      rewrite nth_cat size_to_list ifT 1:/#.
      rewrite -H6 nth_load_buf 1:/#; congr; smt(@W64 pow2_64).
case (64 <= j < 96) => [H_3 | ?].
    + rewrite nth_cat !size_cat size_to_list ThreeNBytesBytes.valP ifT 1:/#.
      rewrite nth_cat size_to_list ifF 1:/#.
      rewrite ThreeNBytesBytes.insubdK.
         * rewrite /P !size_cat !size_to_list size_toByte_64 /#.
      rewrite nth_cat !size_cat !size_to_list ifT 1:/#.
      rewrite nth_cat size_to_list ifF 1:/#.
      rewrite -H7 nth_load_buf 1:/#; congr; smt(@W64 pow2_64).
case (96 <= j < 128) => [H_4 | H_5].
    + rewrite nth_cat !size_cat size_to_list ThreeNBytesBytes.valP ifT 1:/#.
      rewrite nth_cat size_to_list ifF 1:/#.
      rewrite ThreeNBytesBytes.insubdK.
         * rewrite /P !size_cat !size_to_list size_toByte_64 /#.
      rewrite nth_cat !size_cat !size_to_list ifF 1:/#.
      rewrite -H10 nth_load_buf 1:/#; congr; smt(@W64 pow2_64).
    + rewrite nth_cat !size_cat size_to_list ThreeNBytesBytes.valP ifF 1:/#.
      rewrite nth_load_buf 1:/#.
rewrite n_val /=  H11; smt(@W64 pow2_64).
qed.

