pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel JArray.

require import Params Types Address Hash BaseW WOTS. 

require import XMSS_IMPL Parameters.

require import Array2 Array3 Array8 Array32 Array64 Array67 Array96 Array2144.

require import WArray32 WArray96.

require import Correctness_Bytes Correctness_Mem Correctness_Address Correctness_Hash. 
require import Repr Utils Bytes.

(*---*) import BitEncoding.BitChunking.
(*---*) import StdBigop.Bigint.

module ThashF = {
  proc thash_f (t : nbytes, seed : seed, address : adrs) : (nbytes * adrs) = {
    var key : nbytes;
    var bitmask : nbytes;
    var addr_bytes : nbytes;
    
    addr_bytes <- addr_to_bytes address;
    key <@ Hash.prf(addr_bytes, seed);
    address <- set_key_and_mask address 1;
    addr_bytes <- addr_to_bytes address;
    bitmask <@ Hash.prf(addr_bytes, seed);
    t <@ Hash._F(key, nbytexor t bitmask);
    return (t, address);
  }
}.

lemma thash_f_equiv (_out_ _seed_ : W8.t Array32.t) (a : W32.t Array8.t) :
    n = XMSS_N /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    padding_len = XMSS_PADDING_LEN /\ 
    F_padding_val = XMSS_HASH_PADDING_F =>
    equiv [
      M(Syscall).__thash_f ~ ThashF.thash_f :
      arg{1}.`1 = _out_ /\
      arg{1}.`2 = _seed_ /\
      arg{1}.`3 = a /\

      
      arg{2}.`1 = NBytes.insubd (to_list _out_) /\
      arg{2}.`2 = NBytes.insubd (to_list _seed_) /\
      arg{2}.`3 = a
      ==>
      to_list res{1}.`1 = NBytes.val res{2}.`1 /\
      res{1}.`2 = res{2}.`2 /\
      res{1}.`2.[7] = W32.one /\
      sub res{1}.`2 0 7 = sub a 0 7
    ].
proof. 
rewrite /XMSS_N => [#] n_val ???.
proc => /=.
seq 4 0 : #pre; first by auto.

seq 1 1 : (#pre /\ to_list addr_as_bytes{1} = NBytes.val addr_bytes{2}).
  + exists * addr{1}; elim * => P.
    call {1} (addr_to_bytes_correctness P); auto => /> ?->.
    have E : size (flatten (map Bytes.W32toBytes (to_list a))) = 32.
      - rewrite size_flatten sumzE BIA.big_map /(\o) //= -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 4)) /=.
           * rewrite in_nth size_map size_to_list /= => i?.
             rewrite (nth_map witness); by rewrite ?size_to_list // /W32toBytes size_rev size_to_list. 
        by rewrite big_constz count_predT size_map size_to_list /=.
    apply (eq_from_nth witness); rewrite ?NBytes.valP ?n_val E // => i?.
    rewrite /addr_to_bytes => />.
    rewrite NBytes.insubdK.
      - rewrite /P size_flatten sumzE BIA.big_map /(\o) //= -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 4)) /=.
           * rewrite in_nth size_map size_to_list /= => j?.
             rewrite (nth_map witness); by rewrite ?size_to_list // /W32toBytes size_rev size_to_list. 
        rewrite big_constz count_predT size_map size_to_list /= /#.
    do congr => /#.

inline {2} Hash._F. 

swap {2} 7 -6.

seq 2 1 : (#pre /\ to_list padding{1} = padding{2}).
  + sp; wp; conseq />.
    transitivity {1} { padding <@ M(Syscall).bytes_32__ull_to_bytes (padding, W64.zero); }
    (={padding} ==> ={padding})
    (
      padding{2} = toByte_64 F_padding_val padding_len /\
      padding{1} = Array32.init (fun (i_0 : int) => buf{1}.[0 + i_0]) /\
      out{1} = _out_ /\
      pub_seed{1} = _seed_ /\
      addr{1} = a /\
      t{2} = NBytes.insubd (to_list _out_) /\
      seed{2} = NBytes.insubd (to_list _seed_) /\ 
      address{2} = a /\
      to_list addr_as_bytes{1} = NBytes.val addr_bytes{2}
      ==>
      to_list padding{1} = toByte_64 F_padding_val padding_len
    ) => //; 2: by (inline; sim).
      - auto => /> &1 &2 <-.
        by exists a addr_as_bytes{1} buf{1} _out_ (Array32.init ("_.[_]" buf{1})) _seed_. 
      - ecall {1} (ull_to_bytes_32_correct W64.zero); auto => /> &1 &2 ??->; smt(W64toBytes_ext_toByte_64).

seq 1 0 : (#pre /\ sub buf{1} 0 n = padding{2}).
  + auto => /> &1 &2 ?.
    apply (eq_from_nth witness); rewrite ?size_to_list n_val size_sub // => j?.
    by rewrite get_to_list nth_sub // initiE 1:/# /= ifT.

seq 1 1 : (#pre /\ to_list aux{1} = NBytes.val key{2}).
  + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
    exists * in_00{1}, key0{1}; elim * => _P1 _P2.
    call {1} (prf_correctness _P1 _P2) => [/# |]. 
    skip => /> &1 &2 -> ?; smt(NBytes.valKd).

seq 1 0 : (#pre /\ sub buf{1} n n = NBytes.val key{2}).
  + auto => /> &1 &2 H0 H1 H2. 
    split; apply (eq_from_nth witness); rewrite size_sub ?size_to_list ?NBytes.valP n_val //= => j?; rewrite nth_sub //= initiE 1:/# /=.
      - by rewrite ifF 1:/# (: padding{1}.[j] = nth witness (to_list padding{1}) j) 1:/# -H1 nth_sub /#.
      - by rewrite ifT 1:/# -H2 get_to_list.

seq 1 1 : (
  #{/~addr{1} = a}{/~address{2} = a}pre /\ 
  addr{1} = address{2} /\ 
  addr{1}.[7] = W32.one /\
  sub addr{1} 0 7 = sub a 0 7
).
  + by inline {1}; auto => /> &1 &2 *; apply (eq_from_nth witness); rewrite !size_sub // => j?; rewrite !nth_sub //= get_setE //= ifF 1:/#.

seq 1 1 : (#pre /\ to_list addr_as_bytes{1} = NBytes.val addr_bytes{2}).
  + exists * addr{1}; elim * => P1; call {1} (addr_to_bytes_correctness P1).
    auto => /> 9? ->.
    have E : size (flatten (map Bytes.W32toBytes (to_list P1))) = 32.
      - rewrite size_flatten sumzE BIA.big_map /(\o) //= -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 4)) /=.
           * rewrite in_nth size_map size_to_list /= => i?.
             rewrite (nth_map witness); by rewrite ?size_to_list // /W32toBytes size_rev size_to_list. 
        by rewrite big_constz count_predT size_map size_to_list /=.
    split.

    apply (eq_from_nth witness); rewrite ?NBytes.valP ?n_val E // => i?.
    rewrite /addr_to_bytes => />.
    rewrite NBytes.insubdK.
      - rewrite /P size_flatten sumzE BIA.big_map /(\o) //= -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 4)) /=.
           * rewrite in_nth size_map size_to_list /= => j?.
             rewrite (nth_map witness); by rewrite ?size_to_list // /W32toBytes size_rev size_to_list. 
        rewrite big_constz count_predT size_map size_to_list /= /#.
    do congr => /#.


    apply (eq_from_nth witness); rewrite ?NBytes.valP ?n_val E // => i?.
    rewrite /addr_to_bytes => />.
    rewrite NBytes.insubdK.
      - rewrite /P size_flatten sumzE BIA.big_map /(\o) //= -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 4)) /=.
           * rewrite in_nth size_map size_to_list /= => j?.
             rewrite (nth_map witness); by rewrite ?size_to_list // /W32toBytes size_rev size_to_list. 
        rewrite big_constz count_predT size_map size_to_list /= /#.
    do congr => /#.

seq 1 1 : (#pre /\ to_list bitmask{1} = NBytes.val bitmask{2}).
  + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
    exists * in_00{1}, key0{1}; elim * => _P1 _P2.
    call {1} (prf_correctness _P1 _P2) => [/# |]. 
    skip => /> &1 &2 -> *; split => [| /#]; by rewrite NBytes.valKd. 

seq 1 3 : (
  addr{1} = address{2} /\
  addr{1}.[7] = W32.one /\
  sub addr{1} 0 7 = sub a 0 7 /\
  to_list buf{1} = buf{2}
); last by auto; ecall {1} (hash_96 buf{1}); auto => />. 

wp; sp.

rcondt{1} 1 => //.
unroll {1} 2; rcondt {1} 2; 1: by auto.
unroll {1} 6; rcondt {1} 6; 1: by auto.
unroll {1} 10; rcondt {1} 10; 1: by auto.
unroll {1} 14; rcondt {1} 14; 1: by auto.
rcondf{1} 18; 1: by auto. 
auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6.
apply (eq_from_nth witness); rewrite ?size_cat !size_to_list ?NBytes.valP ?n_val //= => j?.
case (0 <= j < 32) => ?.
- do 2! rewrite nth_cat ?size_cat ?NBytes.valP size_to_list ifT 1:/#.
  rewrite get_to_list initiE // /set64_direct /get8 wordP => k?.
  rewrite initiE //= ifF 1:/# initiE // initiE //= initiE //= ifF 1:/#.
  rewrite initiE //= initiE //= initiE //= ifF 1:/# initiE // initiE //= initiE //= ifF 1:/#.
  rewrite initiE //=.
  have ->: padding{1}.[j].[k] = (nth witness (to_list padding{1}) j).[k] by rewrite get_to_list //.
  rewrite -H1 nth_sub /#.
case (32 <= j < 64) => ?.
- rewrite nth_cat ?size_cat ?NBytes.valP size_to_list ifT 1:/# nth_cat ?size_cat ?NBytes.valP size_to_list ifF 1:/#.
  rewrite initiE // /set64_direct /get8 wordP => k?.
  rewrite initiE //= ifF 1:/# initiE // initiE //= initiE //= ifF 1:/#.
  rewrite initiE //= initiE //= initiE //= ifF 1:/# initiE // initiE //= initiE //= ifF 1:/#.
  rewrite initiE //= -H3 nth_sub /#.
- rewrite nth_cat ?size_cat ?NBytes.valP size_to_list ifF 1:/#.
  rewrite initiE // /set64_direct /get8 wordP => k?.
  rewrite initiE //=.
  case (88 <= j < 96) => ?.
    * rewrite !bits8E /= initiE //= get64E pack8E /= initiE 1:/#/=.
      rewrite  get64E pack8E /= initiE 1:/#/= initiE 1:/# initiE 1:/#/= initiE 1:/#/= initiE 1:/#/= initiE 1:/#/=.
      rewrite /nbytexor -H6 NBytes.insubdK /bytexor.
         + rewrite size_map size_zip NBytes.valP size_to_list /#.
      rewrite (nth_map witness) /=.
         + rewrite size_zip NBytes.valP size_to_list /#.
      rewrite !NBytes.insubdK ?size_to_list ?n_val //=.
      have ->: (nth witness (zip (to_list _out_) (to_list bitmask{1})) (j - 64)) = nth (witness, witness) (zip (to_list _out_) (to_list bitmask{1})) (j - 64)
      by apply (nth_change_dfl); rewrite size_zip !size_to_list /#.
      rewrite !nth_zip ?size_to_list //= /#.
  rewrite initiE //= initiE //= initiE //=. 
  case (80 <= j < 88) => ?.
    * rewrite !bits8E /= initiE //= get64E pack8E /= initiE 1:/#/=.
      rewrite  get64E pack8E /= initiE 1:/#/= initiE 1:/# initiE 1:/#/= initiE 1:/#/= initiE 1:/#/= initiE 1:/#/=.
      rewrite /nbytexor -H6 NBytes.insubdK /bytexor.
         + rewrite size_map size_zip NBytes.valP size_to_list /#.
      rewrite (nth_map witness) /=.
         + rewrite size_zip NBytes.valP size_to_list /#.
      rewrite !NBytes.insubdK ?size_to_list ?n_val //=.
      have ->: (nth witness (zip (to_list _out_) (to_list bitmask{1})) (j - 64)) = nth (witness, witness) (zip (to_list _out_) (to_list bitmask{1})) (j - 64)
      by apply (nth_change_dfl); rewrite size_zip !size_to_list /#.
      rewrite !nth_zip ?size_to_list //= /#.
  rewrite initiE //= initiE //= initiE //=. 
  case (72 <= j < 80) => ?.
    * rewrite !bits8E /= initiE //= get64E pack8E /= initiE 1:/#/=.
      rewrite  get64E pack8E /= initiE 1:/#/= initiE 1:/# initiE 1:/#/= initiE 1:/#/= initiE 1:/#/= initiE 1:/#/=.
      rewrite /nbytexor -H6 NBytes.insubdK /bytexor.
         + rewrite size_map size_zip NBytes.valP size_to_list /#.
      rewrite (nth_map witness) /=.
         + rewrite size_zip NBytes.valP size_to_list /#.
      rewrite !NBytes.insubdK ?size_to_list ?n_val //=.
      have ->: (nth witness (zip (to_list _out_) (to_list bitmask{1})) (j - 64)) = nth (witness, witness) (zip (to_list _out_) (to_list bitmask{1})) (j - 64)
      by apply (nth_change_dfl); rewrite size_zip !size_to_list /#.
      rewrite !nth_zip ?size_to_list //= /#.
  rewrite initiE //= initiE //= initiE //= ifT 1:/#.  
  rewrite  !get64E !pack8E /= !bits8E.
  rewrite initiE 1:/#/= initiE 1:/# initiE 1:/#/= initiE 1:/#/= initiE 1:/#/= initiE 1:/#/=.
  rewrite initiE 1:/#/= initiE 1:/# /nbytexor -H6 NBytes.insubdK /bytexor. 
    * rewrite size_map size_zip NBytes.valP size_to_list /#.
  rewrite (nth_map witness) /=.
    * rewrite size_zip NBytes.valP size_to_list /#.
  rewrite !NBytes.insubdK ?size_to_list ?n_val //=.
  have ->: (nth witness (zip (to_list _out_) (to_list bitmask{1})) (j - 64)) = nth (witness, witness) (zip (to_list _out_) (to_list bitmask{1})) (j - 64)
  by apply (nth_change_dfl); rewrite size_zip !size_to_list /#.
  rewrite !nth_zip ?size_to_list //= /#.
qed.

lemma gen_chain_correct (_buf_ : W8.t Array32.t, _start_ _steps_ : W32.t, _pub_seed_ : W8.t Array32.t) (a1 a2 : W32.t Array8.t):
    n = XMSS_N /\
    w = XMSS_WOTS_W /\ 
    len = XMSS_WOTS_LEN /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\ 
    padding_len = XMSS_PADDING_LEN /\ 
    F_padding_val = XMSS_HASH_PADDING_F =>
    equiv [
      M(Syscall).__gen_chain_inplace ~ Chain.chain : 
      arg{1} = (_buf_, _start_, _steps_, _pub_seed_, a1) /\
      arg{2} = (NBytes.insubd (to_list _buf_), to_uint _start_, to_uint _steps_, NBytes.insubd (to_list _pub_seed_), a2) /\
      0 <= to_uint _start_ <= XMSS_WOTS_W - 1/\
      0 <= to_uint _steps_ <= XMSS_WOTS_W - 1 /\
      0 <= to_uint (_start_ + _steps_) <= w - 1 /\
      sub a1 0 6 = sub a2 0 6
      ==> 
      NBytes.val res{2} = to_list res{1}.`1 /\
      sub res{1}.`2 0 6 = sub a1 0 6 
    ].
proof.
rewrite /XMSS_N /XMSS_WOTS_W => [#] n_val w_val *.
proc => //=.

swap {1} 1 2.

seq 2 1 : ( 
  0 <= to_uint start{1} <= w - 1/\
  0 <= to_uint steps{1} <= w - 1 /\
  0 <= to_uint (start{1} + steps{1}) <= w - 1 /\
  NBytes.val t{2} = to_list out{1} /\
  i{2} = to_uint start{1} /\
  s{2} = to_uint steps{1} /\
  NBytes.val _seed{2} = to_list pub_seed{1} /\
  NBytes.val t{2} = to_list out{1} /\  
  t{1} = start{1} + steps{1} /\
  sub addr{1} 0 6 = sub address{2} 0 6 /\ 
  sub addr{1} 0 6 = sub a1 0 6 /\
  start{1} = _start_ /\
  steps{1} = _steps_ 
); first by auto => /> *; do split => [/# | /# | | |]; by rewrite NBytes.insubdK /P // size_to_list n_val.

while (
  sub addr{1} 0 6 = sub address{2} 0 6 /\ 
  sub addr{1} 0 6 = sub a1 0 6 /\

  0 <= to_uint start{1} <= w - 1/\
  0 <= to_uint steps{1} <= w - 1 /\ 
  0 <= to_uint (start{1} + steps{1}) <= w - 1 /\

  NBytes.val t{2} = to_list out{1} /\
  NBytes.val _seed{2} = to_list pub_seed{1} /\
  
  0 <= chain_count{2} <= s{2} /\
  s{2} = to_uint steps{1} /\ 
  i{2} = to_uint start{1} /\
  to_uint i{1} = i{2} + chain_count{2} /\
  t{1} = start{1} + steps{1} 
); last by auto => /> *; rewrite ultE !to_uintD /#.

seq 2 2 : (#pre /\ address{2} = addr{1}).
    + inline {1}; auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 *.
      rewrite /set_key_and_mask /set_hash_addr.
      do split.
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => j?.
           rewrite !nth_sub // !get_setE // !ifF 1..4:/#.
           smt(sub_k).
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => j?.
           rewrite !nth_sub // !get_setE // !ifF 1,2:/#.
           smt(sub_k).
         * rewrite tP => j?.
           rewrite !get_setE //.
           case (j = 7) => //?.
           case (j = 6) => //?; first by rewrite -H12 to_uintK.
           smt(sub_k).


conseq />. (* simplify #post *)

outline {2} [1..6] by { 
  (t, address) <@ ThashF.thash_f (t, _seed, address); 
}.

inline {1}  M(Syscall).__thash_f_  M(Syscall)._thash_f.

sp; wp.

conseq />.

exists * out1{1}, pub_seed1{1}, addr1{1}.
elim * => P0 P1 P2.
call (thash_f_equiv P0 P1 P2) => [/# |]. 
skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 <- <- H9 H10 H11 H12 H13.
rewrite !NBytes.valKd.
do split => _ _. (* These hypothesis are useless: t{2} = t{2} and _seed{2} = _seed{2} *)
move => H14 H15 resultL resultR H16 H17.
rewrite !ultE !to_uintD -H0; smt(sub_N). 
qed.

