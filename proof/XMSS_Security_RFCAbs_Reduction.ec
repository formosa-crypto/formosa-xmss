require import AllCore IntDiv List Distr DList StdOrder RealExp.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.
require import Array8.

require import XMSS_RFC_Abs.
import XMSS_RFC_Params WOTS_RFC_Abs Address BaseW.

require import XMSS_Security_RFCAbs.
import XMSS_Security RFC.
import FLXMSSTW.
import SA.
import WTW.

require (*****) DigitalSignaturesROM.
  clone import DigitalSignaturesROM as DSS_TOP with
    type pk_t <- xmss_pk,
    type sk_t <- xmss_sk,
    type msg_t <- W8.t list,
    type sig_t <- sig_t,

    type in_t <- nbytes * (dgstblock * index * W8.t list),
    type out_t <- msgFLXMSSTW ,
    type d_in_t <- int,
    type d_out_t <- bool,

      op doutm <- fun _ => duniform DigestBlockFT.enum

    proof *.
import DSS.
import KeyUpdating.
import KeyUpdatingROM.

module (S : Scheme_RO) (O : RO.POracle) = {
   proc keygen() = {
      var kp;
      kp <@ XMSS_RFC_Abs(RFC_O(O)).kg();
      return (kp.`2,kp.`1);
   }

   proc sign = XMSS_RFC_Abs(RFC_O(O)).sign

   (* THIS IS A HACK BECAUSE RFC SHOULD BE CHECKING FOR IDX RANGE.  *)
   proc verify(pk : xmss_pk, m : W8.t list, sig : sig_t) : bool  = {
       var r;
       r <@ XMSS_RFC_Abs(RFC_O(O)).verify(pk,m,sig);
       return 0 <= to_uint sig.`sig_idx < l && r;
   }
}.

module B_Oracles(O : DSS_RFC.DSS.KeyUpdating.SOracle_CMA) : SOracle_CMA = {
   proc sign(m : W8.t list) : sig_t = {
      var sig;
      sig <@ O.sign(m);
      return ({| sig_idx = W32.of_int (Index.val sig.`2.`1) ; r = sig.`1; 
           
          r_sig = (LenNBytes.insubd (map NBytes.insubd (map (BitsToBytes \o DigestBlock.val) (DBLL.val sig.`2.`2))),
                  AuthPath.insubd (rev (map NBytes.insubd (map  (BitsToBytes \o DigestBlock.val) (DBHL.val sig.`2.`3))))) |});
   }
}.

module (B(A : Adv_EUFCMA_RO) : DSS_RFC.KeyUpdatingROM.Adv_EUFCMA_RO) (RO : RO.POracle, O : DSS_RFC.DSS.KeyUpdating.SOracle_CMA) = {
   proc forge(pk : pkXMSSTWRFC) : W8.t list * sigXMSSTW = { 
         var f;
         f <@ A(RO,B_Oracles(O)).forge({| pk_oid = impl_oid; pk_root = NBytes.insubd (BitsToBytes (DigestBlock.val pk.`1)); pk_pub_seed = pk.`2|});
         return (f.`1,
          (f.`2.`r,
            (Index.insubd (to_uint f.`2.`sig_idx),
             DBLL.insubd (map (fun (b : nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (LenNBytes.val f.`2.`r_sig.`1)),
             DBHL.insubd (rev (map (fun (b : nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (AuthPath.val f.`2.`r_sig.`2))))));
   }
}. 

lemma verify1_ll (O <: RO.Oracle) : islossless O.o => islossless XMSS_RFC_Abs(RFC_O(O)).verify.
move => Oll. 
proc. 
islossless.
+ while (true) (h - k);move => *; auto => /> /#.
+ while (true) (Params.len - i). 
  + move => *; inline *; wp; while (true) (s - chain_count);move => *; auto => /> /#.
    by auto;smt().
+ while (true) (outlen - consumed);move => *; auto => /> /#.
+ while (true) (Params.len1 - i);move => *; auto => /> /#.
+ while (true) (outlen - consumed);move => *; auto => /> /#.
qed.

lemma verify2_ll (O <: RO.Oracle) : islossless O.o => islossless XMSS_TW_RFC(O).verify.
move => Oll. 
proc. 
islossless.
while (true) (XMSS_Security.FLXMSSTW.len - size pkWOTS);move => *; auto => />;smt(size_rcons).
qed.

lemma sign1_ll (O <: RO.Oracle) : islossless O.o => islossless XMSS_TW_RFC(O).sign.
move => Oll.
islossless.
+ while (true) (l - size leafl); last by auto;smt(size_rcons).
  move => z;wp;conseq (: true);1:smt(size_rcons).
  islossless.
  + while (true) (XMSS_Security.FLXMSSTW.len - size pkWOTS);move => *; auto => />;smt(size_rcons).
  + while (true) (XMSS_Security.FLXMSSTW.len - size skWOTS);move => *; auto => />;smt(size_rcons).
  + while (true) (XMSS_Security.FLXMSSTW.len - size sig);move => *; auto => />;smt(size_rcons).
  while (true) (XMSS_Security.FLXMSSTW.len - size skWOTS);move => *; auto => />;smt(size_rcons).
qed.

lemma sign2_ll (O <: RO.Oracle) : islossless O.o => islossless S(O).sign.
move => Oll.
islossless.
+ while (true) (Params.len - i). 
  + move => *; inline *; wp; while (true) (s - chain_count);move => *; auto => /> /#.
    by auto;smt().
+ while (true) (outlen - consumed);move => *; auto => /> /#.
+ while (true) (Params.len1 - i);move => *; auto => /> /#.
+ while (true) (outlen - consumed);move => *; auto => /> /#.
+ while (true) (Params.len - i);move => *; auto => /> /#.
+ while (true) (h-j);last by auto => /> /#.
  move => z;wp;conseq (: true);1:smt().
  islossless.
  + while (true) (2^t - i); last by auto;smt().
    move => zz;wp;conseq (: true);1:smt().
    while (true) (to_uint offset - 2 + 1).
    + move => zzz;auto => /> &hr; rewrite uleE /= => ? _.
      by rewrite to_uintB /=;rewrite ?uleE /#.
    conseq (: true) => /=;1: by move => &hr ?? ofs ?;rewrite uleE /= /#. 
    islossless.
    + while (true) (Params.len - i). 
    + move => *; inline *; wp; while (true) (s - chain_count);move => *; auto => /> /#.
      by auto;smt().
+ while (true) (Params.len - i);move => *; auto => /> /#.
qed.

lemma security &m  (O <: RO.Oracle  {-O_CMA_Default, -DSS_RFC.DSS.KeyUpdating.O_CMA_Default}) (A <: Adv_EUFCMA_RO {-O_CMA_Default, -DSS_RFC.DSS.KeyUpdating.O_CMA_Default, -O}):
    islossless O.o =>
    (forall (RO <: RO.POracle{-A}) (O0 <: SOracle_CMA{-A}),
      islossless O0.sign => islossless RO.o => islossless A(RO, O0).forge) =>
     (forall  (RO <: RO.POracle{-A}), hoare [ A(RO,O_CMA_Default(S(O))).forge :  
         size O_Base_Default.qs = 0 ==> size O_Base_Default.qs <= l]) =>
    Pr [ EUF_CMA_RO(S,A,O_CMA_Default,O).main() @ &m : res ] <=
    Pr[DSS_RFC.KeyUpdatingROM.EUF_CMA_RO(XMSS_TW_RFC, B(A), DSS_RFC.DSS.KeyUpdating.O_CMA_Default, O).main
                   () @ &m : res].
proof. 
move => O_ll A_ll Abounded.
byequiv => //.
proc. 
seq 1 1 : (={glob A,glob O}); 1: by call(:true);auto.

inline {1} 1; inline {2} 1;inline {2} 3;inline {1} 4.

seq 3 4 : (O_Base_Default.qs{1} = DSS_RFC.DSS.O_Base_Default.qs{2} 
       /\ pkrel pk{2} pk{1} 
       /\ ={glob O} 
       /\ m{1} = f{2}.`1 
       /\ f{2}.`2 = sig{1}); last first.
+ sp;case (0 <= to_uint sig0{1}.`sig_idx < l); last first. 
  + inline {1} 3;inline {2} 2;wp;conseq (: _ ==> true);1: by auto => />.
    + call {1} (: true ==> true);1: by apply (verify1_ll O).
    + call {2} (: true ==> true);1: by apply (verify2_ll O).
    by auto.
  wp;call(:O_Base_Default.qs{1} = DSS_RFC.DSS.O_Base_Default.qs{2} /\ ={arg} ==> 
     O_Base_Default.qs{1} = DSS_RFC.DSS.O_Base_Default.qs{2} /\ ={res});1: by proc; auto => /#.
  wp;call(: pkrel  arg{2}.`1 arg{1}.`1 /\ ={m,glob O} /\ sigrel arg{2}.`3 arg{1}.`3 ==> ={res});
    1: by symmetry;proc*;call(ver_eq O);auto => /#.
  auto =>  /> &1 &2 *;do split. 
  + by rewrite Index.insubdK;smt().
  + rewrite DBHL.insubdK /=;1: by rewrite size_rev size_map AuthPath.valP. 
    by rewrite revK. 

seq 2 2 : (={glob A, glob O} 
   /\ O_Base_Default.qs{1} = DSS_RFC.DSS.O_Base_Default.qs{2} 
   /\ O_Base_Default.qs{1} = []
   /\ pkrel pk{2} pk{1}
   /\ skrel DSS_RFC.DSS.KeyUpdating.O_CMA_Default.sk{2} O_CMA_Default.sk{1}
   /\ to_uint O_CMA_Default.sk{1}.`idx = 0).
+ inline {1} 2; inline {2} 2;wp => /=.
  inline {1} 1;wp;symmetry;call (kg_eq O).
  auto => />.

sp;symmetry.

conseq (: pk0{1} = pk{1} /\
  ((glob A){2} = (glob A){1} /\ (glob O){2} = (glob O){1}) /\
  O_Base_Default.qs{2} = DSS_RFC.DSS.O_Base_Default.qs{1} /\
  O_Base_Default.qs{2} = [] /\
  pkrel pk{1} pk{2} /\
  skrel DSS_RFC.DSS.KeyUpdating.O_CMA_Default.sk{1} O_CMA_Default.sk{2} /\ 
  to_uint O_CMA_Default.sk{2}.`idx = 0
  ==> 
  !(2^h < size O_Base_Default.qs{2}) =>
  O_Base_Default.qs{2} = DSS_RFC.DSS.O_Base_Default.qs{1} /\
  pkrel pk{1} pk{2} /\ (glob O){2} = (glob O){1} /\ m{2} = f{1}.`1 /\ f{1}.`2 = sig{2})
 _ (: size O_Base_Default.qs =  0 ==> size O_Base_Default.qs <= l).
+ smt().
+ smt().
+ by call (Abounded O);  auto => />.

call(: 2^h < size O_Base_Default.qs,
       ={glob O} 
    /\ O_Base_Default.qs{2} = DSS_RFC.DSS.O_Base_Default.qs{1} /\ size O_Base_Default.qs{2} = to_uint O_CMA_Default.sk{2}.`idx
    /\ (to_uint O_CMA_Default.sk{2}.`idx < 2 ^ h => skrel DSS_RFC.DSS.KeyUpdating.O_CMA_Default.sk{1} O_CMA_Default.sk{2} ),true).
+ proc;inline {1} 1.
  case : (to_uint O_CMA_Default.sk{2}.`idx < 2 ^ h); last first. 
  + sp;wp => /=; conseq(: _ ==> true).
    + move => &1 &2 />*;split => *;
      have ? : to_uint (O_CMA_Default.sk{2}.`Top.XMSS_RFC_Abs.idx + W32.one) = 2^h + 1; 
       rewrite ?to_uintD_small /=;smt(size_rcons l_max). 
    + call {1} (: true ==> true);1: by apply (sign1_ll O).
    + call {2} (: true ==> true);1: by apply (sign2_ll O).
    by auto.

  exlim O_CMA_Default.sk{2}.`idx => _idx.
  wp; call (sig_eq O (to_uint _idx)).
  auto => /> &1 &2. 
  move =>  H0 H1 H2  H3;split;1:smt(). 
  move =>  H4 H5 H6 H7 H8 H9 s1 s2 H10 H11 H12 H13 H14 H15 H16;do split. 
  + have ? : W32.of_int (Index.val s1.`1.`2.`1) = s2.`1.`sig_idx.
    + apply W32.to_uint_eq; rewrite /= of_uintK /= -H11; smt(Index.valP l_max). 
    have ? : LenNBytes.insubd (map NBytes.insubd (map (BitsToBytes \o DigestBlock.val) (DBLL.val s1.`1.`2.`2))) = s2.`1.`r_sig.`1.
    + rewrite H12 /= DBLL.insubdK;1: by rewrite size_map LenNBytes.valP eq_lens. 
      rewrite  -!map_comp /(\o) /=.
      have -> /= : (fun (x : nbytes) =>
        NBytes.insubd (BitsToBytes (DigestBlock.val (DigestBlock.insubd (BytesToBits (NBytes.val x)))))) = idfun.
      + apply fun_ext => x; rewrite DigestBlock.insubdK. 
        + rewrite /BytesToBits (size_flatten_ctt 8); last by rewrite size_map NBytes.valP.
          by move => xx; rewrite mapP => Hex;elim Hex;smt(@W8).
        by rewrite BytesToBitsK NBytes.valKd /#. 
      by rewrite map_id LenNBytes.valKd.
    have ? : AuthPath.insubd (rev (map NBytes.insubd (map (BitsToBytes \o DigestBlock.val) (DBHL.val s1.`1.`2.`3)))) = s2.`1.`r_sig.`2; last by smt().
    rewrite -!map_rev H13 -!map_comp /(\o) /=.
    have -> /= : (fun (x : nbytes) =>
        NBytes.insubd (BitsToBytes (DigestBlock.val (DigestBlock.insubd (BytesToBits (NBytes.val x)))))) = idfun.
    + apply fun_ext => x; rewrite DigestBlock.insubdK. 
      + rewrite /BytesToBits (size_flatten_ctt 8); last by rewrite size_map NBytes.valP.
        by move => xx; rewrite mapP => Hex;elim Hex;smt(@W8).
      by rewrite BytesToBitsK NBytes.valKd /#. 
    by rewrite map_id AuthPath.valKd.   
  + by smt(size_rcons).
  + by smt().

+ move => &2 ?;proc;conseq />. 
  by inline 1;wp;call (sign1_ll O); auto.
+ move => *;proc;wp;conseq (: _ ==> true);1:smt(size_rcons).
  by call(sign2_ll O).
+ conseq (: _ ==> ={res,glob O}); first by smt(). 
  by sim.

+ by move => *;proc*;call(:true);auto. 

auto => /> &1 &2 H1????????;do split.
+ move => *; do split;2:smt(). 
  have ? : pk{2}.`pk_pub_seed = pk{1}.`2 by smt().
  have ? : pk{2}.`pk_root = NBytes.insubd (BitsToBytes (DigestBlock.val pk{1}.`1)); last by smt().
+ rewrite H1 /bs2block DigestBlock.insubdK.
  + rewrite /BytesToBits (size_flatten_ctt 8); last by rewrite size_map NBytes.valP.
    move => x; rewrite mapP => Hex;elim Hex;smt(@W8).
  by rewrite BytesToBitsK NBytes.valKd.

by smt().
qed.
