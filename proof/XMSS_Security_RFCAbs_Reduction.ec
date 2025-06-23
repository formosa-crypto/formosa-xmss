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
lemma security &m  (O <: RO.Oracle  {-O_CMA_Default, -DSS_RFC.DSS.KeyUpdating.O_CMA_Default}) (A <: Adv_EUFCMA_RO {-O_CMA_Default, -DSS_RFC.DSS.KeyUpdating.O_CMA_Default, -O}):
    Pr [ EUF_CMA_RO(S,A,O_CMA_Default,O).main() @ &m : res ] <=
    Pr[DSS_RFC.KeyUpdatingROM.EUF_CMA_RO(XMSS_TW_RFC, B(A), DSS_RFC.DSS.KeyUpdating.O_CMA_Default, O).main
                   () @ &m : res].
proof. 
byequiv => //.
proc. 
seq 1 1 : (={glob A,glob O}); 1: by call(:true);auto.

inline {1} 1; inline {2} 1;inline {2} 3;inline {1} 4.

seq 3 4 : (O_Base_Default.qs{1} = DSS_RFC.DSS.O_Base_Default.qs{2} /\ pkrel pk{2} pk{1} /\ ={glob O} /\ m{1} = f{2}.`1 /\ f{2}.`2 = sig{1}); last first.
+ sp;case (0 <= to_uint sig0{1}.`sig_idx < l); last first. (* FIXME : WHO SHOULD BE CHECKING FOR THIS? *)
  + inline {1} 3;inline {2} 2;wp;conseq (: _ ==> true);1: by auto => />.
    admit. (* lossless; won't be needed once we sort out who's keeping track of indices *)
  wp;call(: ={glob O} /\ O_Base_Default.qs{1} = DSS_RFC.DSS.O_Base_Default.qs{2}); 1: by auto => /#.
  wp;call(: pkrel  arg{2}.`1 arg{1}.`1 /\ ={m,glob O} /\ sigrel arg{2}.`3 arg{1}.`3 ==> ={res});
    1: by symmetry;proc*;call(ver_eq O);auto => /#.
  auto =>  /> &1 &2 *;do split. 
  + by rewrite Index.insubdK;smt().
  + rewrite DBHL.insubdK /=;1: by rewrite size_rev size_map AuthPath.valP. 
    by rewrite revK.
  move => *. admit. (* EASY FIXME: we need to prove that O is preserved in the verify equiv *) 

call(: ={glob O} 
    /\ O_Base_Default.qs{1} = DSS_RFC.DSS.O_Base_Default.qs{2} 
    /\ (to_uint O_CMA_Default.sk{1}.`idx < 2 ^ h => skrel DSS_RFC.DSS.KeyUpdating.O_CMA_Default.sk{2} O_CMA_Default.sk{1} )).
+ symmetry;proc;inline {1} 1.
  exlim O_CMA_Default.sk{2}.`idx => _idx.
  wp; call (sig_eq O (to_uint _idx)).
  auto => /> &1 &2.
  have ? : to_uint O_CMA_Default.sk{2}.`idx < 2 ^ h  by  admit. (* query bounds *)
  move =>  H0;split;1:smt(). 
  move =>  H1 H2  H3 H4 H5 H6 s1 s2 O1 O2 H7 H8 H9 H10 H11 H12 ;do split.
  + have ? : W32.of_int (Index.val s1.`1.`2.`1) = s2.`1.`sig_idx.
    + apply W32.to_uint_eq; rewrite /= of_uintK /= -H8; smt(Index.valP l_max). 
    have ? : LenNBytes.insubd (map NBytes.insubd (map (BitsToBytes \o DigestBlock.val) (DBLL.val s1.`1.`2.`2))) = s2.`1.`r_sig.`1.
    + rewrite H9 /= DBLL.insubdK;1: by rewrite size_map LenNBytes.valP eq_lens. 
      rewrite  -!map_comp /(\o) /=.
      have -> /= : (fun (x : nbytes) =>
        NBytes.insubd (BitsToBytes (DigestBlock.val (DigestBlock.insubd (BytesToBits (NBytes.val x)))))) = idfun.
      + apply fun_ext => x; rewrite DigestBlock.insubdK. 
        + rewrite /BytesToBits (size_flatten_ctt 8); last by rewrite size_map NBytes.valP.
          by move => xx; rewrite mapP => Hex;elim Hex;smt(@W8).
        by rewrite BytesToBitsK NBytes.valKd /#. 
      by rewrite map_id LenNBytes.valKd.
    have ? : AuthPath.insubd (rev (map NBytes.insubd (map (BitsToBytes \o DigestBlock.val) (DBHL.val s1.`1.`2.`3)))) = s2.`1.`r_sig.`2; last by smt().
    rewrite -!map_rev H10 -!map_comp /(\o) /=.
    have -> /= : (fun (x : nbytes) =>
        NBytes.insubd (BitsToBytes (DigestBlock.val (DigestBlock.insubd (BytesToBits (NBytes.val x)))))) = idfun.
    + apply fun_ext => x; rewrite DigestBlock.insubdK. 
      + rewrite /BytesToBits (size_flatten_ctt 8); last by rewrite size_map NBytes.valP.
        by move => xx; rewrite mapP => Hex;elim Hex;smt(@W8).
      by rewrite BytesToBitsK NBytes.valKd /#. 
    by rewrite map_id AuthPath.valKd.      
  + admit. (* EASY FIXME: need to prove preservation of RO in signature *)
  + by smt().
  + conseq (: _ ==> ={res,glob O}); first by smt(). 
    by sim.
inline {1} 2; inline {2} 2;wp => /=.
inline {1} 1;wp;symmetry;call (kg_eq O).
auto => /> r1 r2 H1??????.
have ? : r2.`2.`pk_pub_seed = r1.`1.`2 by smt().
have ? : r2.`2.`pk_root = NBytes.insubd (BitsToBytes (DigestBlock.val r1.`1.`1)); last by smt().
+ rewrite H1 /bs2block DigestBlock.insubdK.
  + rewrite /BytesToBits (size_flatten_ctt 8); last by rewrite size_map NBytes.valP.
    move => x; rewrite mapP => Hex;elim Hex;smt(@W8).
  by rewrite BytesToBitsK NBytes.valKd.
qed.
