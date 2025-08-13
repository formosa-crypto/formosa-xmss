(* --- Require/Import --- *)
(* -- Built-In (Standard Library) -- *)
require import AllCore List Distr FinType BitEncoding.
require (*--*) ROM.
(*---*) import BS2Int.

(* -- Local -- *)
require (*--*) FL_XMSS_TW.
clone import FL_XMSS_TW as FLXMSSTW.
require (*--*) DigitalSignatures DigitalSignaturesROM KeyedHashFunctions HashThenSign.
(*---*) import SA WTW FLXMSSTW_EUFRMA.

(* --- Types --- *)
(* -- General -- *)
(*
  Seeds (i.e., indexing keys) for PRF that produces (pseudo)randomness
  (i.e., indexing keys) for message compression
*)
type mseed.

(* Indexing keys used for message compression (assumed to be finite) *)
type mkey.

clone import FinType as MKey with
  type t <= mkey.


(* -- XMSS-TW specific -- *)
(* Authentication paths in XMSS-TW binary hash tree *)
type apXMSSTW = apFLXMSSTW.

(* Public keys *)
type pkXMSSTW = pkFLXMSSTW.

(* Secret keys *)
type skXMSSTW = mseed * skFLXMSSTW.

(* Messages (assumed to be finite) *)
type msgXMSSTW.

clone import FinType as MsgXMSSTW with
  type t <= msgXMSSTW.

(* Signatures *)
type sigXMSSTW = mkey * sigFLXMSSTW.


(* -- Miscellaneous -- *)
(* Product type of indexing keys used for message compression and messages *)
clone import FinProdType as MKeyMsgXMSSTW with
  type t1 <- mkey,
  type t2 <- msgXMSSTW,
  theory FT1 <- MKey,
  theory FT2 <- MsgXMSSTW

  proof *.



(* --- Distributions --- *)
(* Proper distribution over seeds used for PRF that generates (pseudo)randomness for message compression *)
op [lossless] dmseed : mseed distr.

(* Proper, full, and uniform distribution over indexing keys used for message compression *)
op [lossless full uniform] dmkey : mkey distr.



(* --- Operators --- *)
(* PRF that generates indexing keys for message compression given a seed and an index *)
op mkg : mseed -> index -> mkey.


abstract theory Original.
(* -- Proof-specific -- *)
(* Hash-then-sign proof technique *)
clone import HashThenSign as HtS with
  type pk_fl_t <= pkFLXMSSTW,
  type sk_fl_t <= skFLXMSSTW,
  type msg_fl_t <= msgFLXMSSTW,
  type sig_fl_t <= sigFLXMSSTW,
  type rco_t <= mkey,
  type msg_al_t <= msgXMSSTW,
  type WithPRF.ms_t <= mseed,
  type WithPRF.id_t <= index,

    op n <- l,

    op WithPRF.mkg <= mkg,
    op WithPRF.extr_id <= fun (skfl : skFLXMSSTW) => skfl.`1,

    op dmsg_fl <= dmsgFLXMSSTW,
    op drco <= dmkey,
    op WithPRF.dms <= dmseed,

  theory RCO <= MKey,
  theory MSG_AL <= MsgXMSSTW

  proof *.
  realize ge0_n by smt(ge2_l).
  realize dmsg_fl_ll by exact: dmsgFLXMSSTW_ll.
  realize dmsg_fl_uni by exact: dmsgFLXMSSTW_uni.
  realize dmsg_fl_fu by exact: dmsgFLXMSSTW_fu.
  realize drco_ll by exact: dmkey_ll.
  realize drco_uni by exact: dmkey_uni.
  realize drco_fu by exact: dmkey_fu.
  realize WithPRF.dms_ll by exact: dmseed_ll.

import Repro MCORO MCOROLE.
import EUFRMAEqv DSS_FL DSS_FL_EUFRMA.
import WithPRF MKG MKG_PRF DSS_AL_PRF KeyUpdatingROM DSS KeyUpdating.
import WS.


(* --- XMSS-TW --- *)
(* Specification of XMSS-TW (assuming the message compression function is an RO) *)
module (XMSS_TW : Scheme_RO) (RO : POracle) = {
  proc keygen() : pkXMSSTW * skXMSSTW  = {
    var ms : mseed;
    var pk : pkXMSSTW;
    var skfl : skFLXMSSTW;
    var sk : skXMSSTW;

    ms <$ dmseed;

    (pk, skfl) <@ FL_XMSS_TW.keygen();

    sk <- (ms, skfl);

    return (pk, sk);
  }

  proc sign(sk : skXMSSTW, m : msgXMSSTW) : sigXMSSTW * skXMSSTW = {
    var ms : mseed;
    var skfl : skFLXMSSTW;
    var idx : index;
    var mk : mkey;
    var cm : msgFLXMSSTW;
    var sigfl: sigFLXMSSTW;
    var sig : sigXMSSTW;

    ms <- sk.`1;
    skfl <- sk.`2;

    idx <- skfl.`1;

    mk <- mkg ms idx;
    cm <@ RO.o((mk, m));

    (sigfl, skfl) <@ FL_XMSS_TW.sign(skfl, cm);

    sig <- (mk, sigfl);
    sk <- (ms, skfl);

    return (sig, sk);
  }

  proc verify(pk : pkXMSSTW, m : msgXMSSTW, sig : sigXMSSTW) : bool = {
    var mk : mkey;
    var sigfl : sigFLXMSSTW;
    var cm : msgFLXMSSTW;
    var ver : bool;

    mk <- sig.`1;
    sigfl <- sig.`2;

    cm <@ RO.o((mk, m));

    ver <@ FL_XMSS_TW.verify(pk, cm, sigfl);

    return ver;
  }
}.


(* --- Reduction adversaries --- *)
(*
module (R_PRF_EUFCMAROXMSSTW (A : Adv_EUFCMA_RO) : Adv_PRF) (O : Oracle_PRF) = {
  module O_CMA_R_PRF_EUFCMAROXMSSTW : SOracle_CMA = {
    include var O_Base_Default

    var skfl : skFLXMSSTW

    proc init(skfl_init : skFLXMSSTW) = {
      skfl <- skfl_init;
      qs <- [];
    }

    proc sign(m : msgXMSSTW) : sigXMSSTW = {
      var idx : index;
      var mk : mkey;
      var cm : msgFLXMSSTW;
      var sigfl : sigFLXMSSTW;
      var sig : sigXMSSTW;

      idx <- skfl.`1;

      mk <@ O.query(idx);

      cm <@ MCO.o(mk, m);

      (sigfl, skfl) <@ FL_XMSS_TW.sign(skfl, cm);

      sig <- (mk, sigfl);

      return sig;
    }
  }

  proc distinguish() : bool = {
    var pk : pkXMSSTW;
    var skfl : skFLXMSSTW;
    var m : msgXMSSTW;
    var sig : sigXMSSTW;
    var is_valid, is_fresh;

    MCO.init();

    (pk, skfl) <@ FL_XMSS_TW.keygen();

    O_CMA_R_PRF_EUFCMAROXMSSTW.init(skfl);

    (m, sig) <@ A(MCO, O_CMA_R_PRF_EUFCMAROXMSSTW).forge(pk);

    is_valid <@ XMSS_TW(MCO).verify(pk, m, sig);

    is_fresh <@ O_CMA_R_PRF_EUFCMAROXMSSTW.fresh(m);

    return is_valid /\ is_fresh;
  }
}.
*)

(* --- Proofs of EUF-CMA property for XMSS-TW (assuming message compression is a RO) --- *)
section Proofs_EUF_CMA_RO_XMSSTW.
(* -- Declarations -- *)
(* Models the signing procedure of FL-XMSS-TW *)
declare op opsign : skFLXMSSTW -> msgFLXMSSTW -> sigFLXMSSTW * skFLXMSSTW.

(* opsign precisely captures the semantics of the signing procedure of FL-XMSS-TW *)
declare axiom FLXMSSTW_sign_fun (skfl : skFLXMSSTW) (cm : msgFLXMSSTW) :
  hoare[FL_XMSS_TW.sign: arg = (skfl, cm) ==> res = opsign skfl cm].

(* The signing procedure of FL-XMSS-TW is lossless (and captured by opsign) *)
local lemma FLXMSSTW_sign_pfun (skfl : skFLXMSSTW) (cm : msgFLXMSSTW) :
  phoare[FL_XMSS_TW.sign: arg = (skfl, cm) ==> res = opsign skfl cm] = 1%r.
proof. by conseq FLXMSSTW_sign_ll (FLXMSSTW_sign_fun skfl cm). qed.

(* Adversary against EUF-CMA in the ROM *)
declare module A <: Adv_EUFCMA_RO{-FL_XMSS_TW, -ERO, -O_CMA_Default, -O_METCR, -R_EUFCMARO_CRRO, -R_EUFCMARO_METCRRO, -Repro.Wrapped_Oracle, -Repro.RepO, -O_RMA_Default, -R_EUFCMARO_IEUFRMA, -QC_A, -Lazy.LRO, -Repro.ReproGame, -R_EUFRMA_IEUFRMA, -R_PRF_EUFCMARO, -O_PRF_Default, -DSS_AL.DSS.KeyUpdating.O_CMA_Default, -PRF_SK_PRF.O_PRF_Default, -FC.O_THFC_Default, -FC_PRE.O_SMDTPRE_Default, -FC_TCR.O_SMDTTCR_Default, -FC_UD.O_SMDTUD_Default, -O_MEUFGCMA_WOTSTWES, -PKCOC.O_THFC_Default, -PKCOC_TCR.O_SMDTTCR_Default, -TRHC.O_THFC_Default, -TRHC_TCR.O_SMDTTCR_Default, -R_SMDTUDC_Game23WOTSTWES, -R_SMDTTCRC_Game34WOTSTWES, -R_PRF_FLXMSSTWESInlineNOPRF, -R_SMDTPREC_Game4WOTSTWES, -R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF, -R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF, -R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF, -R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF, -R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES}.

(* The adversary always terminates if the oracle procedures it can call terminate *)
declare axiom A_forge_ll (RO <: POracle{-A}) (SO <: SOracle_CMA{-A}) :
  islossless RO.o => islossless SO.sign => islossless A(RO, SO).forge.

(* Number of allowed signature queries *)
declare op qS : { int | 0 <= qS <= l } as rng_qS.

(* Number of allowed random oracle (hash) queries *)
declare op qH : { int | 0 <= qH } as ge0_qH.

(* The adversary makes a limited number of queries to the given random (hash) oracle and signing oracle *)
declare axiom A_forge_queries (RO <: POracle{-A, -QC_A}) (SO <: SOracle_CMA{-A, -QC_A}) :
  hoare[A(QC_A(A, RO, SO).QC_RO, QC_A(A, RO, SO).QC_SO).forge :
    QC_A.cH = 0 /\ QC_A.cS = 0 ==> QC_A.cH <= qH /\ QC_A.cS <= qS].


(* -- Security theorems -- *)
(*
  High-level security theorem (based on EUF-RMA of FL-XMSS-TW):
  XMSS-TW is EUF-CMA secure in the ROM if mkg (i.e., the function that generates
  indexing keys for the message compression function) is a PRF, MCO (i.e., the message
  compression function) is a "collision-resistant random oracle", and FL-XMSS-TW is EUF-RMA
  secure
*)
lemma EUFCMARO_XMSSTW_EUFRMA &m :
  Pr[EUF_CMA_RO(XMSS_TW, A, O_CMA_Default, MCO).main() @ &m : res]
  <=
  `| Pr[PRF(R_PRF_EUFCMARO(FL_XMSS_TW, A), O_PRF_Default).main(false) @ &m : res] -
     Pr[PRF(R_PRF_EUFCMARO(FL_XMSS_TW, A), O_PRF_Default).main(true) @ &m : res] |
  +
  Pr[CR_RO(R_EUFCMARO_CRRO(FL_XMSS_TW, A), MCO).main() @ &m : res]
  +
  Pr[EUF_RMA(FL_XMSS_TW, R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A))).main() @ &m : res]
  +
  qS%r * (qS + qH + 1)%r * mu1 dmkey witness
  +
  l%r * mu1 dmsgFLXMSSTW witness.
proof.
have ->:
  Pr[EUF_CMA_RO(XMSS_TW, A, O_CMA_Default, MCO).main() @ &m : res]
  =
  Pr[EUF_CMA_RO(WithPRF.AL_KU_DSS(FL_XMSS_TW), A, O_CMA_Default, MCO).main() @ &m : res].
+ byequiv => //.
  proc; inline{1} 2; inline{2} 2.
  seq 5 5 : (={O_Base_Default.qs, m, is_valid}); last by sim.
  inline{1} 5; inline{2} 5.
  inline{1} 11; inline{2} 11.
  wp; call(: true) => />; 1: by sim.
  wp; call(: ={ERO.m}) => />; 1: by wp.
  wp; call(: ={O_Base_Default.qs, O_CMA_Default.sk, ERO.m}) => />; first 2 by sim.
  inline *.
  wp; while (={ss1, ss0, ps1, ps0, ms, leafl0, ad0, ERO.m}); 1: by sim.
  wp; do 3! rnd.
  while (={w, ERO.m}); 1: by wp; rnd; wp; skip.
  by wp; skip.
move: (ALKUDSS_EUFCMARO_PRF_CRRO_EUFRMA FL_XMSS_TW FLXMSSTW_sign_ll FLXMSSTW_verify_ll qS rng_qS qH ge0_qH).
move=> /(_ (fun (skfl : skFLXMSSTW) => skfl.`1 = Index.insubd 0)
           (fun (skfl : skFLXMSSTW) => (Index.insubd (Index.val skfl.`1 + 1), skfl.`2, skfl.`3, skfl.`4))
           opsign _ FLXMSSTW_sign_fun _ _ _ _).
+ proc; inline *.
  wp; while (true).
  - wp; while (true); 1: by wp.
    wp; while (true); 1: by wp.
    by wp.
  by wp; do 2! rnd; skip.
+ move=> skfl.
  proc; inline *.
  wp => />; while (true).
  - wp; while (true); 1: by wp.
    wp; while (true); 1: by wp.
    by wp.
  wp; while (true); 1: by wp.
  wp; while (true); 1: by wp.
  by wp; skip.
+ move=> i j skfl /= init_sk [ge0i leqS_i] [ge0_j leqS_j] neqj_i.
  have fupd_it:
    forall (k : int), 0 <= k => k < qS =>
      (fold (fun (sk : skFLXMSSTW) =>
        ((Index.insubd ((Index.val sk.`1) + 1)), sk.`2, sk.`3, sk.`4)) skfl k).`1
      =
      Index.insubd k.
  - elim => [@/fupd | k ge0_k @/fupd ih ltqS_k1].
    * by rewrite fold0.
    rewrite foldS //= ih 2:Index.insubdK //; smt(rng_qS).
  rewrite fupd_it // fupd_it //.
  move: neqj_i; apply contra => eqins_ij.
  by rewrite -(Index.insubdK i) 2:-(Index.insubdK j) 3:eqins_ij; 1,2: smt(rng_qS).
+ by sim.
+ by sim.
by move=> /(_ A A_forge_ll A_forge_queries &m).
qed.


(*
  Low-level security theorem (based on properties of KHFs and THFs)
  XMSS-TW is EUF-CMA secure in the ROM if mkg (i.e., the function that generates
  indexing keys for the message compression function) is a PRF; MCO (i.e., the message
  compression function) is a "collision-resistant random oracle"; prf_sk (i.e., the
  function used to generate WOTS-TW secret keys) is a PRF; f (i.e., the function used
  in the WOTS-TW chains) has SM-DT-UD-C, SM-DT-TCR-C, and SM-DT-PRE-C; pkco (i.e., the
  fucntion used to compress WOTS-TW public keys to leaves of the binary hash tree) has
  SM-DT-TCR-C; and trh (i.e., the function used to construct the full binary hash tree from
  the leaves) has SM-DT-TCR-C.
*)
lemma EUFCMARO_XMSSTW &m :
  Pr[EUF_CMA_RO(XMSS_TW, A, O_CMA_Default, MCO).main() @ &m : res]
  <=
  `| Pr[MKG_PRF.PRF(R_PRF_EUFCMARO(FL_XMSS_TW, A), O_PRF_Default).main(false) @ &m : res] -
     Pr[MKG_PRF.PRF(R_PRF_EUFCMARO(FL_XMSS_TW, A), O_PRF_Default).main(true) @ &m : res] |
  +
  Pr[CR_RO(R_EUFCMARO_CRRO(FL_XMSS_TW, A), MCO).main() @ &m : res]
  +
  `|Pr[PRF_SK_PRF.PRF(R_PRF_FLXMSSTWESInlineNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A)))), PRF_SK_PRF.O_PRF_Default).main(false) @ &m : res] -
  Pr[PRF_SK_PRF.PRF(R_PRF_FLXMSSTWESInlineNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A)))), PRF_SK_PRF.O_PRF_Default).main(true) @ &m : res]|
  +
  (w - 2)%r *
`|Pr[FC_UD.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A))))), FC_UD.O_SMDTUD_Default, FC.O_THFC_Default).main(false) @ &m : res] -
  Pr[FC_UD.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A))))), FC_UD.O_SMDTUD_Default, FC.O_THFC_Default).main(true) @ &m : res]|
  +
  Pr[FC_TCR.SM_DT_TCR_C(R_SMDTTCRC_Game34WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A))))), FC_TCR.O_SMDTTCR_Default, FC.O_THFC_Default).main() @ &m : res]
  +
  Pr[FC_PRE.SM_DT_PRE_C(R_SMDTPREC_Game4WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A))))), FC_PRE.O_SMDTPRE_Default, FC.O_THFC_Default).main() @ &m : res]
  +
  Pr[PKCOC_TCR.SM_DT_TCR_C(R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A)))), PKCOC_TCR.O_SMDTTCR_Default, PKCOC.O_THFC_Default).main() @ &m : res]
  +
  Pr[TRHC_TCR.SM_DT_TCR_C(R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A)))), TRHC_TCR.O_SMDTTCR_Default, TRHC.O_THFC_Default).main() @ &m : res]
  +
  qS%r * (qS + qH + 1)%r * mu1 dmkey witness
  +
  l%r * mu1 dmsgFLXMSSTW witness.
proof.
move: (EUFRMA_FLXMSSTW (R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A))) _ &m) (EUFCMARO_XMSSTW_EUFRMA &m); last first.
have -> /#:
  Pr[FLXMSSTW_EUFRMA.EUF_RMA(FL_XMSS_TW, R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A))).main() @ &m : res]
  =
  Pr[EUF_RMA(FL_XMSS_TW, R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A))).main() @ &m : res].
+ by byequiv => //; sim.
proc; inline *.
wp; call (: true).
+ by move=> RO SO ROll SOll; apply (A_forge_ll RO SO).
+ proc; inline *.
  wp; rnd; skip => />.
  by apply dmkey_ll.
+ proc; inline *.
  by wp; skip.
wp; while (true) (size w).
+ move=> z.
  wp; rnd; wp; skip => /> &1 neqel_w.
  split; 2: by apply dmsgFLXMSSTW_ll.
  by elim: (w{1}) neqel_w => //= /#.
by wp; skip => />; smt(size_eq0 size_ge0).
qed.

end section Proofs_EUF_CMA_RO_XMSSTW.

end Original.


(* Specification closer aligned with the RFC *)
theory RFC.
(*---*) import SA.RFC FMap.

type pkXMSSTWRFC = pkFLXMSSTWRFC.
type skXMSSTWRFC = mseed * skFLXMSSTWRFC.
(* type msgXMSSTWRFC = msgXMSSTW. *)
(* type sigXMSSTWRFC = sigXMSSTW. *)

clone import DigitalSignaturesROM as DSS_RFC with
  type pk_t <- pkXMSSTWRFC,
  type sk_t <- skXMSSTWRFC,
  type msg_t <- msgXMSSTW,
  type sig_t <- sigXMSSTW,

  type in_t <- mkey * (dgstblock * index * msgXMSSTW),
  type out_t <- msgFLXMSSTW,
  type d_in_t <- unit,
  type d_out_t <- bool,

  op doutm <- fun _ => dmsgFLXMSSTW
proof *.


module (XMSS_TW_RFC : DSS_RFC.KeyUpdatingROM.Scheme_RO) (RO : DSS_RFC.RO.POracle) = {
  proc keygen() : pkXMSSTWRFC * skXMSSTWRFC = {
    var ms : mseed;
    var pk : pkXMSSTWRFC;
    var skfl : skFLXMSSTWRFC;
    var sk : skXMSSTWRFC;

    ms <$ dmseed;
    (pk, skfl) <@ FL_XMSS_TW_RFC.keygen();
    sk <- (ms, skfl);

    return (pk, sk);
  }

  proc sign(sk : skXMSSTWRFC, m : msgXMSSTW) : sigXMSSTW * skXMSSTWRFC = {
    var ms : mseed;
    var skfl : skFLXMSSTWRFC;
    var idx : index;
    var root : dgstblock;
    var mk : mkey;
    var cm : msgFLXMSSTW;
    var sigfl : sigFLXMSSTW;
    var sig : sigXMSSTW;

    ms <- sk.`1;
    skfl <- sk.`2;
    idx <- skfl.`1;
    root <- skfl.`3.`1;
    mk <- mkg ms idx;
    (* TODO: cm <@ RO.o((mk, root, idx), m); *)
    cm <@ RO.o(mk, (root, idx, m));
    (sigfl, skfl) <@ FL_XMSS_TW_RFC.sign(skfl, cm);
    sig <- (mk, sigfl);
    sk <- (ms, skfl);

    return (sig, sk);
  }

  proc verify(pk : pkXMSSTWRFC, m : msgXMSSTW, sig : sigXMSSTW) : bool = {
    var mk : mkey;
    var sigfl : sigFLXMSSTW;
    var idx : index;
    var root : dgstblock;
    var cm : msgFLXMSSTW;
    var ver : bool;

    root <- pk.`1;
    mk <- sig.`1;
    sigfl <- sig.`2;
    idx <- sigfl.`1;
    (* TODO: cm <@ RO.o((mk, root, idx), m); *)
    cm <@ RO.o(mk, (root, idx, m));
    ver <@ FL_XMSS_TW_RFC.verify(pk, cm, sigfl);

    return ver;
  }
}.

clone FinType as IndexFT with
  type t <= index,
  op enum <= map Index.insubd (range 0 l)

proof *.
realize enum_spec.
move=> x; rewrite count_uniq_mem.
+ rewrite map_inj_in_uniq 2:range_uniq => x0 y0 /mem_range x0in /mem_range y0in eqind.
  by rewrite -(Index.insubdK _ x0in) -(Index.insubdK _ y0in) eqind.
rewrite mapP /b2i (: exists (x0 : int), (x0 \in range 0 l) /\ x = Index.insubd x0) 2://.
by exists (Index.val x); rewrite mem_range Index.valP Index.valKd.
qed.

clone FinProdType as DBIDX with
  type t1 <= dgstblock,
  type t2 <= index,

  theory FT1 <= DigestBlockFT,
  theory FT2 <= IndexFT

proof *.

clone FinProdType as DBIDXMSGNested with
  type t1 <= dgstblock * index,
  type t2 <= msgXMSSTW,

  theory FT1 <= DBIDX,
  theory FT2 <= MsgXMSSTW

proof *.

clone FinType as DBIDXMSG with
  type t <= dgstblock * index * msgXMSSTW,
  op enum <= map (fun (dbim : (_ * _) * _) => (dbim.`1.`1, dbim.`1.`2, dbim.`2)) DBIDXMSGNested.enum

proof *.
realize enum_spec.
move => dbim; rewrite count_map /preim.
by rewrite -(DBIDXMSGNested.enum_spec ((dbim.`1, dbim.`2), dbim.`3)) /#.
qed.

(* -- Proof-specific -- *)
(* Hash-then-sign proof technique *)
clone import HashThenSign as HtSRFC with
  type pk_fl_t <= pkFLXMSSTWRFC,
  type sk_fl_t <= skFLXMSSTWRFC,
  type msg_fl_t <= msgFLXMSSTW,
  type sig_fl_t <= sigFLXMSSTW,
  type rco_t <= mkey,
  type msg_al_t <= dgstblock * index * msgXMSSTW,
  type WithPRF.ms_t <= mseed,
  type WithPRF.id_t <= index,

    op n <- l,

    op WithPRF.mkg <= mkg,
    op WithPRF.extr_id <= fun (skfl : skFLXMSSTWRFC) => skfl.`1,

    op dmsg_fl <= dmsgFLXMSSTW,
    op drco <= dmkey,
    op WithPRF.dms <= dmseed,

  theory RCO <= MKey,
  theory MSG_AL <= DBIDXMSG

  proof *.
  realize ge0_n by smt(ge2_l).
  realize dmsg_fl_ll by exact: dmsgFLXMSSTW_ll.
  realize dmsg_fl_uni by exact: dmsgFLXMSSTW_uni.
  realize dmsg_fl_fu by exact: dmsgFLXMSSTW_fu.
  realize drco_ll by exact: dmkey_ll.
  realize drco_uni by exact: dmkey_uni.
  realize drco_fu by exact: dmkey_fu.
  realize WithPRF.dms_ll by exact: dmseed_ll.

import Repro MCORO MCOROLE.
import EUFRMAEqv DSS_FL DSS_FL_EUFRMA.
import WithPRF MKG MKG_PRF DSS_AL_PRF KeyUpdatingROM DSS KeyUpdating.
import WS.
(*
module (R_PRF_EUFCMAROXMSSTWRFC (A : Adv_EUFCMA_RO) : Adv_PRF) (O : Oracle_PRF) = {
  module O_CMA_R_PRF_EUFCMAROXMSSTWRFC : SOracle_CMA = {
    include var O_Base_Default

    var skfl : skFLXMSSTWRFC

    proc init(skfl_init : skFLXMSSTWRFC) = {
      skfl <- skfl_init;
      qs <- [];
    }

    proc sign(dbim : dgstblock * index * msgXMSSTW) : sigXMSSTW = {
      var idx : index;
      var mk : mkey;
      var cm : msgFLXMSSTW;
      var sigfl : sigFLXMSSTW;
      var sig : sigXMSSTW;

      idx <- skfl.`1;

      mk <@ O.query(idx);

      cm <@ MCO.o(mk, dbim);

      (sigfl, skfl) <@ FL_XMSS_TW_RFC.sign(skfl, cm);

      sig <- (mk, sigfl);

      return sig;
    }
  }

  proc distinguish() : bool = {
    var pk : pkXMSSTWRFC;
    var skfl : skFLXMSSTWRFC;
    var dbim : dgstblock * index * msgXMSSTW;
    var sig : sigXMSSTW;
    var is_valid, is_fresh;

    MCO.init();

    (pk, skfl) <@ FL_XMSS_TW_RFC.keygen();

    O_CMA_R_PRF_EUFCMAROXMSSTWRFC.init(skfl);

    (dbim, sig) <@ A(MCO, O_CMA_R_PRF_EUFCMAROXMSSTWRFC).forge(pk);

    is_valid <@ XMSS_TW_RFC(MCO).verify(pk, dbim.`3, sig);

    is_fresh <@ O_CMA_R_PRF_EUFCMAROXMSSTWRFC.fresh(dbim);

    return is_valid /\ is_fresh;
  }
}.
*)

module (QC_A_RFC (A : DSS_RFC.KeyUpdatingROM.Adv_EUFCMA_RO) : DSS_RFC.KeyUpdatingROM.Adv_EUFCMA_RO)
                 (RO : DSS_RFC.RO.POracle)
                 (O : DSS_RFC.DSS.KeyUpdating.SOracle_CMA) = {
  var cS : int
  var cH : int

  module QC_SO = {
    proc sign(m : msgXMSSTW) : sig_al_t = {
      var sig : sig_al_t;

      cS <- cS + 1;
      sig <@ O.sign(m);

      return sig;
    }
  }

  module QC_RO = {
    proc o(x : mkey * (dgstblock * index * msgXMSSTW)) : msgFLXMSSTW = {
      var cm : msgFLXMSSTW;

      cH <- cH + 1;
      cm <@ RO.o(x);

      return cm;
    }
  }

  proc forge(pk : pk_al_t) : msgXMSSTW * sig_al_t = {
    var m : msgXMSSTW;
    var sig : sig_al_t;

    cS <- 0;
    cH <- 0;
    (m, sig) <@ A(QC_RO, QC_SO).forge(pk);

    return (m, sig);
  }
}.

module (R_EUFCMA_EUFCMARFC (A : DSS_RFC.KeyUpdatingROM.Adv_EUFCMA_RO) : Adv_EUFCMA_RO)
       (RO : RO.POracle) (O : SOracle_CMA) = {
  var root : dgstblock
  var idx : index

  module R_O : DSS_RFC.DSS.KeyUpdating.SOracle_CMA = {
    proc sign(m : msgXMSSTW) : sigXMSSTW = {
      var sig : sigXMSSTW;

      sig <@ O.sign((root, idx, m));

      idx <- Index.insubd (Index.val idx + 1);

      return sig;
    }
  }

  proc forge(pk : pkXMSSTWRFC) : (dgstblock * index * msgXMSSTW) * sigXMSSTW = {
    var ps : pseed;
    var m : msgXMSSTW;
    var sig : sigXMSSTW;

    (root, ps) <- pk;
    idx <- Index.insubd 0;

    (m, sig) <@ QC_A_RFC(A, RO, R_O).forge(pk);

    return ((root, sig.`2.`1, m), sig);
  }
}.


(* --- Proofs of EUF-CMA property for XMSS-TW (assuming message compression is a RO) --- *)
section Proofs_EUF_CMA_RO_XMSSTWRFC.
(* -- Declarations -- *)
(* Models the signing procedure of FL-XMSS-TW *)
declare op opsign : skFLXMSSTWRFC -> msgFLXMSSTW -> sigFLXMSSTW * skFLXMSSTWRFC.

(* opsign precisely captures the semantics of the signing procedure of FL-XMSS-TW *)
declare axiom FLXMSSTWRFC_sign_fun (skfl : skFLXMSSTWRFC) (cm : msgFLXMSSTW) :
  hoare[FL_XMSS_TW_RFC.sign: arg = (skfl, cm) ==> res = opsign skfl cm].

(* The signing procedure of FL-XMSS-TW is lossless (and captured by opsign) *)
local lemma FLXMSSTWRFC_sign_pfun (skfl : skFLXMSSTWRFC) (cm : msgFLXMSSTW) :
  phoare[FL_XMSS_TW_RFC.sign: arg = (skfl, cm) ==> res = opsign skfl cm] = 1%r.
proof. by conseq FLXMSSTWRFC_sign_ll (FLXMSSTWRFC_sign_fun skfl cm). qed.

(* Adversary against EUF-CMA in the ROM *)
declare module A <: DSS_RFC.KeyUpdatingROM.Adv_EUFCMA_RO{
    -FL_XMSS_TW_RFC, -ERO, -O_CMA_Default, -O_METCR, -R_EUFCMA_EUFCMARFC, -R_EUFCMARO_CRRO,
    -R_EUFCMARO_METCRRO, -Repro.Wrapped_Oracle, -Repro.RepO, -O_RMA_Default,
    -R_EUFCMARO_IEUFRMA, -QC_A, -QC_A_RFC, -Lazy.LRO, -Repro.ReproGame, -R_EUFRMA_IEUFRMA,
    -R_PRF_EUFCMARO, -O_PRF_Default, -DSS_AL.DSS.KeyUpdating.O_CMA_Default,
    -DSS_RFC.DSS.KeyUpdating.O_CMA_Default,
    -PRF_SK_PRF.O_PRF_Default, -FC.O_THFC_Default, -FC_PRE.O_SMDTPRE_Default,
    -FC_TCR.O_SMDTTCR_Default, -FC_UD.O_SMDTUD_Default, -O_MEUFGCMA_WOTSTWES,
    -PKCOC.O_THFC_Default, -PKCOC_TCR.O_SMDTTCR_Default, -TRHC.O_THFC_Default,
    -TRHC_TCR.O_SMDTTCR_Default, -R_SMDTUDC_Game23WOTSTWES, -R_SMDTTCRC_Game34WOTSTWES,
    -R_PRF_FLXMSSTWESInlineNOPRF, -R_SMDTPREC_Game4WOTSTWES, -R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF,
    -R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF, -R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF,
    -R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF, -R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES
}.

(* The adversary always terminates if the oracle procedures it can call terminate *)
declare axiom A_forge_ll (RO <: DSS_RFC.RO.POracle{-A}) (SO <: DSS_RFC.DSS.KeyUpdating.SOracle_CMA{-A}) :
  islossless RO.o => islossless SO.sign => islossless A(RO, SO).forge.

local lemma R_forge_ll (RO <: POracle{-R_EUFCMA_EUFCMARFC(A)}) (SO <: SOracle_CMA{-R_EUFCMA_EUFCMARFC(A)}) :
  islossless RO.o => islossless SO.sign => islossless R_EUFCMA_EUFCMARFC(A, RO, SO).forge.
proof.
move => RO_ll SO_ll.
proc.
inline 3; wp.
call (A_forge_ll
      (<: QC_A_RFC(A, RO, R_EUFCMA_EUFCMARFC(A, RO, SO).R_O).QC_RO)
      (<: QC_A_RFC(A, RO, R_EUFCMA_EUFCMARFC(A, RO, SO).R_O).QC_SO)) => //.
+ by proc; call RO_ll; wp.
+ by proc; inline 2; wp; call SO_ll; wp.
by wp.
qed.

(* Number of allowed signature queries *)
declare op qS : { int | 0 <= qS <= l } as rng_qS.

(* Number of allowed random oracle (hash) queries *)
declare op qH : { int | 0 <= qH } as ge0_qH.

(* The adversary makes a limited number of queries to the given random (hash) oracle and signing oracle *)
declare axiom A_forge_queries (RO <: DSS_RFC.RO.POracle{-A, -QC_A_RFC}) (SO <: DSS_RFC.DSS.KeyUpdating.SOracle_CMA{-A, -QC_A_RFC}) :
  hoare[A(QC_A_RFC(A, RO, SO).QC_RO, QC_A_RFC(A, RO, SO).QC_SO).forge :
    QC_A_RFC.cH = 0 /\ QC_A_RFC.cS = 0 ==> QC_A_RFC.cH <= qH /\ QC_A_RFC.cS <= qS].

local lemma R_forge_queries (RO <: POracle{-R_EUFCMA_EUFCMARFC(A), -QC_A})
                            (SO <: SOracle_CMA{-R_EUFCMA_EUFCMARFC(A), -QC_A}) :
  hoare[R_EUFCMA_EUFCMARFC(A, QC_A(R_EUFCMA_EUFCMARFC(A), RO, SO).QC_RO, QC_A(R_EUFCMA_EUFCMARFC(A), RO, SO).QC_SO).forge :
    QC_A.cH = 0 /\ QC_A.cS = 0 ==> QC_A.cH <= qH /\ QC_A.cS <= qS].
proof.
proc.
inline 3; wp; sp.
call (_:
      QC_A_RFC.cS = QC_A.cS /\ QC_A_RFC.cH = QC_A.cH
      /\ QC_A_RFC.cS = 0 /\ QC_A_RFC.cH = 0
      ==>
      QC_A.cH <= qH /\ QC_A.cS <= qS) => //.
conseq (: QC_A_RFC.cS = QC_A.cS /\ QC_A_RFC.cH = QC_A.cH
         ==>
         QC_A_RFC.cS = QC_A.cS /\ QC_A_RFC.cH = QC_A.cH)
       (A_forge_queries
        (<: QC_A(R_EUFCMA_EUFCMARFC(A), RO, SO).QC_RO)
        (<: R_EUFCMA_EUFCMARFC(A, QC_A(R_EUFCMA_EUFCMARFC(A), RO, SO).QC_RO, QC_A(R_EUFCMA_EUFCMARFC(A), RO, SO).QC_SO).R_O)) => //.
proc (QC_A_RFC.cS = QC_A.cS /\ QC_A_RFC.cH = QC_A.cH) => //.
+ proc.
  inline 2; inline 3.
  by wp; call (_: true); wp.
proc.
inline 2.
by wp; call (_: true); wp.
qed.
(*
local module R_EUFCMA_EUFCMARFC_QS (RO : RO.POracle) (O : SOracle_CMA) = {
  include var R_EUFCMA_EUFCMARFC(A, RO, O) [-forge]

  proc forge(pk : pkXMSSTWRFC) : (dgstblock * index * msgXMSSTW) * sigXMSSTW = {
    var ps : pseed;
    var m : msgXMSSTW;
    var sig : sigXMSSTW;

    (root, ps) <- pk;
    idx <- Index.insubd 0;

    (m, sig) <@ QC_A_RFC(A, RO, R_EUFCMA_EUFCMARFC(A, RO, O).R_O).forge(pk);

    return ((root, sig.`2.`1, m), sig);
  }
}.

local lemma EqPr_RQS &m :
  Pr[EUF_CMA_RO(WithPRF.AL_KU_DSS(FL_XMSS_TW_RFC), R_EUFCMA_EUFCMARFC(A), O_CMA_Default, MCO).main() @ &m : res]
  =
  Pr[EUF_CMA_RO(WithPRF.AL_KU_DSS(FL_XMSS_TW_RFC), R_EUFCMA_EUFCMARFC_QS, O_CMA_Default, MCO).main() @ &m : res].
proof.
byequiv => //.
proc.
inline main; inline{1} 4; inline{2} 4; inline{2} 7.
seq 7 11: ( ={sig0, pk, m0, R_EUFCMA_EUFCMARFC.root, O_Base_Default.qs, ERO.m}); last by sim.
wp.
call (_: ={glob O_CMA_Default, glob R_EUFCMA_EUFCMARFC, ERO.m}).
+ proc.
  by inline{2} 2; sim.
+ proc.
  by inline{2} o; wp.
by conseq />; sim.
qed.

local lemma R_forge_ll (RO <: POracle{-R_EUFCMA_EUFCMARFC_QS}) (SO <: SOracle_CMA{-R_EUFCMA_EUFCMARFC_QS}) :
  islossless RO.o => islossless SO.sign => islossless R_EUFCMA_EUFCMARFC_QS(RO, SO).forge.
proof.
move=> RO_ll SO_ll.
proc.
inline 3; wp; sp.
call (A_forge_ll
      (<: QC_A_RFC(A, RO, R_EUFCMA_EUFCMARFC(A, RO, SO).R_O).QC_RO)
      (<: QC_A_RFC(A, RO, R_EUFCMA_EUFCMARFC(A, RO, SO).R_O).QC_SO)).
+ proc; call RO_ll; by wp.
+ proc; inline 2; wp.
  by call SO_ll; wp.
by wp.
qed.

local lemma R_forge_queries (RO <: POracle{-R_EUFCMA_EUFCMARFC_QS, -QC_A})
                            (SO <: SOracle_CMA{-R_EUFCMA_EUFCMARFC_QS, -QC_A}) :
  hoare[R_EUFCMA_EUFCMARFC_QS(QC_A(R_EUFCMA_EUFCMARFC_QS, RO, SO).QC_RO, QC_A(R_EUFCMA_EUFCMARFC_QS, RO, SO).QC_SO).forge :
    QC_A.cH = 0 /\ QC_A.cS = 0 ==> QC_A.cH <= qH /\ QC_A.cS <= qS].
proof.
proc.
inline 3.
wp; sp.
call (_:
      QC_A_RFC.cS = QC_A.cS /\ QC_A_RFC.cH = QC_A.cH
      /\ QC_A_RFC.cS = 0 /\ QC_A_RFC.cH = 0
      ==>
      QC_A.cH <= qH /\ QC_A.cS <= qS) => //.
conseq (: QC_A_RFC.cS = QC_A.cS /\ QC_A_RFC.cH = QC_A.cH
         ==>
         QC_A_RFC.cS = QC_A.cS /\ QC_A_RFC.cH = QC_A.cH)
       (A_forge_queries
        (<: QC_A(R_EUFCMA_EUFCMARFC_QS, RO, SO).QC_RO)
        (<: R_EUFCMA_EUFCMARFC(A, QC_A(R_EUFCMA_EUFCMARFC_QS, RO, SO).QC_RO, QC_A(R_EUFCMA_EUFCMARFC_QS, RO, SO).QC_SO).R_O)) => //.
proc (QC_A_RFC.cS = QC_A.cS /\ QC_A_RFC.cH = QC_A.cH) => //.
+ proc.
  inline 2; inline 3.
  by wp; call (_: true); wp.
proc.
inline 2.
by wp; call (_: true); wp.
qed.

*)
(* local module EUF_CMA_RO_R = { *)
(*   proc main() : bool = { *)
(*     var pk : pk_al_t; *)
(*     var sk : WithPRF.sk_al_t; *)
(*     var m : dgstblock * index * msgXMSSTW; *)
(*     var sig : sig_al_t; *)
(*     var is_valid : bool; *)
(*     var is_fresh : bool; *)

(*     MCO.init(); *)

(*     (pk, sk) <@ WithPRF.AL_KU_DSS(FL_XMSS_TW_RFC, MCO).keygen(); *)
(*     DSS_AL_PRF.DSS.KeyUpdating.O_CMA_Default(WithPRF.AL_KU_DSS(FL_XMSS_TW_RFC, MCO)).init(sk); *)

(*     (m, sig) <@ R_EUFCMA_EUFCMARFC(A, MCO, DSS_AL_PRF.DSS.KeyUpdating.O_CMA_Default(WithPRF.AL_KU_DSS(FL_XMSS_TW_RFC, MCO))).forge(pk); *)

(*     is_valid <@ WithPRF.AL_KU_DSS(FL_XMSS_TW_RFC, MCO).verify(pk, m, sig); *)
(*     is_fresh <@ DSS_AL_PRF.DSS.KeyUpdating.O_CMA_Default(WithPRF.AL_KU_DSS(FL_XMSS_TW_RFC, MCO)).fresh(m); *)

(*     return is_valid /\ is_fresh; *)
(*   } *)
(* }. *)

(* -- Security theorems -- *)
(*
  High-level security theorem (based on EUF-RMA of FL-XMSS-TW-RFC):
  XMSS-TW-RFC is EUF-CMA secure in the ROM if mkg (i.e., the function that generates
  indexing keys for the message compression function) is a PRF, MCO (i.e., the message
  compression function) is a "collision-resistant random oracle", and FL-XMSS-TW-RFC is EUF-RMA
  secure
*)
lemma EUFCMARO_XMSSTWRFC_EUFRMA &m :
  Pr[DSS_RFC.KeyUpdatingROM.EUF_CMA_RO(XMSS_TW_RFC, A, DSS_RFC.DSS.KeyUpdating.O_CMA_Default, MCO).main() @ &m : res]
  <=
  `| Pr[PRF(R_PRF_EUFCMARO(FL_XMSS_TW_RFC, R_EUFCMA_EUFCMARFC(A)), O_PRF_Default).main(false) @ &m : res] -
     Pr[PRF(R_PRF_EUFCMARO(FL_XMSS_TW_RFC, R_EUFCMA_EUFCMARFC(A)), O_PRF_Default).main(true) @ &m : res] |
  +
  Pr[CR_RO(R_EUFCMARO_CRRO(FL_XMSS_TW_RFC, R_EUFCMA_EUFCMARFC(A)), MCO).main() @ &m : res]
  +
  Pr[EUF_RMA(FL_XMSS_TW_RFC, R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(R_EUFCMA_EUFCMARFC(A)))).main() @ &m : res]
  +
  qS%r * (qS + qH + 1)%r * mu1 dmkey witness
  +
  l%r * mu1 dmsgFLXMSSTW witness.
proof.
have LePrR_A:
  Pr[DSS_RFC.KeyUpdatingROM.EUF_CMA_RO(XMSS_TW_RFC, A, DSS_RFC.DSS.KeyUpdating.O_CMA_Default, MCO).main() @ &m : res]
  <=
  Pr[EUF_CMA_RO(WithPRF.AL_KU_DSS(FL_XMSS_TW_RFC), R_EUFCMA_EUFCMARFC(A), O_CMA_Default, MCO).main() @ &m : res].
+ byequiv => //.
  proc.
  inline main.
  inline fresh verify.
  inline{2} 4; inline{2} 7.
  wp; call (: true); 1: by sim.
  wp; call (: ={ERO.m}); 1: by wp.
  wp; call (:  ={ERO.m}
            /\ DSS_RFC.DSS.KeyUpdating.O_CMA_Default.sk{1} = O_CMA_Default.sk{2}
            /\ DSS_RFC.DSS.KeyUpdating.O_CMA_Default.sk{1}.`2.`3.`1 = R_EUFCMA_EUFCMARFC.root{2}
            /\ DSS_RFC.DSS.KeyUpdating.O_CMA_Default.sk{1}.`2.`1 = R_EUFCMA_EUFCMARFC.idx{2}
            /\ (forall m,
                m \in DSS_RFC.DSS.O_Base_Default.qs{1}
                <=>
                m \in map (fun (q : _ * _ * _) => q.`3) O_Base_Default.qs{2})).
  proc.
  wp.
  inline{1} 1.
  inline{2} 2; inline{2} 3.
  inline sign.
  (* wp; call (_: DSS_RFC.DSS.KeyUpdating.O_CMA_Default.sk{1} = O_CMA_Default.sk{2} *)
  (*           /\ O_CMA_Default.sk{1}.`2.`3.`1 = R_EUFCMA_EUFCMARFC.root{2} *)
  (*           /\ O_CMA_Default.sk{1}.`2.`1 = Index.insubd R_EUFCMA_EUFCMARFC.idx{2}). *)
  (* + inline sign. *)
  (*   wp 19 19. *)
  wp; call (_: true); 1: by sim.
  wp; while (={skWOTS0, em, ps0, ad0} /\ sig3{1} = sig5{2}); 1: by sim.
  wp; call (_: true); 1: by sim.
  wp; call (_: ={ERO.m}); 1: by wp.
  wp; skip => &1 &2 /> eqqs _ _ _ mx.
  rewrite mem_rcons mapP /=; split.
  + case => [->|].
    exists ((O_CMA_Default.sk{2}.`2.`3.`1, O_CMA_Default.sk{2}.`2.`1, m{2})); smt(mem_rcons).
  move=> mxin.
  move/iffLR: (eqqs mx) => /(_ mxin).
  rewrite mapP => -[x] [xin /=] eq3.
  exists x; smt(mem_rcons).
  move => -[x] []; rewrite mem_rcons /= => -[-> //|].
  rewrite eqqs mapP => t d; right.
  exists x => /#.
  by proc; inline o; wp.
  seq 1 1 : (={glob A, ERO.m}); 1: by sim.
  inline init; wp.
  inline keygen; wp; call (_: true); 1: by sim.
  auto => &1 &2 /> ms msin ss ssin ps psin sigw /> ->.
  rewrite /sko2skr /pko2pkr /pkr2pko /= => msig qs1 qs2 sk eqskvl qsrel.
  rewrite &(contra) qsrel mapP; pose tup := (_, _, _).
  move=> tp; exists tup => /#.
move: (ALKUDSS_EUFCMARO_PRF_CRRO_EUFRMA FL_XMSS_TW_RFC FLXMSSTWRFC_sign_ll FLXMSSTWRFC_verify_ll qS rng_qS qH ge0_qH).
move=> /(_ (fun (skfl : skFLXMSSTWRFC) => skfl.`1 = Index.insubd 0)
           (fun (skfl : skFLXMSSTWRFC) => (Index.insubd (Index.val skfl.`1 + 1), skfl.`2, skfl.`3))
           opsign _ FLXMSSTWRFC_sign_fun _ _ _ _).
+ proc; inline *.
  wp; while (true).
  - wp; while (true); 1: by wp.
    wp; while (true); 1: by wp.
    by wp.
  by wp; do 2! rnd; skip.
+ move=> skfl.
  proc; inline *.
  wp => />; while (true).
  - wp; while (true); 1: by wp.
    wp; while (true); 1: by wp.
    by wp.
  wp; while (true); 1: by wp.
  wp; while (true); 1: by wp.
  by wp; skip.
+ move=> i j skfl /= init_sk [ge0i leqS_i] [ge0_j leqS_j] neqj_i.
  have fupd_it:
    forall (k : int), 0 <= k => k < qS =>
      (fold (fun (sk : skFLXMSSTWRFC) =>
        ((Index.insubd ((Index.val sk.`1) + 1)), sk.`2, sk.`3)) skfl k).`1
      =
      Index.insubd k.
  - elim => [@/fupd | k ge0_k @/fupd ih ltqS_k1].
    * by rewrite fold0.
    rewrite foldS //= ih 2:Index.insubdK //; smt(rng_qS).
  rewrite fupd_it // fupd_it //.
  move: neqj_i; apply contra => eqins_ij.
  by rewrite -(Index.insubdK i) 2:-(Index.insubdK j) 3:eqins_ij; 1,2: smt(rng_qS).
+ by sim.
+ by sim.
move=> /(_ (R_EUFCMA_EUFCMARFC(A)) R_forge_ll R_forge_queries &m) /#.
qed.

(*
  Low-level security theorem (based on properties of KHFs and THFs)
  XMSS-TW is EUF-CMA secure in the ROM if mkg (i.e., the function that generates
  indexing keys for the message compression function) is a PRF; MCO (i.e., the message
  compression function) is a "collision-resistant random oracle"; prf_sk (i.e., the
  function used to generate WOTS-TW secret keys) is a PRF; f (i.e., the function used
  in the WOTS-TW chains) has SM-DT-UD-C, SM-DT-TCR-C, and SM-DT-PRE-C; pkco (i.e., the
  fucntion used to compress WOTS-TW public keys to leaves of the binary hash tree) has
  SM-DT-TCR-C; and trh (i.e., the function used to construct the full binary hash tree from
  the leaves) has SM-DT-TCR-C.
*)
lemma EUFCMARO_XMSSTWRFC &m :
  Pr[DSS_RFC.KeyUpdatingROM.EUF_CMA_RO(XMSS_TW_RFC, A, DSS_RFC.DSS.KeyUpdating.O_CMA_Default, MCO).main() @ &m : res]
  <=
  `| Pr[MKG_PRF.PRF(R_PRF_EUFCMARO(FL_XMSS_TW_RFC, R_EUFCMA_EUFCMARFC(A)), O_PRF_Default).main(false) @ &m : res] -
     Pr[MKG_PRF.PRF(R_PRF_EUFCMARO(FL_XMSS_TW_RFC, R_EUFCMA_EUFCMARFC(A)), O_PRF_Default).main(true) @ &m : res] |
  +
  Pr[CR_RO(R_EUFCMARO_CRRO(FL_XMSS_TW_RFC, R_EUFCMA_EUFCMARFC(A)), MCO).main() @ &m : res]
  +
  `|Pr[PRF_SK_PRF.PRF(R_PRF_FLXMSSTWESInlineNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMAFLXMSSTWRFC_EUFRMAFLXMSSTW(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(R_EUFCMA_EUFCMARFC(A)))))), PRF_SK_PRF.O_PRF_Default).main(false) @ &m : res] -
    Pr[PRF_SK_PRF.PRF(R_PRF_FLXMSSTWESInlineNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMAFLXMSSTWRFC_EUFRMAFLXMSSTW(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(R_EUFCMA_EUFCMARFC(A)))))), PRF_SK_PRF.O_PRF_Default).main(true) @ &m : res]|
  +
  (w - 2)%r *
  `|Pr[FC_UD.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMAFLXMSSTWRFC_EUFRMAFLXMSSTW(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(R_EUFCMA_EUFCMARFC(A))))))), FC_UD.O_SMDTUD_Default, FC.O_THFC_Default).main(false) @ &m : res] -
    Pr[FC_UD.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMAFLXMSSTWRFC_EUFRMAFLXMSSTW(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(R_EUFCMA_EUFCMARFC(A))))))), FC_UD.O_SMDTUD_Default, FC.O_THFC_Default).main(true) @ &m : res]|
  +
  Pr[FC_TCR.SM_DT_TCR_C(R_SMDTTCRC_Game34WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMAFLXMSSTWRFC_EUFRMAFLXMSSTW(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(R_EUFCMA_EUFCMARFC(A))))))), FC_TCR.O_SMDTTCR_Default, FC.O_THFC_Default).main() @ &m : res]
  +
  Pr[FC_PRE.SM_DT_PRE_C(R_SMDTPREC_Game4WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMAFLXMSSTWRFC_EUFRMAFLXMSSTW(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(R_EUFCMA_EUFCMARFC(A))))))), FC_PRE.O_SMDTPRE_Default, FC.O_THFC_Default).main() @ &m : res]
  +
  Pr[PKCOC_TCR.SM_DT_TCR_C(R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMAFLXMSSTWRFC_EUFRMAFLXMSSTW(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(R_EUFCMA_EUFCMARFC(A)))))), PKCOC_TCR.O_SMDTTCR_Default, PKCOC.O_THFC_Default).main() @ &m : res]
  +
  Pr[TRHC_TCR.SM_DT_TCR_C(R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMAFLXMSSTWRFC_EUFRMAFLXMSSTW(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(R_EUFCMA_EUFCMARFC(A)))))), TRHC_TCR.O_SMDTTCR_Default, TRHC.O_THFC_Default).main() @ &m : res]
  +
  qS%r * (qS + qH + 1)%r * mu1 dmkey witness
  +
  l%r * mu1 dmsgFLXMSSTW witness.
proof.
move: (EUFRMA_FLXMSSTWRFC (R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(R_EUFCMA_EUFCMARFC(A)))) _ &m) (EUFCMARO_XMSSTWRFC_EUFRMA &m); last first.
have -> /#:
  Pr[FLXMSSTWRFC_EUFRMA.EUF_RMA(FL_XMSS_TW_RFC, R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(R_EUFCMA_EUFCMARFC(A)))).main() @ &m : res]
  =
  Pr[EUF_RMA(FL_XMSS_TW_RFC, R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(R_EUFCMA_EUFCMARFC(A)))).main() @ &m : res].
+ by byequiv => //; sim.
proc; inline *.
wp; call (: true).
+ by move=> RO SO ROll SOll; apply (A_forge_ll RO SO).
+ proc; inline *.
  auto => />.
  by apply dmkey_ll.
+ proc; inline *.
  by wp; skip.
wp; while (true) (size w).
+ move=> z.
  wp; rnd; wp; skip => /> &1 neqel_w.
  split; 2: by apply dmsgFLXMSSTW_ll.
  by elim: (w{1}) neqel_w => //= /#.
by wp; skip => />; smt(size_eq0 size_ge0).
qed.

end section Proofs_EUF_CMA_RO_XMSSTWRFC.
end RFC.
