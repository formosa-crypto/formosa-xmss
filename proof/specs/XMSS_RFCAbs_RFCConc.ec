require import AllCore List IntDiv.
require import XMSS_PRF.
require XMSS_Security_RFCAbs.

from Jasmin require import JModel.

import Params Types Address BaseW Hash WOTS LTree XMSS_TreeHash OTSKeys.
import ThreeNBytesBytes AuthPath.

clone import XMSS_Security_RFCAbs as XMSSSecToAbs with
  op XMSSRFCAbs.prf_keygen <- (fun (ss : nbytes) (psad : nbytes * adrs) =>
                                prf_keygen (NBytes.val psad.`1 ++ NBytes.val (addr_to_bytes psad.`2)) ss),
  op XMSSRFCAbs.prf <- fun ss idx => prf idx ss,
  op XMSSRFCAbs.f <- f,
  op XMSSRFCAbs.rand_hash <- (fun (ps : seed) (ad : adrs) (l r : nbytes) => rand_hash l r ps ad),
  op XMSSRFCAbs.ltree <- ltree
proof *.

import XMSSRFCAbs.


module H_msg = {
  proc o(mkm : threen_bytes * msg_t) : nbytes = {
    return H_msg mkm.`1 mkm.`2;
  }
}.


equiv sample_randomness_eqv :
  XMSS_RFC_Abs(H_msg).sample_randomness ~ XMSS_PRF.sample_randomness :
   true
   ==>
   ={res}.
proof. by sim. qed.

lemma chain_ll1 : islossless Chain.chain.
proof.
proc => //.
by while (true) (s - chain_count); by auto => /#.
qed.

lemma chain_ll2 : islossless Top.WOTS.Chain.chain.
proof.
proc => //.
while (true) (s - chain_count).
+ move=> z; inline.
  by auto => /#.
by auto => /#.
qed.

lemma chain_eq1_ph1 _X _i _s _se _ad:
  phoare[ Chain.chain : arg = (_X, _i, _s, _se, _ad)
         ==> res = Top.XMSSSecToAbs.XMSSRFCAbs.chain _X _i _s _se _ad] = 1%r.
proof.
conseq chain_ll1 (chain_eq _X _i _s _se _ad). progress.
qed.

lemma chain_eq2_ph1 _X _i _s _se _ad:
  phoare[ Top.WOTS.Chain.chain: arg = (_X, _i, _s, _se, _ad)
         ==> res = Top.WOTS.chain _X _i _s _se _ad] = 1%r.
proof.
by conseq chain_ll2 (Top.WOTS.chain_eq _X _i _s _se _ad).
qed.

equiv chain_eqv :
  Chain.chain ~ Top.WOTS.Chain.chain :
  ={arg} ==> ={res}.
proof.
proc*.
ecall{1} (chain_eq1_ph1 X{1} i{1} s{1} _seed{1} address{1}).
ecall{2} (chain_eq2_ph1 X{2} i{2} s{2} _seed{2} address{2}).
by auto => &1 &2 />; rewrite chain_ch chain_eq_ch_f.
qed.

equiv pseudorandom_gensk_eqv :
  WOTS.pseudorandom_genSK ~ Top.WOTS.WOTS.pseudorandom_genSK : ={arg} ==> ={res}.
proof.
proc.
while (={i, address, sk, seed, sk_seed}).
+ by wp; inline prf_keygen; auto => />.
by auto.
qed.

equiv wots_pkgen_eqv :
  WOTS.pkGen ~ Top.WOTS.WOTS.pkGen : ={arg} ==> ={res}.
proof.
proc => //.
while (={i, address, _seed, pk, wots_skey}).
+ wp; call (chain_eqv).
  by auto => />; smt(w_vals).
by call (pseudorandom_gensk_eqv); auto => />.
qed.

lemma rand_hash_ll : islossless Hash.rand_hash.
proof. by proc; inline prf; wp. qed.

lemma ltree_ll1 : islossless LTree.ltree.
proof.
proc.
wp; while (1 <= _len <= len) (_len - 1).
+ move=> z.
  wp.
  while (0 <= i <= _len %/ 2) (_len %/ 2 - i).
  + move=> z'.
    wp; call rand_hash_ll.
    by auto => &1 /#.
  by auto => />; smt(divz_ge0).
auto => &1 />; smt(gt2_len).
qed.

lemma ltree_eq_ph1 (s0 : seed) (a0 : adrs) (pk0 : wots_pk):
  phoare[ LTree.ltree : pk = pk0 /\ _seed = s0 /\ address = a0 ==> res = ltree s0 a0 pk0] = 1%r.
proof. by conseq ltree_ll1 (ltree_eq s0 a0 pk0). qed.

lemma rand_hash_eq_ph1 (l r s : nbytes) (a : adrs) :
  phoare[ Hash.rand_hash : _left = l /\ _right = r /\ _seed = s /\ address = a ==> res = rand_hash l r s a] = 1%r.
proof. by conseq rand_hash_ll (rand_hash_eq l r s a). qed.

equiv treehash_eqv :
  TreeHash.treehash ~ XMSS_TreeHash.TreeHash.treehash :
   ={arg}
   ==>
   ={res}.
proof.
proc=> //.
wp; while (={i, address, sk_seed, pub_seed, stack, heights, offset, s, t}).
+ wp; while (={i, address, sk_seed, pub_seed, stack, heights, offset, s, t}).
  + wp; ecall{2} (rand_hash_eq_ph1 node0{2} node1{2} pub_seed{2} address{2}).
    by wp.
  wp; ecall{2} (ltree_eq_ph1 pub_seed{2} address{2} pk{2}).
  wp; call wots_pkgen_eqv.
  by auto.
by auto.
qed.

equiv kg_eqv :
  XMSS_RFC_Abs(H_msg).kg ~ XMSS_PRF.kg :
  ={arg} ==> ={res}.
proof.
proc => //.
by wp; call (treehash_eqv); wp; call (sample_randomness_eqv); wp.
qed.

equiv wots_checksum_eqv :
  WOTS.checksum ~ Top.WOTS.WOTS.checksum :
  ={arg}
  ==>
  ={res}.
proof. by sim. qed.

module WOTS_Encode = {
  proc encode(m : W8.t list) : int list = {
    var msg, csum, csum_32, len_2_bytes, csum_bytes, csum_base_w;

    (* Convert message to base w *)
    msg <@ BaseW.base_w(m, len1);

    (* Compute checksum *)
    csum <@ WOTS.checksum(msg);
    csum_32 <- W32.of_int csum;

    (* Convert checksum to base w *)
    csum_32 <- csum_32 `<<` W8.of_int ( 8 - ( ( len2 * log2_w) ) %% 8 );
    len_2_bytes <- ceil( ( len2 * log2_w )%r / 8%r );

    (* msg = msg || base_w(toByte(csum_32, len_2_bytes), w, len_2); *)
    csum_bytes <- toByte csum_32 len_2_bytes;
    csum_base_w <@ BaseW.base_w(csum_bytes, len2);
    msg <- msg ++ csum_base_w;

    return msg;
  }
}.

lemma gt_exprsbde (x n m : int) :
  1 < x => 0 <= n < m => x ^ n < x ^ m.
proof.
move=> gt1_x [ge0_n gtn_m].
have ge0_m: 0 <= m by smt().
elim: n ge0_n m ge0_m gtn_m => [| i ge0_i ih m ge0_m gti1_m].
+ by elim => [/# | *]; rewrite expr0 StdOrder.IntOrder.exprn_egt1 /#.
rewrite exprD_nneg // expr1 (: m = m - 1 + 1) // exprD_nneg 1:/# // expr1.
by rewrite StdOrder.IntOrder.ltr_pmul2r 2:(ih (m - 1)) /#.
qed.

equiv basew_eqv_range m l :
  BaseW.base_w ~ BaseW.base_w :
  ={arg} /\ X{1} = m /\ outlen{1} = l
  /\ 0 <= l
  ==>
  ={res} /\ size res{1} = l /\ all (fun x => 0 <= x < w) res{1}.
proof.
proc.
while (   #post
       /\ ={consumed, X, _in, out, total, bits, outlen}
       /\ 0 <= out{1} <= size base_w{1}
       /\ out{1} = consumed{1}
       /\ size base_w{1} = outlen{1}).
+ auto => &1 &2 /> allbsw ge0_out lebasew_out ltlen_cons.
  rewrite ?size_put /= -?(all_nthP _ _ witness) ?size_put.
  split => [| neq0_bits]; split => [ | /# | | /#] i rngi /=.
  + rewrite nth_put 1://; case (consumed{2} = i) => ?; 2: smt(all_nthP).
    rewrite /w and_mod 1:ge0_log2_w to_uintK_small modz_ge0 2:/=; 1,3,4: smt(logw_vals StdOrder.IntOrder.expr_gt0).
    rewrite (StdOrder.IntOrder.ltr_trans (2 ^ log2_w)) 1: ltz_pmod 1:StdOrder.IntOrder.expr_gt0 1://.
    by case: logw_vals => -> //.
  rewrite nth_put 1://; case (consumed{2} = i) => ?; 2: smt(all_nthP).
  rewrite /w and_mod 1:ge0_log2_w to_uintK_small modz_ge0 2:/=; 1,3,4: smt(logw_vals StdOrder.IntOrder.expr_gt0).
  rewrite (StdOrder.IntOrder.ltr_trans (2 ^ log2_w)) 1: ltz_pmod 1:StdOrder.IntOrder.expr_gt0 1://.
  by case: logw_vals => -> //.
auto => &1 &2 /> ge0_outlen.
by rewrite size_nseq lez_maxr 1:// 1:/= all_nseq /=; smt(w_vals).
qed.

equiv encode_eqv_ge0 :
  WOTS_Encode.encode ~ WOTS_Encode.encode
  : ={arg} ==> ={res} /\ size res{1} = len /\ all (fun x => 0 <= x < w) res{1}.
proof.
proc => //.
wp; ecall (basew_eqv_range csum_bytes{1} len2).
wp; inline checksum.
wp; while (={i, m0, checksum}); 1: by sim.
wp; ecall (basew_eqv_range m{1} len1).
auto => &1 &2 />.
rewrite ge0_len1 ge0_len2 /= => r0 szr0 allr i /lezNgt gelen1i _ r1 szr1 allr1.
by rewrite size_cat szr0 szr1 /len /= all_cat.
qed.

equiv wots_signseed_eqv :
  WOTS.sign_seed ~ Top.WOTS.WOTS.sign_seed : ={arg} ==> ={res}.
proof.
proc => //.
while (  ={i, address, pub_seed, msg, wots_skey, sig}
       /\ all ((<=) 0) msg{1}
       /\ 0 <= i{1} <= len
       /\ size msg{1} = len).
+ wp; call (chain_eqv).
  by auto => />; smt(all_nthP).
rewrite equiv [{2} 2 - (pseudorandom_gensk_eqv)].
outline{1} [3 .. 10] by { msg <@ WOTS_Encode.encode(M); }.
outline{2} [3 .. 10] by { msg <@ WOTS_Encode.encode(M); }.
wp; call (encode_eqv_ge0); call (: true); 1: by sim.
auto => &1 &2 />; smt(all_nthP w_vals gt2_len).
qed.

equiv buildauthpath_eqv :
  TreeSig.buildAuthPath ~ XMSS_TreeHash.TreeSig.buildAuthPath :
   ={arg}
   ==>
   ={res}.
proof.
proc.
while (={j, pub_seed, sk_seed, address, authentication_path, idx}).
+ by wp; call treehash_eqv; auto.
by wp.
qed.

equiv treesig_eqv :
  TreeSig.treesig ~ XMSS_TreeHash.TreeSig.treesig :
   ={arg}
   ==>
   ={res}.
proof.
proc=> //.
by call (wots_signseed_eqv); wp; call (buildauthpath_eqv); wp.
qed.

equiv sig_eqv :
  XMSS_RFC_Abs(H_msg).sign ~ XMSS_PRF.sign :
  ={arg} ==> ={res}.
proof.
proc.
inline{1} o.
wp; call (treesig_eqv); inline prf.
by auto.
qed.

equiv pkfromsig_eqv :
  WOTS.pkFromSig ~ Top.WOTS.WOTS.pkFromSig :
   ={arg}
   ==>
   ={res}.
proof.
proc => //.
while (  ={i, address, msg, _seed, tmp_pk, sig}
       /\ all (fun x => 0 <= x < w) msg{1}
       /\ 0 <= i{1} <= len
       /\ size msg{1} = len).
+ wp; call (chain_eqv).
  auto => />; smt(all_nthP w_vals).
rewrite equiv [{2} 3 - (wots_checksum_eqv)].
+ outline{1} [2 .. 9] by { msg <@ WOTS_Encode.encode(NBytes.val M); }.
  outline{2} [2 .. 9] by { msg <@ WOTS_Encode.encode(NBytes.val M); }.
  wp; call (encode_eqv_ge0).
  by auto => &1 &2 />; smt(gt2_len).
call (: true); 1: by sim.
by wp.
qed.

equiv rootfromsig_eqv :
  RootFromSig.rootFromSig ~ XMSS_TreeHash.RootFromSig.rootFromSig
  : ={arg} ==> ={res}.
proof.
proc.
while (={k, address, _seed, idx_sig, auth, nodes0}).
+ sp 1 1; if => //.
  + wp; ecall{2} (rand_hash_eq_ph1 nodes0{2} auth_k{2} _seed{2} address{2}).
    by auto.
  wp; ecall{2} (rand_hash_eq_ph1 auth_k{2} nodes0{2} _seed{2} address{2}).
  by auto.
wp; ecall{2} (ltree_eq_ph1 _seed{2} address{2}  pk_ots{2}).
by wp; call (pkfromsig_eqv); auto => &1 &2 />.
qed.

equiv ver_eqv :
  XMSS_RFC_Abs(H_msg).verify ~ XMSS_PRF.verify :
  ={arg} ==> ={res}.
proof.
proc => //.
by wp; call (rootfromsig_eqv); inline o; wp.
qed.
