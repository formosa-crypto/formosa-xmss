require import AllCore List.
require Subtype.
from Jasmin require import JModel.

require import Params.

type key = nbytes.
type seed = nbytes.

type wots_message = nbytes.
type wots_message_base_w = onebyte.
type wots_signature = len_nbytes.
type wots_pk = len_nbytes.
type wots_sk = len_nbytes.
type wots_keypair = wots_pk * wots_sk.

subtype wots_keys as WOTSKeys = { l : wots_sk list | size l = 2^h }.
realize inhabited.
proof.
exists (nseq (2^h) witness); rewrite size_nseq; smt(@IntDiv).
qed.

subtype wots_ots_keys as OTSKeys = { l : wots_sk list | size l = 2^h }.
realize inhabited.
proof.
by exists (nseq (2^h) witness); rewrite size_nseq; smt(ge0_h @IntDiv).
qed.

subtype auth_path as AuthPath = { l : nbytes list | size l = h }.
realize inhabited.
proof.
by (exists (nseq h witness);smt(size_nseq ge0_h)).
qed.

type xmss_sk = { idx : W32.t ;
                 sk_seed : nbytes ; (* secret *)
                 sk_prf : nbytes ;
                 pub_seed_sk : nbytes ; (* public *)
                 sk_root : nbytes }.

(* Same as single tree variant *)
type xmss_pk = { pk_oid : W32.t ;
                 pk_root : nbytes ;
                 pk_pub_seed : nbytes }.

type sig_t = { sig_idx : W32.t;
               r : nbytes ;
               r_sig : (wots_signature * auth_path) }.



clone import Subtype as Msg_t with
  type T <- W8.t list,
    op P <- fun wl => 0 <= size wl < mmb

proof *.
realize inhabited by exists []; smt(ge1_mmb).

type msg_t = Msg_t.sT.

type xmss_keypair = xmss_sk * xmss_pk.
