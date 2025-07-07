require import List.
require import XMSS_PRF.
require XMSS_Security_RFCAbs.

import Types XMSS_Types Address BaseW Hash WOTS LTree XMSS_TreeHash.
import Params OTSKeys.
import ThreeNBytesBytes AuthPath.

(* op prf_keygen : Params.nbytes -> Params.nbytes * Address.adrs -> Params.nbytes. *)
(* op rand_hash : seed -> Address.adrs -> Params.nbytes -> Params.nbytes -> Params.nbytes. *)

clone import XMSS_Security_RFCAbs as XMSSSecToAbs with
  type XMSSRFCAbs.auth_path <- auth_path,
  (* op XMSSRFCAbs.prf_keygen <- prf_keygen, *)
  op XMSSRFCAbs.prf <- prf,
  op XMSSRFCAbs.f <- f,
  (* op XMSSRFCAbs.rand_hash <- rand_hash, *)
  op XMSSRFCAbs.ltree <- ltree
  proof *.








