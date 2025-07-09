require import List.
require import XMSS_PRF.
require XMSS_Security_RFCAbs.

from Jasmin require import JModel.

import Params Types Address BaseW Hash WOTS LTree XMSS_TreeHash OTSKeys.
import ThreeNBytesBytes AuthPath.

(* op prf_keygen : Params.nbytes -> Params.nbytes * Address.adrs -> Params.nbytes. *)
(* op rand_hash : seed -> Address.adrs -> Params.nbytes -> Params.nbytes -> Params.nbytes. *)

clone import XMSS_Security_RFCAbs as XMSSSecToAbs with
  op XMSSRFCAbs.prf_keygen <- (fun (ss : nbytes) (psad : nbytes * adrs) =>
                                prf_keygen (NBytes.val psad.`1 ++ NBytes.val (addr_to_bytes psad.`2)) ss),  (* prf_keygen, *)
  op XMSSRFCAbs.prf <- prf,
  op XMSSRFCAbs.f <- f,
  op XMSSRFCAbs.rand_hash <- (fun (ps : seed) (ad : adrs) (l r : nbytes) => rand_hash l r ps ad),
  op XMSSRFCAbs.ltree <- ltree
proof *.

import XMSSRFCAbs.

module H_msg = {
  proc o(mkm : threen_bytes * W8.t list) : nbytes = {
    return H_msg mkm.`1 mkm.`2;
  }
}.

equiv kg_eqv :
  XMSS_RFC_Abs(H_msg).kg ~ XMSS_PRF.kg :
  ={arg} ==> ={res}.
proof. admitted.

equiv sig_eqv :
  XMSS_RFC_Abs(H_msg).sign ~ XMSS_PRF.sign :
  ={arg} ==> ={res}.
proof. admitted.

equiv ver_eqv :
  XMSS_RFC_Abs(H_msg).verify ~ XMSS_PRF.verify :
  ={arg} ==> ={res}.
proof. admitted.
