require import AllCore List RealExp IntDiv.
require (*  *) Subtype. 

require export XMSS_Params WOTS.

from Jasmin require import JModel.

require import Types Array8 LTree.
import Params.

subtype auth_path as AuthPath = { l : nbytes list | size l = h }.
realize inhabited.
proof.
by (exists (nseq h witness);smt(size_nseq ge0_h)).
qed.

type sig_t = { sig_idx : W32.t;
               r : nbytes ;
               r_sig : (wots_signature * auth_path) }.

(******************************************************************************)
