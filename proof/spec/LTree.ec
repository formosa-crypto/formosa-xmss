pragma Goals : printall.


require import AllCore List RealExp IntDiv Distr DList.
require (*--*) Subtype. 

from Jasmin require import JModel.
 
require import Params Address Hash WOTS.

op H_msg_padding_val : W64.t.

op H_msg (t : threen_bytes) (M : W8.t list) : nbytes =
  let padding : W8.t list = toByte_64 H_msg_padding_val n in
  Hash (padding ++ ThreeNBytesBytes.val t ++ M).

subtype wots_keys as WOTSKeys = { l : wots_sk list | size l = 2^h }.
realize inhabited.
proof.
exists (nseq (2^h) witness); rewrite size_nseq; smt(@IntDiv).
qed.

(* 4.1.5 L-Trees *)
(* takes as input a WOTS+ public key pk and compresses it to a single 
   n-byte value pk[0].
*)
module LTree = {
  proc ltree (pk : wots_pk, address : adrs, _seed : seed) : nbytes = {
    var pks : nbytes list;
    var pk_i : nbytes;
    var tmp : nbytes;
    var i : int;
    var _len : int;
    var tree_height : int;

    address <- set_tree_height address 0;
    pks <- LenNBytes.val pk;

    _len <- len;
    while (1 < _len) { (* Same as _len > 1 *)
      i <- 0;
      while (i < _len %/ 2) {
        address <- set_tree_index address i;
        pk_i <- nth witness pks (2*i);
        tmp <- nth witness pks (2*i + 1);
        pk_i <@ Hash.rand_hash (pk_i, tmp, _seed, address);
        pks <- put pks i pk_i;
        i <- i + 1;
      }

      if (_len %% 2 = 1) {
        pk_i <- nth witness pks (_len - 1);
        pks <- put pks (_len %/ 2) pk_i;
      }

      _len <- if _len %% 2 = 0 then _len %/ 2 else _len %/ 2 + 1;

      tree_height <- get_tree_height address;
      address <- set_tree_height address (tree_height + 1);
    }

    pk_i <- nth witness pks 0;

    return pk_i;
  }
}. 
