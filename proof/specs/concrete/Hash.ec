pragma Goals : printall.

require import AllCore List Distr RealExp IntDiv FinType.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

require import Params Types Address.

op Hash : W8.t list -> nbytes.

op prf_padding_val : W64.t.
op prf_kg_padding_val : W64.t.
op F_padding_val : W64.t.
op rand_hash_padding : W64.t = W64.one.

op padding_len : int.
axiom padding_len_ge0 : 0 <= padding_len.

op toByte_64(x : W64.t) (l : int) : W8.t list = 
  rev (mkseq (fun i => nth W8.zero (to_list (W8u8.unpack8 x)) i) l). 

op bytexor(a b : W8.t list) : W8.t list = 
   map (fun (ab : W8.t * W8.t) => ab.`1 `^` ab.`2) (zip a b).

op prf (in_0 key : nbytes): nbytes =
  let padding = toByte_64 prf_padding_val padding_len in
  let buf = padding ++ NBytes.val key ++ NBytes.val in_0 in
  Hash buf.

op prf_keygen (in_0 : W8.t list) (key : nbytes): nbytes =
  let padding = toByte_64 prf_kg_padding_val padding_len in
  let buf = padding ++ NBytes.val key ++ in_0 in
  Hash buf.

op _F (key t : nbytes): nbytes =
  let padding = toByte_64 F_padding_val padding_len in
  let buf = padding ++ NBytes.val key ++ NBytes.val t in
  Hash buf.

op rand_hash (_left _right : nbytes) (_seed : nbytes) (address : adrs) : nbytes =
  let padding = toByte_64 rand_hash_padding  padding_len in
  let address = set_key_and_mask address 0 in
  let addr_bytes = addr_to_bytes address in
  let key = prf addr_bytes _seed in
  let address = set_key_and_mask address 1 in
  let addr_bytes = addr_to_bytes address in
  let bitmask_0 = prf addr_bytes _seed in
  let address = set_key_and_mask address 2 in
  let addr_bytes = addr_to_bytes address in
  let bitmask_1 = prf addr_bytes _seed in
  let t = bytexor (NBytes.val _left ++ NBytes.val _right) (NBytes.val bitmask_0 ++ NBytes.val bitmask_1) in
  let buf = padding ++ NBytes.val key ++ t in
  Hash buf.

module Hash = {
  proc prf (in_0  key : nbytes) : nbytes = {
    var r : nbytes;
    var padding : W8.t list;
    var buf : W8.t list;

    padding <- toByte_64 prf_padding_val padding_len;
    buf <- padding ++ NBytes.val key ++ NBytes.val in_0;

    r <- Hash buf;

    return r;
  }


  proc prf_keygen (in_0 : W8.t list, key : nbytes) : nbytes = {
    var r : nbytes;
    var padding : W8.t list;
    var buf : W8.t list;

    padding <- toByte_64 prf_kg_padding_val padding_len;
    buf <- padding ++ NBytes.val key ++ in_0;

    r <- Hash buf;
    
    return r;

  }

  (* Here, t is nbytesxor tmp bitmask *)
  proc _F (key t : nbytes) : nbytes = {
    var r : nbytes;
    var buf : W8.t list;
    var padding : W8.t list;

    padding <- toByte_64 F_padding_val padding_len;
    buf <- padding ++ NBytes.val key ++ NBytes.val t;

    r <- Hash buf;

    return r;
  }

  proc rand_hash (_left _right : nbytes, _seed : nbytes, address : adrs) : nbytes = {
      var padding : W8.t list;
      var key : nbytes;
      var bitmask_0, bitmask_1 : nbytes;
      var buf, t : W8.t list; 
      var addr_bytes : nbytes;
      var r : W8.t list;
    
      padding <- toByte_64 rand_hash_padding  padding_len;

      address <- set_key_and_mask address 0;
      addr_bytes <- addr_to_bytes address;
      key <@ prf (addr_bytes, _seed);

      address <- set_key_and_mask address 1;
      addr_bytes <- addr_to_bytes address;
      bitmask_0 <@ prf (addr_bytes,  _seed);

      address <- set_key_and_mask address 2;
      addr_bytes <- addr_to_bytes address;
      bitmask_1 <@ prf (addr_bytes,  _seed);
    
      t <- bytexor (NBytes.val _left ++ NBytes.val _right) (NBytes.val bitmask_0 ++ NBytes.val bitmask_1);
      buf <- padding ++ NBytes.val key ++ t;
  
      return Hash buf;
  }
}.

hoare prf_eq in0 k:
  Hash.prf: in_0 = in0 /\ key = k ==> res = prf in0 k.
proof. by proc; auto. qed.

hoare prf_kg_eq in0 k:
  Hash.prf_keygen: in_0 = in0 /\ key = k ==> res = prf_keygen in0 k.
proof. by proc; auto. qed.

hoare _F_eq k t0:
  Hash._F: key = k /\ t = t0 ==> res = _F k t0.
proof. by proc; auto. qed.

hoare rand_hash_eq l r s a:
  Hash.rand_hash: _left = l /\ _right = r /\ _seed = s /\ address = a ==> res = rand_hash l r s a.
proof.
proc.
wp; ecall (prf_eq addr_bytes _seed).
wp; ecall (prf_eq addr_bytes _seed).
wp; ecall (prf_eq addr_bytes _seed).
by auto.
qed.
