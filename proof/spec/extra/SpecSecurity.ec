require import AllCore List Distr DList.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

require (****) XMSS_TW.
require import XMSS_PRF.
import Params Types XMSS_Types Hash WOTS Address LTree BaseW.

op BitsToBytes (bits : bool list) : W8.t list = map W8.bits2w (chunk W8.size bits).
op BytesToBits (bytes : W8.t list) : bool list = flatten (map W8.w2bits bytes).
op W64toBytes_ext (x : W64.t) (l : int) : W8.t list = 
  rev (mkseq (fun i => nth W8.zero (to_list (W8u8.unpack8 x)) i) l). 

(* Get checksum from XMXX_Checksum and then plug those results
   here *)
clone import XMSS_TW as XMSS_ABSTRACT with
   type mseed <- nbytes,
   op dmseed <- (dmap ((dlist W8.dword Params.n)) NBytes.insubd),
   type mkey <- nbytes * int,
   type msgXMSSTW <- W8.t list,
   type FLXMSSTW.SA.WTW.pseed <- nbytes,
   op FLXMSSTW.SA.WTW.dpseed <- (dmap ((dlist W8.dword n)) NBytes.insubd),
   type FLXMSSTW.SA.WTW.sseed <- nbytes,
   op FLXMSSTW.SA.WTW.dsseed <- (dmap ((dlist W8.dword n)) NBytes.insubd),
   type FLXMSSTW.SA.WTW.adrs <- adrs,
   op FLXMSSTW.n <- n,
   op FLXMSSTW.h <- h,
   op mkg = (fun (ms : nbytes) (i : FLXMSSTW.SA.index) => 
          let padding =  W64toBytes_ext prf_padding_val padding_len in
          let in_0 = toByte (W32.of_int (FLXMSSTW.SA.Index.val i)) 4 in   
          (Hash (padding ++ NBytes.val ms ++ in_0),FLXMSSTW.SA.Index.val i)).


import FLXMSSTW SA WTW HtS Repro MCORO. 

module FakeRO : POracle = {
   var root : nbytes

   proc o(x : (nbytes * int) * W8.t list) : msgFLXMSSTW = {
      var t,idx_bytes;
      idx_bytes <- toByte (W32.of_int x.`1.`2) 4;   
      t <- (ThreeNBytesBytes.insubd (NBytes.val x.`1.`1 ++ NBytes.val root ++ idx_bytes));
      return DigestBlock.insubd (BytesToBits (NBytes.val (H_msg t x.`2)));
   }
}.

op skrel(ask : skXMSSTW, sk : xmss_sk) =
   ask.`1 = sk.`sk_seed /\
   ask.`2.`1 = Index.insubd (to_uint sk.`idx) /\
   ask.`2.`2 = sk.`sk_prf  /\
   ask.`2.`3 = sk.`pub_seed_sk
   (* ask.`2.`4 = ??? Why is the address in/not in the sk/pk? *)
   (* ??? = sk.`pk_root Why is the root not in/in the sk? *).

op pkrel(apk : pkXMSSTW, pk : xmss_pk) = 
   apk.`1 = DigestBlock.insubd (BytesToBits (NBytes.val pk.`pk_root)) /\
   apk.`2 = pk.`pk_pub_seed
   (* apk.`3 = ??? Why is the address in the sk/pk? *)
   (* ??? = pk.`pk_oid I guess abstract proofs fon't care about oid *).

(* FD + WR *)
equiv kg_eq : XMSS_TW(FakeRO).keygen ~ XMSS_PRF.kg : ={arg} ==> pkrel res{1}.`1 res{2}.`2 /\ skrel res{1}.`2 res{2}.`1.
proof.
proc. inline {1} 2. inline {1} 5. inline {1} 8.
inline {2} 5. inline {2} 10.
swap {2} [5..7] -4; seq 3 3 : (NBytes.val ms{1} = sk_seed0{2} /\ NBytes.val ss{1} = sk_prf0{2} /\ NBytes.val ps{1} = pub_seed0{2}).
+ do 3!(rnd NBytes.val NBytes.insubd); auto => />. admit.
sp 7 14;wp;conseq 
    (: _ ==> (val_bt_trh (list2tree leafl0{1}) ps{1} (set_typeidx (XAddress.val witness) trhtype) h 0 =
              DigestBlock.insubd (BytesToBits (NBytes.val (nth witness stack{2} 0))))).
+ by auto => /> &1 *;smt(NBytes.valK).
while ( true
  (* We can write a function that fully defines the stack based on the leaf index :
    -> The size of the stack is the hamming weight of the index i
    -> Suppose that hamming weight is k.
    -> Then, let b_0 ... b_k denote the positions of the one bits in (
       At position j in the stack we have the node of the hash tree with path ((rev (bits i))[0..h-b_j-1]++[0])). *)
).
admitted.

(* Signature type is abused with two index copies because I need this to simulate
   the actual operation of the implementation *)

op sigrel(asig : sigXMSSTW, sig : sig_t) =
   (* asig.`1 = ??? /\ why is the public seed in the signature ? *)
   asig.`1.`1 = sig.`r /\
   asig.`1.`2 = to_uint sig.`sig_idx /\
   asig.`2.`1 = Index.insubd (to_uint sig.`sig_idx) /\
   asig.`2.`2 = DBLL.insubd 
     (map (fun (b : nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (LenNBytes.val sig.`r_sig.`1)) /\ 
   asig.`2.`3 = DBHL.insubd 
     (map (fun (b : nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (AuthPath.val sig.`r_sig.`2)).

(* FD + WR *)
equiv sig_eq : XMSS_TW(FakeRO).sign ~ XMSS_PRF.sign : skrel sk{1} sk{2} /\ ={m} ==> 
   sigrel res{1}.`1 res{2}.`1 /\  skrel res{1}.`2 res{2}.`2. 
proof.
proc. inline {1} 6. inline {1} 8. inline {1} 14. inline {1} 20. inline {2} 7. inline {2} 16. inline {2} 22.
admitted.

(* PY *)
equiv ver_eq : XMSS_TW(FakeRO).verify ~ XMSS_PRF.verify : pkrel pk{1} pk{2} /\ ={m} /\ sigrel sig{1} s{2} ==> 
   ={res}.
proof.
proc.
inline {1} 4. inline {1} 7. inline {1} 13.
inline {2} 10. 
admitted.
