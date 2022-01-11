require import Li2_params.
require import AllCore.

require import BitEncoding.
require import List.

type entry_t = Li2_ring.qT.

import PolyModQ.
import Li2_field.
import Li2_Matrix.
import Li2_Matrix.Matrix.

module Packing_impl = {
  proc polyt1_pack(t1 : entry_t) : int list = {
    var coeffs, all_bits;
    coeffs <- mkseq (fun (i : int) => asint (Li2_ring.repr t1).[i]) Li2_n;
    all_bits <- flatten (map (BS2Int.int2bs 10) coeffs);
    return map BS2Int.bs2int (BitChunking.chunk 8 all_bits);
  }

  proc polyt1_pack_veck (t1 : vector) : int list = {
    var i;
    var packed_comps, packed_comp;
    packed_comps <- [];
    i <- 0;
    while(i < Li2_k) {
      packed_comp <@ polyt1_pack(t1.[i]);
      packed_comps <- packed_comps ++ [packed_comp];
      i <- i + 1;
    }
    return flatten packed_comps;
  }

  proc polyz_pack(z : entry_t) : int list = {
    var coeffs, all_bits;
    coeffs <- mkseq (fun i => asint (Li2_ring.repr z).[i]) Li2_n;
    all_bits <- flatten (map (BS2Int.int2bs 20) coeffs);
    return map BS2Int.bs2int (BitChunking.chunk 8 all_bits);
  }

  proc polyz_pack_vecl (zs : vector) : int list = {
    var i;
    var packed_comps, packed_comp;
    packed_comps <- [];
    i <- 0;
    while(i < Li2_l) {
      packed_comp <@ polyz_pack(zs.[i]);
      packed_comps <- packed_comps ++ [packed_comp];
      i <- i + 1;
    }
    return flatten packed_comps;
  }

  proc polyz_unpack(buf : int list) : entry_t = {
    var all_bits, coeffs, p;
    all_bits <- flatten (map (BS2Int.int2bs 8) buf);
    coeffs <- map (fun x => inzmod (BS2Int.bs2int x)) (BitChunking.chunk 20 all_bits);
    p <- polyL coeffs;
    return Li2_ring.pi p;
  }
}.
