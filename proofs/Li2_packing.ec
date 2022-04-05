require import Li2_params.
require import AllCore.
require import BitEncoding.
require import List.

import Li2_PolyReduceZp.
import Li2_Matrix.
import Zp.
import BS2Int.
import Byte.
import BitChunking.

op polyt1_pack (t1 : polyXnD1) : byte list =
  let coeffs = mkseq (fun i => asint t1.[i]) Li2_n in
  let all_bits = flatten (map (int2bs 10) coeffs) in
  map mkword (chunk 8 all_bits).

op polyt1_pack_veck (t1 : vector) : byte list =
  flatten (map polyt1_pack (mkseq (fun i => t1.[i]) Li2_k)).

op polyz_pack (z : polyXnD1) : byte list =
  let coeffs = mkseq (fun i => asint z.[i]) Li2_n in
  let all_bits = flatten (map (int2bs 20) coeffs) in
  map mkword (chunk 8 all_bits).

op polyz_pack_vecl (z : vector) : byte list =
  flatten (map polyz_pack (mkseq (fun i => z.[i]) Li2_l)).

op polyz_unpack(buf : byte list) : polyXnD1 =
  let all_bits = flatten (map ofword buf) in
  let coeffs = map (fun x => inzmod (bs2int x)) (chunk 20 all_bits) in
  pi (BasePoly.polyL coeffs).
