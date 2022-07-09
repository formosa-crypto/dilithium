require import AllCore Li2_params BitEncoding List ZModP.

import Li2_PolyReduceZp.
import Li2_Matrix.
import Zp.
import BS2Int.
import Byte.
import BitChunking.
import Li2_PolyReduceZp.ComRing.

op poly_pack (bits_per_coeff : int) (p : polyXnD1) : byte list =
  let coeffs = mkseq (fun i => asint p.[i]) Li2_n in
  let all_bits = flatten (map (int2bs bits_per_coeff) coeffs) in
  map mkword (chunk 8 all_bits).

op poly_unpack (bits_per_coeff : int) (buf : byte list) : polyXnD1 =
  let all_bits = flatten (map ofword buf) in
  let coeffs = map (fun x => inzmod (bs2int x)) (chunk bits_per_coeff all_bits) in
  pi (BasePoly.polyL coeffs).

op polyvec_pack p_pack (vsize : int) (v : vector) : byte list =
  flatten (map p_pack (mkseq (fun i => v.[i]) vsize)).

op polyvec_unpack p_unpack (bits_per_coeff : int) (buf : byte list) : vector =
  let all_bits = flatten (map ofword buf) in
  let p_len = Li2_n * bits_per_coeff in
  let v = map p_unpack (chunk p_len buf) in
  offunv (nth zeroXnD1 v).

op pack_t1_entry = poly_pack 10.
op pack_t1 = polyvec_pack pack_t1_entry Li2_k.
op unpack_t1_entry = poly_unpack 10.
op unpack_t1 = polyvec_unpack unpack_t1_entry.

op pack_z_entry = poly_pack 20.
op pack_z = polyvec_pack pack_z_entry Li2_l.
op unpack_z_entry = poly_unpack 20.
op unpack_z = polyvec_unpack unpack_z_entry.

op pack_w1_entry = poly_pack 4.
op pack_w1 = polyvec_pack pack_w1_entry Li2_k.
op unpack_w1_entry = poly_unpack 4.
op unpack_w1 = polyvec_unpack unpack_w1_entry.

op poly_pack_neg (bits_per_coeff : int) (max_val : int) (p : polyXnD1) : byte list =
  let allM_poly = pi (BasePoly.polyL (nseq Li2_n (inzmod max_val))) in
  poly_pack bits_per_coeff (allM_poly - p).

op poly_unpack_neg (bits_per_coeff : int) (max_val : int) (buf : byte list) : polyXnD1 =
  let allM_poly = pi (BasePoly.polyL (nseq Li2_n (inzmod max_val))) in
  allM_poly - (poly_unpack bits_per_coeff buf).

op pack_s1_entry = poly_pack_neg 4 Li2_eta.
op pack_s1 = polyvec_pack pack_s1_entry Li2_l.
op unpack_s1_entry = poly_unpack_neg 4 Li2_eta.
op unpack_s1 = polyvec_unpack unpack_s1_entry.

op pack_s2_entry = poly_pack_neg 4 Li2_eta.
op pack_s2 = polyvec_pack pack_s2_entry Li2_k.
op unpack_s2_entry = poly_unpack_neg 4 Li2_eta.
op unpack_s2 = polyvec_unpack unpack_s2_entry.

op pack_t0_entry = poly_pack_neg 13 (2 ^ 12).
op pack_t0 = polyvec_pack pack_t0_entry Li2_k.
op unpack_t0_entry = poly_unpack_neg 13 (2 ^ 12).
op unpack_t0 = polyvec_unpack unpack_t0_entry.
