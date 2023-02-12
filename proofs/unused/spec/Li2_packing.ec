require import AllCore Li2_params BitEncoding List ZModP.

import Li2_PolyReduceZp.
import Li2_Matrix.
import Zp.
import BS2Int.
import Byte.
import BitChunking.
import Li2_PolyReduceZp.ComRing.
require import IntDiv.

(* TODO Ensure all_bits is multiple of 8.
 * Otherwise `chunk` drops fractional words. *)
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
op unpack_t1 = polyvec_unpack unpack_t1_entry 10.

op pack_z_entry = poly_pack 20.
op pack_z = polyvec_pack pack_z_entry Li2_l.
op unpack_z_entry = poly_unpack 20.
op unpack_z = polyvec_unpack unpack_z_entry 20.

op pack_w1_entry = poly_pack 4.
op pack_w1 = polyvec_pack pack_w1_entry Li2_k.
op unpack_w1_entry = poly_unpack 4.
op unpack_w1 = polyvec_unpack unpack_w1_entry 4.

op poly_pack_neg (bits_per_coeff : int) (max_val : int) (p : polyXnD1) : byte list =
  let allM_poly = pi (BasePoly.polyL (nseq Li2_n (inzmod max_val))) in
  poly_pack bits_per_coeff (allM_poly - p).

op poly_unpack_neg (bits_per_coeff : int) (max_val : int) (buf : byte list) : polyXnD1 =
  let allM_poly = pi (BasePoly.polyL (nseq Li2_n (inzmod max_val))) in
  allM_poly - (poly_unpack bits_per_coeff buf).

op pack_s1_entry = poly_pack_neg 4 Li2_eta.
op pack_s1 = polyvec_pack pack_s1_entry Li2_l.
op unpack_s1_entry = poly_unpack_neg 4 Li2_eta.
op unpack_s1 = polyvec_unpack unpack_s1_entry 4.

op pack_s2_entry = poly_pack_neg 4 Li2_eta.
op pack_s2 = polyvec_pack pack_s2_entry Li2_k.
op unpack_s2_entry = poly_unpack_neg 4 Li2_eta.
op unpack_s2 = polyvec_unpack unpack_s2_entry 4.

op pack_t0_entry = poly_pack_neg 13 (2 ^ 12).
op pack_t0 = polyvec_pack pack_t0_entry Li2_k.
op unpack_t0_entry = poly_unpack_neg 13 (2 ^ 12).
op unpack_t0 = polyvec_unpack unpack_t0_entry 13.

(* packing offsets *)
op Li2_pack_eta_len = Li2_n %/ 2.
op Li2_pack_s1_len = Li2_l * Li2_n %/ 2.
op Li2_pack_s2_len = Li2_k * Li2_n %/ 2.
op Li2_pack_s2_loc = 96 + Li2_pack_s1_len.
op Li2_pack_t1_len = 10 * Li2_n %/ 8.
op Li2_pack_t0_len = 416.
op Li2_pack_sk_len = 4000.
op Li2_pack_t0_loc = Li2_pack_sk_len - Li2_k * Li2_pack_t0_len.

op pack_pk (pk: pk_t) : byte list =
  let (rho, t1) = pk in
  rho ++ pack_t1 t1.

op unpack_pk (buf: byte list) : pk_t =
  let rho = take 32 buf in
  let t1 = unpack_t1 (drop 32 buf) in
  (rho, t1).

op pack_sk (sk: sk_t) : byte list =
  let (rho, k, tr, s1, s2, t0) = sk in
  rho ++ k ++ tr ++ pack_s1 s1 ++ pack_s2 s2 ++ pack_t0 t0.

op unpack_sk (buf: byte list) : sk_t =
  let rho = take 32 buf in
  let k = take 32 (drop 32 buf) in
  let tr = take 32 (drop 64 buf) in
  let s1 = unpack_s1 (take Li2_pack_s1_len (drop 96 buf)) in
  let s2 = unpack_s2 (take Li2_pack_s2_len (drop Li2_pack_s2_loc buf)) in
  let t0 = unpack_t0 (take Li2_pack_t0_len (drop Li2_pack_t0_loc buf)) in
  (rho, k, tr, s1, s2, t0).

op pack_hint_entry(h: polyXnD1) : byte list =
  let locs = mkseq (fun i => mkword (int2bs 8 (i * asint h.[i]))) Li2_n in
  filter (pred1 (mkword wordw)) locs.

op max_hint_weight : int.

(* Pack hint, assuming its weight is low enough.
 * Returns garbage on invalid hints without checking.
 *)
op pack_hint(h: vector) : byte list =
  let entries = mkseq (fun i => pack_hint_entry h.[i]) Li2_k in
  let cumulative_weights = (fun j => sumz (map List.size (take j entries))) in
  let num_zeroes = max_hint_weight - cumulative_weights Li2_k in
  flatten entries ++ nseq num_zeroes (mkword wordw) ++ mkseq (fun i => mkword (int2bs 8 (cumulative_weights i))) Li2_k.

op pack_sig(s: sig_t) : byte list =
  let (c, z, h) = s in
  c ++ pack_z z ++ pack_hint h.

op is_ordered_aux (x0 : int) (lst : int list) : bool =
  with lst = [] => true
  with lst = x1 :: lst' =>
    x0 < x1 && is_ordered_aux x1 lst'.

op is_ordered = is_ordered_aux (-1).

op unpack_hint_entry(buf : byte list) : polyXnD1 option =
  let locs = mkseq (fun i => b2i (mkword (int2bs 8 i) \in buf)) Li2_n in
  if !(is_ordered locs) then None else
  Some (polyLX (map inzmod locs)).

op slice ['a] (a b : int) (lst : 'a list) = drop a (take b lst).

op unpack_hint(buf: byte list) : vector option =
  let cutoffs = 0 :: map (bs2int \o ofword) (drop max_hint_weight buf) in
  if !(is_ordered cutoffs) then None else
  if Li2_omega < last 0 cutoffs then None else
  let packed_entries = mkseq (fun i => slice (nth 0 cutoffs i) (nth 0 cutoffs (i + 1)) buf) Li2_k in
  let unpacked_entries = map unpack_hint_entry packed_entries in
  if None \in unpacked_entries then None else
  Some (offunv (fun i => oget (nth witness unpacked_entries i))).

op Li2_pack_z_len = Li2_n * 20 %/ 8.
op Li2_pack_hstart = 32 + Li2_l * Li2_pack_z_len.

op unpack_sig(buf: byte list) : sig_t option =
  let c = take 32 buf in
  let z = unpack_z (slice 32 Li2_pack_hstart buf) in
  let h = unpack_hint (drop Li2_pack_hstart buf) in
  if h = None then None else
  Some (c, z, oget h).
