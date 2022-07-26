require import AllCore List.
require import Li2_params Li2_rounding.

import Li2_Matrix.
import Li2_PolyReduceZp.
import Li2_Matrix.Vector.

import Zp.

op poly_power2round (p : R) (d : int) : R * R =
  let coeffs = mkseq (fun deg => Zp.asint p.[deg]) Li2_n in
  let results = map (fun r => power2round r d) coeffs in
  ((pinject \o BasePoly.polyL) (map (fun (r : int * int) => inzmod r.`1) results),
   (pinject \o BasePoly.polyL) (map (fun (r : int * int) => inzmod r.`2) results)).

op polyveck_power2round (v : vector) (d : int) : vector * vector =
  (offunv (fun i => (poly_power2round v.[i] d).`1),
   offunv (fun i => (poly_power2round v.[i] d).`2)).

op poly_highbits (p : R) (alpha : int) : R =
  let coeffs = mkseq (fun deg => Zp.asint p.[deg]) Li2_n in
  let results = map (fun r => inzmod (highbits r alpha)) coeffs in
  (pinject \o BasePoly.polyL) results.

op polyveck_highbits (v : vector) alpha : vector =
  offunv (fun i => poly_highbits v.[i] alpha).

op poly_lowbits (p : R) (alpha : int) : R =
  let coeffs = mkseq (fun deg => Zp.asint p.[deg]) Li2_n in
  let results = map (fun r => inzmod (lowbits r alpha)) coeffs in
  (pinject \o BasePoly.polyL) results.

op polyveck_lowbits (v : vector) alpha : vector =
  offunv (fun i => poly_lowbits v.[i] alpha).

op poly_makeHint (z : R) (r : R) (alpha : int) : R =
  let zcoeffs = mkseq (fun deg => Zp.asint z.[deg]) Li2_n in
  let rcoeffs = mkseq (fun deg => Zp.asint r.[deg]) Li2_n in
  (* TODO clean-up. This doesn't seem reasonable. *)
  let coeffs = zip zcoeffs rcoeffs in
  polyLX (map (fun (zr : int * int) => inzmod (makeHint zr.`1 zr.`2 alpha))
      coeffs).

op polyveck_makeHint (z : vector) (r : vector) (alpha : int) : vector =
  offunv (fun i => poly_makeHint z.[i] r.[i] alpha).

op poly_useHint (hs rs : R) (alpha : int) =
  polyLX (mkseq (fun i => inzmod (useHint (asint hs.[i]) (asint rs.[i]) alpha)) Li2_n).

op polyveck_useHint (hv rv :vector) alpha =
  offunv (fun i => poly_useHint hv.[i] rv.[i] alpha).

op poly_max (p : R) : int =
  let coeffs = mkseq (fun deg => Zp.asint p.[deg]) Li2_n in
  let coeffs' = map (fun x => if Li2_q < 2 * x then x - Li2_q else x) coeffs in
  foldr max 0 coeffs'.

op polyvec_max (vlen : int) (v : vector) =
  let polys = mkseq (fun i => v.[i]) vlen in
  let p_maxs = map poly_max polys in
  foldr max 0 p_maxs.

op poly_weight (p : polyXnD1) =
  let coeffs = mkseq (fun deg => Zp.asint p.[deg]) Li2_n in
  foldr (+)%Int 0 coeffs.

op polyveck_weight (v : vector) =
  let polys = mkseq (fun i => v.[i]) Li2_k in
  let weights = map poly_weight polys in
  foldr (+)%Int 0 weights.
