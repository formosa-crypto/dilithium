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

op poly_makeHint (z : R) (r : R) (alpha : int) : R =
  let zcoeffs = mkseq (fun deg => Zp.asint z.[deg]) Li2_n in
  let rcoeffs = mkseq (fun deg => Zp.asint r.[deg]) Li2_n in
  let coeffs = zip zcoeffs rcoeffs in
  (pinject \o BasePoly.polyL)
    (map (fun (zr : int * int) => inzmod (makeHint zr.`1 zr.`2 alpha))
      coeffs).

op polyveck_makeHint (z : vector) (r : vector) (alpha : int) : vector =
  offunv (fun i => poly_makeHint z.[i] r.[i] alpha).
