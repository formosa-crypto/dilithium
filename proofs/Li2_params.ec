require import AllCore IntDiv.

op Li2_q : int = 8380417.
op Li2_d : int = 13.
op Li2_tau : int.
op Li2_gamma1 : int.
op Li2_gamma2 : int.
op Li2_k : int.
op Li2_l : int.
op Li2_eta : int.
op Li2_beta : int = Li2_tau * Li2_eta.
op Li2_omega : int.

axiom Li2_matrix_size : 4 <= Li2_l <= Li2_k.

require ZModP.

clone ZModP.ZModField as Li2_field with op p = Li2_q.
require Poly.

clone import Poly.Poly as PolyModQ with type coeff = Li2_field.zmod.
(* -- TODO proof *. -- *)

require Ideal.

clone Ideal.IdealComRing as Li2_polyIdeals with type t = PolyModQ.poly.
(* -- TODO proof *. -- *)

require import List.

op Li2_n = 256.

op ideal = Li2_polyIdeals.idgen [(polyXn Li2_n) + (polyXn 0)].

clone Li2_polyIdeals.RingQuotient as Li2_ring with op p = ideal.

require Matrix.

clone Matrix as Li2_Matrix with type ZR.t = Li2_ring.qT.
(* -- TODO proof *. -- *)

