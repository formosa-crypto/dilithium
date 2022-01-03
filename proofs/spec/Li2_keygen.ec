require import AllCore.
require import List.
require import Li2_params Li2_hashing Li2_rounding.

import Li2_Matrix.
import Li2_Matrix.Matrix.

type pk_t = int list * vector.
type sk_t = int list * int list * int list * vector * vector * vector.

module Keygen(H : RO) = {
  proc keygen(seed : int list) : pk_t * sk_t = {
    var rho, rho', k, tr, s1, s2, t, t1, t0;
    var a;
    H.init(SHAKE256);
    H.absorb(seed);
    rho <@ H.squeeze(32);
    rho' <@ H.squeeze(64);
    k <@ H.squeeze(32);
    a <@ Expand_impl(H).expandA(rho);
    (s1, s2) <@ Expand_impl(H).expandS(rho');
    t <- a *^ s1 + s2;
    (* (t1, t0) <@ Li2_Rounding_impl.power2round(t, Li2_d); *)
    H.init(SHAKE256);
    H.absorb(rho);
    (* pack t1 so it can be absorbed by H? *)
    tr <@ H.squeeze(32);
    return ((rho, t1), (rho, k, tr, s1, s2, t0));
  }
}.
