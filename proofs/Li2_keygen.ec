require import AllCore.
require import List.
require import Li2_params Li2_hashing Li2_rounding Li2_poly.
require import Li2_packing.
require import SpongeROM.

import Li2_Matrix.
import Li2_Matrix.Matrix.

module Keygen(H : RO) = {
  proc keygen(seed : int list) : pk_t * sk_t = {
    var rho, rho', k, tr, s1, s2, t, t1, t0, t1_packed;
    var a;
    H.init(SHAKE256);
    H.absorb(seed);
    rho <@ H.squeeze(32);
    rho' <@ H.squeeze(64);
    k <@ H.squeeze(32);
    a <@ Expand_impl(H).expandA(rho);
    (s1, s2) <@ Expand_impl(H).expandS(rho');
    t <- a *^ s1 + s2;
    (t1, t0) <@ Polyvec_impl.power2round_veck(t, Li2_d);
    t1_packed <@ Packing_impl.polyt1_pack_veck(t1);
    H.init(SHAKE256);
    H.absorb(rho);
    H.absorb(t1_packed);
    tr <@ H.squeeze(32);
    return ((rho, t1), (rho, k, tr, s1, s2, t0));
  }
}.
