require import AllCore.
require import List.
require import Li2_params Li2_hashing Li2_rounding Li2_poly.
require import Li2_packing.
require import SpongeROM.

import Li2_Matrix Li2_Matrix.Matrix.

module Keygen(H : SpongeRO) = {
  proc keygen(seed : byte list) : byte list * byte list = {
    var rho, rho', k, tr, s1, s2, t, t1, t0, t1_packed;
    var sk, pk;
    var a;
    H.reset(SHAKE256);
    H.absorb(seed);
    rho <@ H.squeeze(32);
    rho' <@ H.squeeze(64);
    k <@ H.squeeze(32);
    a <@ Expand_impl(H).expandA(rho);
    (s1, s2) <@ Expand_impl(H).expandS(rho');
    t <- a *^ s1 + s2;
    (t1, t0) <- polyveck_power2round t Li2_d;
    t1_packed <- pack_t1 t1;
    H.reset(SHAKE256);
    H.absorb(rho);
    H.absorb(t1_packed);
    tr <@ H.squeeze(32);
    pk <- (rho, t1);
    sk <- (rho, k, tr, s1, s2, t0);
    return (pack_pk pk, pack_sk sk);
  }
}.
