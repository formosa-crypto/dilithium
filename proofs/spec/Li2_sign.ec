require import AllCore List.
require import Li2_params Li2_hashing Li2_poly Li2_packing SpongeROM.

import Li2_Matrix Li2_Matrix.Vector.

module Sign(H: SpongeRO) = {
  proc sign(sk_packed: byte list, m: byte list) = {
    var sk, seed, k, tr, s1, s2, t0;
    var mu : byte list;
    var kappa : int;
    var z : vector;
    sk <- unpack_sk sk_packed;
    (seed, k, tr, s1, s2, t0) <- sk;
    H.reset(SHAKE256);
    H.absorb(tr);
    H.absorb(m);
    mu <@ H.squeeze(512);
    kappa <- 0;
  }
}.
