require import AllCore List.
require import Li2_params Li2_hashing Li2_poly Li2_packing SpongeROM.

module Sign(H: RO) = {
  proc sign(sk: sk_t, m: int list) = {
    var seed, k, tr, s1, s2, t0;
    var mu : int list;
    var kappa : int;
    (seed, k, tr, s1, s2, t0) <- sk;
    H.init(SHAKE256);
    H.absorb(tr);
    H.absorb(m);
    mu <- H.squeeze(512);
    
  }
}.
