require import AllCore List.
require import Li2_params Li2_hashing Li2_poly Li2_packing SpongeROM.

import Li2_Matrix Li2_Matrix.Vector.
import Li2_PolyReduceZp.
import Li2_Matrix.Vector.ZModule.

module Sign(H: SpongeRO) = {
  proc sign(sk_packed: byte list, m: byte list) = {
    var sk, rho, k, tr, s1, s2, t0;
    var mu : byte list;
    var a : matrix;
    var kappa : int;
    var z, h : vector;
    var good;
    var c' : byte list;
    var c : polyXnD1;
    var y, w, w1 : vector;
    var r0;

    (* Suppresses unused variables warning *)
    z <- witness;
    h <- witness;
    c <- witness;

    sk <- unpack_sk sk_packed;
    (rho, k, tr, s1, s2, t0) <- sk;
    a <@ Expand_impl(H).expandA(rho);
    H.reset(SHAKE256);
    H.absorb(tr);
    H.absorb(m);
    mu <@ H.squeeze(512);
    kappa <- 0;
    good <- false;
    while(!good) {
      y <@ Expand_impl(H).expandMask(k, kappa);
      w <- a *^ y;
      w1 <- polyveck_highbits w (2 * Li2_gamma2);
      H.reset(SHAKE256);
      H.absorb(mu);
      H.absorb(pack_w1 w1);
      c' <@ H.squeeze(256);
      c <@ Expand_impl(H).sampleInBall(c');

      (* TODO Implement this diagc thing in the standard library already *)
      z <- y + (diagc c) *^ s1;
      r0 <- polyveck_lowbits (w - (diagc c) *^ s2) (2 * Li2_gamma2);

      good <- polyvec_max Li2_l z < Li2_gamma1 - Li2_beta;
      good <- good || polyvec_max Li2_k r0 < Li2_gamma2 - Li2_beta;

      if (good) {
        h <- polyveck_makeHint
             (- (diagc c) *^ t0)
             (w - (diagc c) *^ s2 + (diagc c) *^ t0)
             (2 * Li2_gamma2);
        good <- good || polyveck_weight h <= Li2_omega;
      }
    }
    return (z, c, h);
  }
}.
