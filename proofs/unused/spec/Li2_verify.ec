require import AllCore List.
require import Li2_params Li2_hashing Li2_poly Li2_packing SpongeROM Li2_rounding.

import Li2_Matrix Li2_Matrix.Vector.
import Li2_PolyReduceZp.
import Li2_Matrix.Vector.ZModule.

print ( * ).

print Poly.

print BasePoly.polyC.

import Zp.

module Verify(H: SpongeRO) = {
  proc main(pk: byte list, m: byte list, sig_packed: byte list) : bool = {
    var osig;
    var good;
    var tr : byte list;
    var c', c, z, h;
    var w1;
    var c'' : byte list;
    var mu : byte list;
    var t1, rho;
    var a;

    good <- true;
    (rho, t1) <- unpack_pk pk;
    a <@ Expand_impl(H).expandA(rho);

    H.reset(SHAKE256);
    H.absorb(rho);
    H.absorb(pack_t1 t1);
    tr <@ H.squeeze(32);

    H.reset(SHAKE256);
    H.absorb(tr);
    H.absorb(m);
    mu <@ H.squeeze(512);

    osig <- unpack_sig sig_packed;
    if(osig = None) {
      good <- false;
    }
    (c', z, h) <- oget osig;
    c <@ Expand_impl(H).sampleInBall(c');
    (* TODO FIXME this is ugly *)
    w1 <- polyveck_useHint h (a *^ z - (diagc (pi (BasePoly.polyC (inzmod (2 ^ Li2_d))))) *^ ((diagc c) *^ t1)) (2 * Li2_gamma2);
    good <- good || polyvec_max Li2_l z < Li2_gamma1 - Li2_beta;

    H.reset(SHAKE256);
    H.absorb(mu);
    H.absorb(pack_w1 w1);
    c'' <@ H.squeeze(256);
    good <- good || c' = c'';

    return good;
  }
}.
