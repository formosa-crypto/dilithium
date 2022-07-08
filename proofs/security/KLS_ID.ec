(* Identification schemes found in KLS *)

require import AllCore List.
require import DBool.
require import Li2_params.
import Li2_Matrix.
require import SpongeROM.
require import Li2_hashing.

type challenge_t = byte list. (* length = 256? *)
type response_t = (vector * vector) option. (* (z, h) *)

require import Li2_poly.
require import Li2_packing.

import Li2_PolyReduceZp.

import Vector.ZModule.

module KLS_ID_P (H : SpongeRO) = {
  var w : vector
  var y : vector

  proc keygen(seed : byte list) : pk_t * sk_t = {
    var rho, rho', k, tr, s1, s2, t, t1, t0, t1_packed;
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
    t1_packed <- polyt1_pack_veck t1;
    H.reset(SHAKE256);
    H.absorb(rho);
    H.absorb(t1_packed);
    tr <@ H.squeeze(32);
    return ((rho, t1), (rho, k, tr, s1, s2, t0));
  }

  (* Nonce isn't compatible with standard library sigma protocols too? *)
  proc commit(sk: sk_t, nonce : int) : vector = {
    var rho, k, tr, s1, s2, t0;
    var a;
    (rho, k, tr, s1, s2, t0) <- sk;
    a <@ Expand_impl(H).expandA(rho);
    y <@ Expand_impl(H).expandMask(k, nonce);
    w <- a *^ y;
    return polyveck_highbits w (2 * Li2_gamma2);
  }

  proc respond(sk: sk_t, c_tilde: challenge_t) : response_t = {
    var rho, k, tr, s1, s2, t0;
    var z, h;
    var c : polyXnD1;
    var good : bool;
    var r0;

    (* Suppresses "unused variable" warning *)
    h <- zerov;

    (rho, k, tr, s1, s2, t0) <- sk;
    c <@ Expand_impl(H).sampleInBall(c_tilde);
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

    return
      if good then
        Some (z, h)
      else
        None;
  }

  (* TODO recover commitment... *)
}.

(* Umm...

    axiom recover_correct c0 z0 pk0 sk0 &m :
        (* valid key pair *)
        Pr[ID_inst.gen() @ &m : res = (pk0, sk0)] > 0%r =>
        (* exists unique result from recover_commitment *)
        exists w0, hoare[ID_inst.recover_commitment : pk = pk0 && c = c0 && z = z0 ==> res = w0] /\
        (* recover_commitment output is correct *)
        hoare[ID_inst.verify : pk = pk0 && c = c0 && z = z0 ==> res = true].
*)
