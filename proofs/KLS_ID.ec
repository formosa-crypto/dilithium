(* Identification schemes found in KLS *)

require import AllCore List.
require import SigmaProtocol.
require import DBool.
require import Li2_params.
import Li2_Matrix.
require import SpongeROM.
require import Li2_hashing.

type challenge_t = byte list. (* length = 256? *)
type response_t = (vector * vector) option. (* (z, h) *)

(* Interface incompatible.
   SigmaScheme keygen has to take a seed for RO

clone import SigmaProtocol as Li2_SigmaProtocol with
  type statement = pk_t,
  type witness = sk_t,
  type message = vector, (* w1 *)
  type secret = state_t, (* This seems extraneous *)
  type challenge = challenge_t,
  type response = response_t.
*)

require import Li2_poly.
require import Li2_packing.


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
    var c : R;
    (rho, k, tr, s1, s2, t0) <- sk;
    (* TODO init c *)
    z <- y + (diagc c) *^ s1;
    return
      if true (* TODO *) then
        None
      else
        Some (z, h);
  }
}.

module KLS_ID (H : SpongeRO) (* : SigmaScheme *) = {
  proc gen() : pk_t * sk_t = {
    (* This doesn't work.
       It requires "seed" as parameter for the RO.
       Which isn't a thing in SigmaProtocol.
 *)
    return witness;
  }

  proc commit(pk : pk_t, sk : sk_t) : vector * state_t = {
    (* TODO *)
    return witness;
  }

  (** This makes zero sense.
      Why does this even take any input?
  proc test( (* pk: pk_t, w : vector *) ) : challenge_t = {
    (* TODO *)
    return witness;
  }

  *)
  
  proc respond(sk : sk_t, w1: vector, c : challenge_t, st : state_t) : response_t = {
    (* TODO *)
    return witness;
  }
    
  proc verify(pk : pk_t, w1 : vector, c : challenge_t, z : response_t) : bool = {
    (* TODO *)
    return witness;
  }

  (* new procedure *)
  proc recover_commitment(pk: pk_t, c: byte list, z: response_t) : challenge_t = {
    (* TODO *)
    return witness;
  }
}.

(* Umm...

    axiom recover_correct c0 z0 pk0 sk0 &m :
        (* valid key pair *)
        Pr[ID_inst.gen() @ &m : res = (pk0, sk0)] > 0%r =>
        (* exists unique result from recover_commitment *)
        exists w0, hoare[ID_inst.recover_commitment : pk = pk0 && c = c0 && z = z0 ==> res = w0] /\
        (* recover_commitment output is correct *)
        hoare[ID_inst.verify : pk = pk0 && c = c0 && z = z0 ==> res = true].

  module type NaHvzkSim = {
    proc main(pk : pk_t) : commit_t * challenge_t * unveil_t
  }.
*)
