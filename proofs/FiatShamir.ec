require import AllCore SigmaProtocol List.

require import KLS_ID.
clone import KLS_ID.
clone import KLS_ID.SigmaProtocol.

(* parameters *)
op max_kappa : int.
axiom max_kappa_positive : 0 < max_kappa.

(* Take the built-in public key signature scheme *)
require PKS.
clone PKS with
  type pkey <- pk_t,
  type skey <- pk_t * sk_t,
  type signature <- (challenge_t * unveil_t) option
proof *.

(* Random oracle with the appropriate input/output types for our Fiat-Shamir *)
module type RO_Challenge = {
  proc * init() : unit
  proc hash(w : commit_t, m : PKS.message) : challenge
}.

(* Taken from [KLS17] *)
module FiatShamirWithAbort(ID: KLS_ID, H: RO_Challenge) : PKS.Scheme = {
  proc init() = {
  H.init();
  }
  proc keygen() = {
      var pk_ID, sk_ID;
    (pk_ID, sk_ID) <- ID.gen();
      return (pk_ID, (pk_ID, sk_ID));
  }

  proc sign(pksk_ID, m) = {
      var kappa : int;
      var z : unveil_t;
      var w, st, c;
      var pk_ID, sk_ID;

      c <- witness; (* suppresses unused warning *)

    (pk_ID, sk_ID) <- pksk_ID;
      z <- None;
      kappa <- 0;
    while(z = None && kappa <= max_kappa) {
      kappa <- kappa + 1;
      (w, st) <- ID.commit(pk_ID, sk_ID);
	c <- H.hash(w, m);
	z <- ID.respond((pk_ID, sk_ID), (w, st), c);
    }
    return (if z = None then None else Some (c, z));
  }

  proc verify(pk, m, signature) = {
      var result;
      var w, z, c, c';
    if(signature = None) {
      result <- false;
    } else {
      (c, z) <- oget signature;
	w <@ ID.recover_commitment(pk, c, z);
	c' <- H.hash(w, m);
	result <- (c = c');
    }
        return result;
  }
}.
