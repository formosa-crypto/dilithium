require import AllCore SigmaProtocol List.

theory FiatShamirWithAbort.

  (* parameters *)
  op key_len : int.
  op max_kappa : int.

  (* ID scheme response type should be nullable for correctness error *)
  type response_t.
  type response = response_t option.

  (* Take the built-in ID scheme *)
  clone import SigmaProtocol with
    type response <- response.

  module type CommitmentRecoverableScheme = {
    (* same as the built-in ID schemes from the SigmaProtocol module *)
    proc gen() : statement * witness
    proc commit(pk: statement, sk: witness) : message * secret
    proc test(pk: statement, w: message) : challenge
    proc respond(pk_sk: statement * witness, w_st: message * secret, c: challenge) : response
    proc verify(pk: statement, w: message, c: challenge, z: response) : bool

    (* added procedure *)
    proc recover_commitment(pk: statement, c: challenge, z: response) : message
  }.

  section Correctness.
    (**
     * Is this syntax out of date? I see `<:` instead of `:` on newer versions of Easycrypt.
     *
     * Is there a way to multiple-inherit with this syntax?
     * If not, I may have a workaround, but it's not really clean...
     *)
    declare module ID : CommitmentRecoverableScheme.
    (* I've seen `declare axiom` instead of just `axiom`. What's the deal? *)
    axiom recover_correct :
      forall c0 z0 pk0 sk0,
        (**
         * Valid key pair.
         * When I tried `> 0%r` instead, it doesn't parse...
         *)
        !(phoare[ID.gen : true ==> res = (pk0, sk0)] = 0%r) =>
        (* exists unique result from recover_commitment *)
        exists w0, hoare[ID.recover_commitment : pk = pk0 && c = c0 && z = z0 ==> res = w0] &&
        (* recover_commitment output is correct *)
        hoare[ID.verify : pk = pk0 && c = c0 && z = z0 ==> res = true].
  end section Correctness.

  (* Take the built-in public key signature scheme *)
  require PKS.
  clone PKS with
    type pkey <- statement,
    type skey <- statement * witness,
    type signature <- (challenge * response) option
  proof *.

  (* Random oracle with the appropriate input/output types for our Fiat-Shamir *)
  module type RO_Challenge = {
    proc * init() : unit
    proc hash(w : SigmaProtocol.message, m : PKS.message) : challenge
  }.

  (* Taken from [KLS17] *)
  module FiatShamirWithAbort(ID: CommitmentRecoverableScheme, H: RO_Challenge) : PKS.Scheme = {
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
      var z : response;
      var w, st, c;
      var pk_ID, sk_ID;

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
  
end FiatShamirWithAbort.
