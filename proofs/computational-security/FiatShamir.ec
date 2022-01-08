require import AllCore SigmaProtocol.

theory FiatShamirWithAbort.

  clone import SigmaProtocol.

  module type CommitmentRecoverableScheme = {
    (* same as other sigma protocols *)
    proc gen() : statement * witness
    proc commit(pk: statement, sk: witness) : message * secret
    proc test(pk: statement, w: message) : challenge
    proc respond(pk_sk: statement * witness, w_st: message * secret, c: challenge) : response
    proc verify(pk: statement, w: message, c: challenge, z: response) : bool

    (* added procedure *)
    proc recover_commitment(pk: statement, c: challenge, z: response) : message
  }.

  section Correctness.
    declare module ID : CommitmentRecoverableScheme.
    axiom recover_correct :
      forall c0 z0 pk0 sk0,
        !(phoare[ID.gen : true ==> res = (pk0, sk0)] = 0%r) =>
        exists w0, hoare[ID.recover_commitment : pk = pk0 && c = c0 && z = z0 ==> res = w0] =>
        hoare[ID.verify : pk = pk0 && c = c0 && z = z0 ==> res = true].
  end section Correctness.

  require PKS.
  clone PKS with
    type pkey <- statement,
    type skey <- witness
  proof *.

  (*
  module FiatShamirWithAbort(ID : CommitmentRecoverableScheme) : PKS.Scheme = {
    proc init() = {}
    proc keygen = ID.gen
    proc sign(sk, m) = {
      
    }
    proc verify
  }.*)
  
  
end FiatShamirWithAbort.


