(* Identification schemes found in KLS *)

require import AllCore.
require import SigmaProtocol.
require import DBool.

theory KLS_ID.

  type pk_t.
  type sk_t.
  type commit_t.
  type state_t.
  type challenge_t.
  type unveil_content_t.
  type unveil_t = unveil_content_t option.

  clone import SigmaProtocol with
    type statement = pk_t,
    type witness = sk_t,
    type message = commit_t,
    type secret = state_t,
    type challenge = challenge_t,
    type response = unveil_t.

  module type KLS_ID = {
    (* same as SigmaScheme *)
    proc gen(): pk_t * sk_t
    proc commit(pk: pk_t, sk: sk_t) : commit_t * state_t
    proc test(pk: pk_t, w: commit_t) : challenge_t
    proc respond(keys: pk_t * sk_t, states: commit_t * state_t, c: challenge_t) : unveil_t
    proc verify(pk: pk_t, w: commit_t, c: challenge_t, z: unveil_t) : bool

    (* new procedure *)
    proc lossyGen() : pk_t
    proc recover_commitment(pk: pk_t, c: challenge_t, z: unveil_t) : commit_t
  }.

  section Correctness.
    (**
     * Is this syntax out of date? I see `<:` instead of `:` on newer versions of Easycrypt.
     *)
    declare module ID_inst : KLS_ID.
    (* I've seen `declare axiom` instead of just `axiom`. What's the deal? *)
    axiom recover_correct c0 z0 pk0 sk0 &m :
        (* valid key pair *)
        Pr[ID_inst.gen() @ &m : res = (pk0, sk0)] > 0%r =>
        (* exists unique result from recover_commitment *)
        exists w0, hoare[ID_inst.recover_commitment : pk = pk0 && c = c0 && z = z0 ==> res = w0] /\
        (* recover_commitment output is correct *)
        hoare[ID_inst.verify : pk = pk0 && c = c0 && z = z0 ==> res = true].
  end section Correctness.

  module type LossyAdv = {
    proc main(pk : pk_t) : bool
  }.

  module LossyGame(ID_inst: KLS_ID, Adv: LossyAdv) = {
    proc main() : bool = {
      var b, b' : bool;
      var pk : pk_t;
      var sk : sk_t;

      b <$ dbool;
      if(b) {
        (pk, sk) <- ID_inst.gen();
      } else {
        pk <- ID_inst.lossyGen();
      }
      b' <- Adv.main(pk);
      return (b = b');
    }
  }.

  module type NaHvzkSim = {
    proc main(pk : pk_t) : commit_t * challenge_t * unveil_t
  }.

  (* stat. distance stuff? *)

  (* TODO other games... *)
end KLS_ID.
