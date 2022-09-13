require import AllCore Int Real List FinType DBool.

abstract theory IDS.
(* Generic types for 
   public and secret key, 
   commitment W, challenge C, response Z, 
   and internal state of the prover
*)
type PK, SK, W, C, Z, Pstate.

type transcript = W*C*Z.

(* ---------------------------------------------------------------------------*)
(*   Identification scheme (protocol between prover and verifier)             *)
(* ---------------------------------------------------------------------------*)   

(* Generic prover *)
module type Prover = { 
  proc keygen(): PK*SK
  proc commit(sk:SK): W
  proc response(sk:SK, c:C): Z option
}. 

(* Generic verifier *)
module type Verifier ={
  proc challenge(w:W, pk:PK): C
  proc verify(pk:PK, w:W, c:C, z:Z): bool
}.


(* ----------------------------------
    Security for IDS 1: Impersonation  
   ----------------------------------*)

(* Impersonator *)
module type Adv_Imp = {
  proc commit(pk:PK): W
  proc response(pk:PK, c:C): Z (* option or not *)
}.

(* Impersonation Game *)
module Imp_Game (P: Prover, V: Verifier, A: Adv_Imp) = {

  proc main() = {
    var sk, pk,w,c,z,result;
   
    (pk,sk) <@ P.keygen();
    w <@ A.commit(pk);
    c <@ V.challenge(w,pk);
    z <@ A.response(pk, c);
    result <@ V.verify(pk,w,c,z);
    return result;
  }
}.


(* -----------------------------------------------------
    Security for IDS 2: HonestVerifierZeroKnowledge  
   ----------------------------------------------------- *)


(***********************************************************)
(*     HVZK: There exists an HVZK_Sim such that            *)
(*     HVZK_Sim.getTrace(pk)                               *) 
(*             ~ Honest_Execution.get_trace()              *)
(***********************************************************)

(* Simulator for HVZK that generates valid transcripts given a public key *)
module type HVZK_Sim = {
  proc get_trans(pk:PK) : transcript option
}.


(* Module that generates transcripts of honest executions as reference *) 
module Honest_Execution (P: Prover, V: Verifier) = {

  proc get_trans(pk:PK, sk:SK) = {
    var w,c,z,r;

    w <@ P.commit(sk);
    c <@ V.challenge(w,pk);
    z <@ P.response(sk, c);
    r <- if z = None then None else Some (w,c,oget z);
    return r;
  }
}.

(* Abstract oracle used in the game to give the distinguisher adaptive 
   access to multiple transcripts *) 
module type HVZK_Oracle = {
  proc get_trans() : transcript option
}.

 (* Instantiation of the oracle using a Simultor. Note that init 
    only takes a public key *)
module HVZK_Sim_Oracle (Sim :HVZK_Sim) : HVZK_Oracle = {
  var pk : PK
  proc init (pki : PK) : unit = {
    pk <- pki;
  }
  
  proc get_trans() = {
    var trans;
    trans <@ Sim.get_trans(pk);
    return trans;
  }
}.

 (* Instantiation of the oracle using honest execution. Note that 
    init in this case also needs the secret key *)
module HVZK_HE_Oracle (P : Prover, V: Verifier ) : HVZK_Oracle = {
  var pk : PK
  var sk : SK
  proc init (pki : PK, ski : SK) : unit = {
    pk <- pki;
    sk <- ski;
  }
  
  proc get_trans() = {
    var trans;
    trans <@ Honest_Execution(P,V).get_trans(pk,sk);
    return trans;
  }
}.

(* abstract adversary type *)
(* quantum *) module type HVZK_Distinguisher (O: HVZK_Oracle) = {
  proc distinguish (pk : PK): bool
}.

 (* actual distinguishing game *)
module HVZK_Game (Sim: HVZK_Sim, P: Prover, V: Verifier, D: HVZK_Distinguisher) = {
  module OSim = HVZK_Sim_Oracle(Sim)
  module OHE = HVZK_HE_Oracle(P,V)
 
  proc main(n: int, b:bool) = {
    var sk, pk, result;
    
    (pk, sk) <@ P.keygen();
    if(b) {
      OSim.init(pk);
      result <@ D(OSim).distinguish(pk); 
    } else {
      OHE.init(pk, sk);
      result <@ D(OHE).distinguish(pk); 
    }
    return result;
  }
}.


end IDS.
