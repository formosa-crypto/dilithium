require import AllCore Distr DBool PROM.
import Biased.

(* Define some necessary abstract stuff *)

type M, W, C, Z, ST, PK, SK.

op [lossless] keygen : (PK * SK) distr.
op commit : SK -> (W * ST) distr.
op [lossless uniform] dC : C distr.
op respond : ST -> C -> Z option.

clone import FullRO with
  type in_t <- W * M,
  type out_t <- C,
  op dout <- (fun _ => dC).

(* G0, G1: Pair of games that we want to distinguish *)
module G0 = {
  var sk : SK

  proc init() = {
    var pk;
    (pk, sk) <$ keygen;
  }

  proc sign(m: M) = {
    var w, st, c, oz;

    (* Silences unused variables warning *)
    w <- witness;
    c <- witness;

    oz <- None;
    while(oz = None) {
      (w, st) <$ commit sk;
      c <$ dC;
      oz <- respond st c;
      RO.set((w, m), c);
    }
    return (w, c, oget oz);
  }
}.

(* Moving RO.set outside while-loop *)
module G1 = {
  var sk : SK

  proc init() = {
    var pk;
    (pk, sk) <$ keygen;
  }

  proc sign(m: M) = {
    var w, st, c, oz;

    (* Silences unused variables warning *)
    w <- witness;
    c <- witness;

    oz <- None;
    while(oz = None) {
      (w, st) <$ commit sk;
      c <$ dC;
      oz <- respond st c;
    }
    RO.set((w, m), c);
    return (w, c, oget oz);
  }
}.

(* Next we reorganize transcript computation.
 * We want to first sample f=acc/rej,
 * then sample the rest of transcript conditioned on f.
 *)

(* Transcript distribution *)
op dWCZ sk : (W * C * Z option) distr =
  dlet (commit sk) (fun wst =>
  let (w, st) = wst in
  dlet dC (fun c =>
  let z = respond st c in
  dunit (w, c, z))).

(* Scales a subdistr. back to full *)
op scale_full (d : 'a distr) : 'a distr =
  mk (fun x => mu1 d x / weight d).

(* Transcript distribution, conditioned on accept.
 * Main idea here is the use of `drestrict`.
 *)
op dWCoZ_acc sk = scale_full (drestrict (dWCZ sk) (fun wcz => let (w, c, z) = wcz in z <> None)).
op dWCZ_acc sk = dmap (dWCoZ_acc sk) (fun wcoz => let (w, c, oz) = wcoz in (w, c, oget oz)).

(* Transcript, conditioned on reject.
 * Constructed similarly as above.
 *)
op dWCoZ_rej sk = scale_full (drestrict (dWCZ sk) (fun wcz => let (w, c, z) = wcz in z = None)).
op dWC_rej sk = dmap (dWCoZ_rej sk) (fun wcz => let (w, c, _) = wcz in (w, c)).

(* Accept and reject probabilities *)
op p_acc sk = mu (dWCZ sk) (fun wcz => let (w, c, z) = wcz in z <> None).
op p_rej sk = mu (dWCZ sk) (fun wcz => let (w, c, z) = wcz in z = None).

(* Helper lemma...
 * Hopefully it's in the standard library.
 * If not, things get somewhat interesting.
 *)
op marginal (dAB : ('a * 'b) distr) : 'a distr.
op conditional (dAB : ('a * 'b) distr) (a : 'a) : 'b distr.
lemma conditional_probability_fact ['a 'b] (dAB : ('a * 'b) distr) :
  dAB = dlet (marginal dAB) (fun a => dmap (conditional dAB a) (fun b => (a, b))).
proof.
admitted.

(* Now state the alternative way of sampling transcript is correct *)
lemma conditional_sampling_transcript sk :
  dWCZ sk = dlet (dbiased (p_acc sk)) (fun f =>
    if f then
      dlet (dWCZ_acc sk) (fun wcz => let (w, c, z) = wcz in dunit (w, c, Some z))
    else
      dlet (dWC_rej sk) (fun wc => let (w, c) = wc in dunit (w, c, None))).
proof.
(* Some nasty conditional probability manipulation...
 * Maybe helper lemma above helps.
 *)
admitted.

(* Replaces the transcript generation with the above *)
module G0A = {
  var sk : SK

  proc init() = {
    var pk;
    (pk, sk) <$ keygen;
  }

  proc sign(m: M) = {
    var w, c, z, f;

    (* Silences unused variables warning *)
    w <- witness;
    c <- witness;

    (* Maybe there's an argument to do another game with `oz` first? *)
    f <- false;
    while(!f) {
      f <$ dbiased (p_acc sk);
      if(f)
        (w, c, z) <$ dWCZ_acc sk;
      else
        (w, c) <$ dWC_rej sk;
      RO.set((w, m), c);
    }
    return (w, c, z);
  }
}.

equiv G0A_hop : G0.sign ~ G0A.sign :
  (* This`G0.sk{1} = Gg0A.sk{2}` looks sus *)
  ={m} /\ G0.sk{1} = G0A.sk{2} ==> ={res}.
proof.
(* Use the lemma proven earlier *)
admitted.

(* Same idea with G0A *)
module G1A = {
  var sk : SK

  proc init() = {
    var pk;
    (pk, sk) <$ keygen;
  }

  proc sign(m: M) = {
    var w, c, z, f;

    (* Silences unused variables warning *)
    w <- witness;
    c <- witness;

    f <- false;
    while(!f) {
      f <$ dbiased (p_acc sk);
      if(f)
        (w, c, z) <$ dWCZ_acc sk;
      else
        (w, c) <$ dWC_rej sk;
    }
    RO.set((w, m), c);
    return (w, c, z);
  }
}.

equiv G1A_hop : G1.sign ~ G1A.sign :
  ={m} /\ G1.sk{1} = G1A.sk{2} ==> ={res}.
proof.
(* Same idea as above *)
admitted.

(* Clean up and line up interface.
 * Equivalent to G0A up to reordering instructions. *)
module G0B = {
  var sk : SK

  proc init() = {
    var pk;
    (pk, sk) <$ keygen;
  }

  proc sign(m: M) = {
    var w, c, z, f;

    (* Silences unused variables warning *)
    w <- witness;
    c <- witness;

    f <- false;
    while(!f) {
      f <$ dbiased (p_acc sk);
      if(f) {
        (w, c, z) <$ dWCZ_acc sk;
        RO.set((w, m), c);
      }
      else {
        (w, c) <$ dWC_rej sk;
        RO.set((w, m), c);
      }
    }
    return (w, c, z);
  }
}.

equiv G0B_hop : G0A.sign ~ G0B.sign :
  ={m} /\ G0A.sk{1} = G0B.sk{2} ==> ={res}.
proof.
(* Should be trivial up to proving termination. *)
admitted.

(* Clean up. Equivalent to G1A up to reordering instructions. *)
module G1B = {
  var sk : SK

  proc init() = {
    var pk;
    (pk, sk) <$ keygen;
  }

  proc sign(m: M) = {
    var w, c, z, f;

    (* Silences unused variables warning *)
    w <- witness;
    c <- witness;

    f <- false;
    while(!f) {
      f <$ dbiased (p_acc sk);
      if(f) {
        (w, c, z) <$ dWCZ_acc sk;
        RO.set((w, m), c);
      }
      else {
        (w, c) <$ dWC_rej sk;
      }
    }
    return (w, c, z);
  }
}.

equiv G1B_hop : G1A.sign ~ G1B.sign :
  ={m} /\ G1A.sk{1} = G1B.sk{2} ==> ={res}.
proof.
(* Should be trivial up to proving termination. *)
admitted.

(* Now let's define the basic RO game that we plan to reduce to. *)

(* First, a couple ingredients. *)
op min_entropy ['a] (d : 'a distr) : real.
(* don't ask *)
op marginal3 (dABC : ('a * 'b * 'c) distr) : 'a distr.
(* min-entropy required *)
op alpha : real.

(*
 * GameA, GameB: Basic RO games that we plan to reduce to.
 * Adversary can make three possible queries, as discussed.
 * Only third query (reprog_rej) is different between GameA and GameB.
 *
 * The games are indistinguishable in ROM.
 * I hope same is true in QROM.
 *)
module GameA = {
  var good : bool

  proc init() = {
    good <- true;
  }

  proc h(w, m) = {
    var z;
    z <@ RO.get((w, m));
    return z;
  }

  proc reprog_acc(dWCZ_acc : (W * C * Z) distr, m : M) = {
    var w, c, z;
    if(min_entropy (marginal3 dWCZ_acc) < alpha) {
      good <- false;
    }
    (w, c, z) <$ dWCZ_acc;
    RO.set((w, m), c);
    return (w, c, z);
  }

  proc reprog_rej(dWC_rej : (W * C) distr, m : M) = {
    var w, c;
    if(min_entropy (marginal dWC_rej) < alpha) {
      good <- false;
    }
    (w, c) <$ dWC_rej;
    (* No reprog. *)
    (* RO.set((w, m), c); *)
    (* no return *)
  }
}.

(* Should this actually be a different module,
 * or should I just let the above take a coin?
 *)
module GameB = {
  var good : bool

  proc init() = {
    good <- true;
  }

  proc h(w, m) = {
    var z;
    z <@ RO.get((w, m));
    return z;
  }

  proc reprog_acc(dWCZ_acc : (W * C * Z) distr, m : M) = {
    var w, c, z;
    if(min_entropy (marginal3 dWCZ_acc) < alpha) {
      good <- false;
    }
    (w, c, z) <$ dWCZ_acc;
    RO.set((w, m), c);
    return (w, c, z);
  }

  proc reprog_rej(dWC_rej : (W * C) distr, m : M) = {
    var w, c;
    if(min_entropy (marginal dWC_rej) < alpha) {
      good <- false;
    }
    (w, c) <$ dWC_rej;
    (* reprog *)
    RO.set((w, m), c);
    (* no return *)
  }
}.

(* TODO Lemma
 * Bound GameA and GameB distinguishing advantage in terms of alpha?
 * TODO query counting too...
 *)

(* Reduction - G0 corresponds to GA *)
module G0R = {
  var sk : SK

  proc init() = {
    var pk;
    (pk, sk) <$ keygen;
  }

  proc sign(m: M) = {
    var w, c, z, f;

    (* Silences unused variables warning *)
    w <- witness;
    c <- witness;
    z <- witness;

    f <- false;
    while(!f) {
      f <$ dbiased (p_acc sk);
      if(f) {
        (w, c, z) <@ GameA.reprog_acc(dWCZ_acc sk, m);
      }
      else {
        GameA.reprog_rej(dWC_rej sk, m);
      }
    }
    return (w, c, z);
  }
}.

(* TODO equiv G0R.sign ~ G0B.sign?
 * Need to argue min-entropy of dW.
 * Everything else seems trivial.
 *)

(* Reduction - G1 corresponds to GB.
 *
 * TODO Code organization is suspect.
 * Maybe instantiate stuff with module types and parametrized modules?
 * Currently there's (unnecessary-looking) duplicate code.
 * For example, maybe G0R and G1R should be the same too?
 *)
module G1R = {
  var sk : SK

  proc init() = {
    var pk;
    (pk, sk) <$ keygen;
  }

  proc sign(m: M) = {
    var w, c, z, f;

    (* Silences unused variables warning *)
    w <- witness;
    c <- witness;
    z <- witness;

    f <- false;
    while(!f) {
      f <$ dbiased (p_acc sk);
      if(f) {
        (w, c, z) <@ GameB.reprog_acc(dWCZ_acc sk, m);
      }
      else {
        GameB.reprog_rej(dWC_rej sk, m);
      }
    }
    return (w, c, z);
  }
}.

(* TODO equiv G1R.sign ~ G1B.sign?
 * Should be trivial.
 *)
