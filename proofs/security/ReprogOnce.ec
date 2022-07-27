require import AllCore Distr DBool PROM List.
import Biased.

require import Dexcepted.
require import Dfilter.
require import Real RealSeries.

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
  include var G0[init]

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
op dWCoZ sk : (W * C * Z option) distr =
  dlet (commit sk) (fun wst =>
  let (w, st) = wst in
  dlet dC (fun c =>
  let z = respond st c in
  dunit (w, c, z))).

(* Transcript distribution, conditioned on accept.
 * Main idea here is the use of `drestrict`.
 *)

op dWCoZ_acc sk = dscale (drestrict (dWCoZ sk) (fun wcz => let (w, c, z) = wcz in z <> None)).
op dWCZ_acc sk = dmap (dWCoZ_acc sk) (fun wcoz => let (w, c, oz) = wcoz in (w, c, oget oz)).

(* Alternative definition:
 *
 * require import Dexcepted.
 * op dWCoZ_acc' sk = dscale ((dWCZ sk) \ (fun wcz => let (w, c, z) = wcz in z = None)). *)

(* Transcript, conditioned on reject.
 * Constructed similarly as above.
 *)
op dWCoZ_rej sk = dscale (drestrict (dWCoZ sk) (fun wcz => let (w, c, z) = wcz in z = None)).
op dWC_rej sk = dmap (dWCoZ_rej sk) (fun wcz => let (w, c, _) = wcz in (w, c)).

(* Accept and reject probabilities *)
op p_acc sk = mu (dWCoZ sk) (fun wcz => let (w, c, oz) = wcz in oz <> None).
op p_rej sk = mu (dWCoZ sk) (fun wcz => let (w, c, oz) = wcz in oz = None).

lemma p_rej_E sk :
  p_rej sk = 1%r - p_acc sk.
proof. admitted.

(* Helper lemma, hopefully in the standard library *)
lemma conditional_probability_fact ['a 'b] (dAB : ('a * 'b) distr) :
  is_lossless dAB =>
  dAB = dlet (dfst dAB) (fun a => dAB \ (fun (ab :'a * 'b) => fst ab <> a)).
proof.
admitted.

(* Now state the alternative way of sampling transcript is correct *)
lemma conditional_sampling_transcript sk :
  dWCoZ sk = dlet (dbiased (p_acc sk)) (fun f =>
    if f then
      dWCoZ_acc sk
    else
      dWCoZ_rej sk).
proof.
(* Some nasty conditional probability manipulation...
 * Maybe helper lemma above helps.
 *)
admitted.

(* Helper module to call bypr... *)
module LoopBodies = {
  include var G0[init]
  proc body1() = {
    var w, c, oz;
    (w, c, oz) <$ dWCoZ sk;
    return (w, c, oz);
  }

  proc body2() = {
    var w, c, oz, st;
    (w, st) <$ commit sk;
    c <$ dC;
    oz <- respond st c;
    return (w, c, oz);
  }

  proc body3() = {
    var w, c, oz, f;
    f <$ dbiased (p_acc sk);
    if(f)
      (w, c, oz) <$ dWCoZ_acc sk;
    else
      (w, c, oz) <$ dWCoZ_rej sk;
    return (w, c, oz);
  }
}.

lemma pr_body1 x &m sk :
  G0.sk{m} = sk =>
  Pr[LoopBodies.body1() @ &m : res = x] = mu1 (dWCoZ sk) x.
proof.
move => *.
byphoare (_ : (G0.sk = sk) ==> (res = x)) => //=.
proc.
rnd (fun r => r = x).
auto => /#.
qed.

equiv hop_body2 :
  LoopBodies.body1 ~ LoopBodies.body2 :
  ={G0.sk} ==> ={res}.
proof. admitted.

lemma pr_body2 x &m sk :
  G0.sk{m} = sk =>
  Pr[LoopBodies.body2() @ &m : res = x] = mu1 (dWCoZ sk) x.
proof.
move => *.
have <- : Pr[LoopBodies.body1() @ &m : res = x] = Pr[LoopBodies.body2() @ &m : res = x].
  byequiv.
  conseq (_ : ={G0.sk} ==> ={res}). trivial. trivial.
  apply hop_body2. trivial. trivial.
rewrite (pr_body1 x &m sk) => /#.
qed.

lemma sum_over_bool (f : bool -> real):
  sum (fun b => f b) = f true + f false.
proof.
rewrite (sumE_fin _ [true; false]) /#.
qed.

equiv hop_body3 :
  LoopBodies.body2 ~ LoopBodies.body3 :
  ={G0.sk} ==> ={res}.
proof.
  bypr res{1} res{2}; 1: auto => /#.
move => &1 &2 x eq_sk.
rewrite (pr_body2 x &1 G0.sk{1}) => //.
byphoare (_: (G0.sk = G0.sk{1}) ==> (res = x)) => //=; 2: subst => //=.
proc.
seq 1: f (p_acc G0.sk{1}) (mu1 (dWCoZ_acc G0.sk{1}) x) (p_rej G0.sk{1}) (mu1 (dWCoZ_rej G0.sk{1}) x) #pre => //=.
- by auto.
- rnd; auto => /> /=.
  rewrite dbiasedE => /=.
  rewrite !clamp_id => //.
  rcondt 1 => //=.
  by rnd (pred1 x); skip => /> /#.
- rnd; auto => /> /=.
  rewrite dbiasedE => /=.
  rewrite !clamp_id => //.
  by rewrite p_rej_E => //=.
- rcondf 1 => //=.
  by rnd (pred1 x); skip => /#.
- move => *; subst.
  rewrite conditional_sampling_transcript.
  rewrite dlet1E /=.
  rewrite sum_over_bool => /=.
  rewrite !dbiased1E => /=.
  rewrite !clamp_id => //=.
  smt(p_rej_E).
qed.

(* Replaces the transcript generation with the above *)
module G0A = {
  include var G0[init]

  proc sign(m: M) = {
    var w, c, z, f;

    (* Silences unused variables warning *)
    w <- witness;
    c <- witness;
    z <- witness;

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
  ={m, G0.sk} ==> ={res}.
proof.
proc.
while (#pre /\ (oz{1} <> None => (={w, c} /\ oget oz{1} = z{2}))).
call (_ : true ==> true); first proc; auto => //=.
transitivity{1}
  {(w, c, oz) <$ dWCoZ G0.sk;}
  (={G0.sk} ==> ={m, G0.sk, w, c, oz})
  (={G0.sk} ==> (={m, G0.sk} /\ (oz{1} <> None => ={w, c} /\ oget oz{1} = z{2})) /\ (oz{1} = None <=> !f{2})).
  smt(). smt().

rnd: *0 *0; auto => />.
move => *.
split.
  admit.
move => *.
split.
  admit.
  admit.

admit.

auto => />.
qed.

(* Same idea with G0A *)
module G1A = {
  include var G0[init]
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
  ={m, G0.sk} ==> ={res}.
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
  ={m, G0.sk} ==> ={res}.
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
  ={m, G0.sk} ==> ={res}.
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
    if(min_entropy (dfst dWC_rej) < alpha) {
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
    if(min_entropy (dfst dWC_rej) < alpha) {
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
