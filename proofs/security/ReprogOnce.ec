require import AllCore Distr DBool PROM List.
import Biased.

require import Dexcepted.
require import Dfilter.
require import Real RealSeries.

(* Define some necessary abstract stuff *)

type M, W, C, Z, ST, PK, SK.

op [lossless] keygen : (PK * SK) distr.
op [lossless] commit : SK -> (W * ST) distr.
op [lossless uniform] dC : C distr.
op respond : ST -> C -> Z option.

require ReprogRej.

clone import ReprogRej as Li2_ReprogRej with
  type M = M,
  type X = W * M,
  type Y = C,
  type Z = Z.

import FullRO.

module ReprogOnce0 = {
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
module ReprogOnce1 = {
  include var ReprogOnce0[init]

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

lemma dWCoZ_ll sk :
  is_lossless (dWCoZ sk).
proof.
(* TODO don't use smt once Easycrypt is fixed *)
apply dlet_ll; first smt(commit_ll).
move => x; case x; move => * /=; apply dlet_ll; first apply dC_ll.
move => * /=; apply dunit_ll.
qed.


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
proof.
print mu_not.
print p_rej.
rewrite /p_rej.
have ->: (fun wcz : (W * C * Z option)=> let (w, c, oz) = wcz in oz = None) =
      predC (fun wcz => let (w, c, oz) = wcz in oz <> None) by apply fun_ext => ? /#.
have <-: weight (dWCoZ sk) = 1%r by apply dWCoZ_ll.
rewrite mu_not; rewrite /p_acc => //.
qed.

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
  include var ReprogOnce0[init]
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

  proc body4() = {
    var w, c, z, f;
    f <$ dbiased (p_acc sk);
    z <- witness; (* silences unused variable warning *)
    if(f)
      (w, c, z) <$ dWCZ_acc sk;
    else
      (w, c) <$ dWC_rej sk;
    return (w, c, f, z);
  }
}.

(*
lemma linearize sk :
  dlet (commit sk) (fun (w_st: W * ST) => dmap dC (fun c => (w_st.`1, c, respond w_st.`2 c)))
= dWCoZ sk.*)

lemma pr_body1 x &m sk :
  ReprogOnce0.sk{m} = sk =>
  Pr[LoopBodies.body1() @ &m : res = x] = mu1 (dWCoZ sk) x.
proof.
move => *.
byphoare (_ : (ReprogOnce0.sk = sk) ==> (res = x)) => //=.
proc.
rnd (fun r => r = x).
auto => /#.
qed.

lemma dWCoZ_linearize sk :
  (dlet (commit sk)
        (fun (w_st : W * ST) =>
           dmap dC (fun (c0 : C) => (w_st.`1, c0, respond w_st.`2 c0)))) =
  (dmap (dWCoZ sk)
        (fun (w_c_oz : W * C * Z option) => (w_c_oz.`1, w_c_oz.`2, w_c_oz.`3))).
proof.
  rewrite /dWCoZ => /=.
  have ->: (fun (w_c_oz : W * C * Z option) => (w_c_oz.`1, w_c_oz.`2, w_c_oz.`3)) =
           (fun x => x) by smt().
  rewrite dmap_id; congr => /=.
  apply fun_ext => wst; case wst => ?? /=.
  rewrite /dmap /(\o) => /#.
qed.

equiv hop_body2 :
  LoopBodies.body1 ~ LoopBodies.body2 :
  ={ReprogOnce0.sk} ==> ={res}.
proof.
proc.
rnd: *0 *0.
auto => /> &2.
split.
- move => * /=; congr; apply dWCoZ_linearize.
- move => _ wcoz H'. rewrite dWCoZ_linearize => //.
qed.

lemma pr_body2 x &m sk :
  ReprogOnce0.sk{m} = sk =>
  Pr[LoopBodies.body2() @ &m : res = x] = mu1 (dWCoZ sk) x.
proof.
move => *.
have <- : Pr[LoopBodies.body1() @ &m : res = x] = Pr[LoopBodies.body2() @ &m : res = x].
  byequiv.
  conseq (_ : ={ReprogOnce0.sk} ==> ={res}). trivial. trivial.
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
  ={ReprogOnce0.sk} ==> ={res}.
proof.
bypr res{1} res{2}; 1: auto => /#.
move => &1 &2 x eq_sk.
rewrite (pr_body2 x &1 ReprogOnce0.sk{1}) => //.
byphoare (_: (ReprogOnce0.sk = ReprogOnce0.sk{1}) ==> (res = x)) => //=; 2: subst => //=.
proc.
seq 1: f (p_acc ReprogOnce0.sk{1}) (mu1 (dWCoZ_acc ReprogOnce0.sk{1}) x) (p_rej ReprogOnce0.sk{1}) (mu1 (dWCoZ_rej ReprogOnce0.sk{1}) x) #pre => //=.
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

equiv hop_body4 :
  LoopBodies.body3 ~ LoopBodies.body4 :
  ={ReprogOnce0.sk} ==> (res{1}.`1 = res{2}.`1 /\
                         res{1}.`2 = res{2}.`2 /\
                         res{1}.`3 <> None <=> res{2}.`3 /\
                         res{1}.`3 <> None => oget res{1}.`3 = res{2}.`4).
proof.
proc; auto.
seq 1 1: (#pre /\ ={f}); 1: auto.
seq 0 1: (#pre); 1: auto.
if; 1: auto.
rnd (fun wcoz => let (w, c, oz) = wcoz in (w, c, oget oz))
    (fun wcz => let (w, c, z) = wcz in (w, c, Some z)).
auto => &2 /> f.
split; first smt().
move => *.
split.
- move => *.
  (* TODO state and proof fact relating dWCZ_acc and dWCoZ_acc *)
  admit.
move => *.
split.
admit.
move => *.
split; last smt().
admit.
admitted.

(* Replaces the transcript generation with the above *)
module G0A = {
  include var ReprogOnce0[init]

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

equiv G0A_hop : ReprogOnce0.sign ~ G0A.sign :
  ={m, ReprogOnce0.sk} ==> ={res}.
proof.
proc.
while (#pre /\ (oz{1} <> None => (={m, w, c} /\ oget oz{1} = z{2}))); 2: by auto => />.
call (_ : true ==> true); first proc; auto => //=.
transitivity{1}
  {(w, c, oz) <$ dWCoZ ReprogOnce0.sk;}
  (={ReprogOnce0.sk, m} ==> ={m, ReprogOnce0.sk, w, c, oz})
  (={ReprogOnce0.sk, m} ==> (={m, ReprogOnce0.sk} /\ (oz{1} <> None => ={w, c} /\ oget oz{1} = z{2})) /\ (oz{1} = None <=> !f{2})); 1: smt(); 1: smt().
- rnd: *0 *0; auto => />.
  move => *; split.
  - move => ? _; congr.
    rewrite dWCoZ_linearize => //.
  - move => _ ? ? /=; rewrite -dWCoZ_linearize => //.
print hop_bodies.

admit.
qed.

(* Same idea with G0A *)
module G1A = {
  include var ReprogOnce0[init]
  proc sign(m: M) = {
    var w, c, z, f;

    (* Silences unused variables warning *)
    w <- witness;
    c <- witness;
    z <- witness;

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

equiv G1A_hop : ReprogOnce1.sign ~ G1A.sign :
  ={m, ReprogOnce0.sk} ==> ={res}.
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
    z <- witness;

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
  ={m, ReprogOnce0.sk} ==> ={res}.
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
    z <- witness;

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
  ={m, ReprogOnce0.sk} ==> ={res}.
proof.
(* Should be trivial up to proving termination. *)
admitted.

(**

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



**)
