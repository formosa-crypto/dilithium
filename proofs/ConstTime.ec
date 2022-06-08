require import List Distr DBool.
clone import Biased.
require Matrix.

type poly_t.
clone import Matrix as PolyMatrix with type ZR.t <- poly_t.

module AbstractLeakage = {
  var leakage : bool list
  proc init() = {
    leakage <- [];
  }
  proc leak(b) = {
    leakage <- b :: leakage;
  }
}.

type sk_t = matrix * vector * vector.
type pk_t = matrix * vector.

type digest_t.
type commit_t = vector.
type challenge_t = poly_t.
type hint_t = vector.
type resp_t = vector.
type sig_t = challenge_t * resp_t * hint_t.
op [lossless full uniform] dA : matrix distr.
op [lossless uniform] ds1 : vector distr.
op [lossless uniform] ds2 : vector distr.
op [lossless full uniform] dC : challenge_t distr.

(* Maybe not necessary; can just prove for all (pk, sk) for now. *)
(*
op keygen : (pk_t * sk_t) distr =
  dlet dA (fun A =>
    dlet ds1 (fun s1 =>
      dlet ds2 (fun s2 =>
        let t = A *^ s1 + s2 in
        dunit ((A, t), (A, s1, s2))))).
*)

type hashfn_t = digest_t -> commit_t -> challenge_t.
(* this may be ok since everything here is a finite set? *)
op [lossless full uniform] dH : hashfn_t distr.
module H = {
  var hashfn : hashfn_t
  proc init () = { hashfn <$ dH; }
  proc hash (mu : digest_t, w : commit_t) = {
    return hashfn mu w;
  }
}.

op dy : vector distr.
op highbits, lowbits : vector -> vector.
op makehint : vector -> vector.
op check_znorm, check_lowbits, checkhint : vector -> bool.

module Sign = {
  proc sign(sk : sk_t, mu : digest_t) : sig_t = {
    var a, s1, s2, t0;
    var w, w1, y, c, z, h;
    var good;

    (* suppress "uninitialized" warning *)
    (c, z, h) <- (ZR.zeror, zerov, zerov);

    (a, s1, s2) <- sk;
    t0 <- lowbits (a *^ s1 + s2);

    good <- false;
    while(good) {
      AbstractLeakage.leak(false);

      y <$ dy;
      w <- a *^ y;
      w1 <- highbits w;
      c <- H.hash(mu, w1);
      z <- y + (diagc c) *^ s1;
      AbstractLeakage.leak(check_znorm z);
      if(check_znorm z) {
        AbstractLeakage.leak(check_lowbits z);
        if(check_lowbits z) {
          h <- makehint (w + (-(diagc c) *^ s2) + (diagc c) *^ t0);
          AbstractLeakage.leak(checkhint h);
          if(checkhint h) {
            good <- true;
          }
        }
      }
    }
    return (c, z, h);
  }
}.

op line12_magicnumber : real.
op dsimz : vector distr.

axiom line12_magic :
  forall c s1, c \in dC => s1 \in ds1 =>
  (dmap dy (fun y =>
      let z = y + (diagc c) *^ s1 in
      if check_znorm z then Some z else None
  )) =
  (dlet (dbiased line12_magicnumber) (fun b => if b then dmap dsimz Some else dunit None)).

module SimLeak = {
  proc simulate(pk : pk_t) = {
    var a, t, t0;
    var z, c, h;
    var good, b;
    (a, t) <- pk;
    t0 <- lowbits t;
    good <- false;
    while(good) {
      AbstractLeakage.leak(false);

      b <$ dbiased line12_magicnumber;
      AbstractLeakage.leak(b);
      if(b) {
        z <$ dsimz;
        c <$ dC;
        AbstractLeakage.leak(check_lowbits z);
        if(check_lowbits z) {
          h <- makehint (a *^ z + (-(diagc c) *^ t) + (diagc c) *^ t0);
          AbstractLeakage.leak(checkhint h);
          if(checkhint h) {
            good <- true;
          }
        }
      }
    }
  }
}.

lemma ct : forall (a : matrix) (s1 s2 : vector) (sig : sig_t),
  (s1 \in ds1) => (s2 \in ds2) =>
  let t = a *^ s1 + s2 in
  equiv[Sign.sign ~ SimLeak.simulate :
    ={AbstractLeakage.leakage} /\ sk{1} = (a, s1, s2) /\ pk{2} = (a, t)
    ==>
    (* QUESTION: No way to state joint distributions as equivs? *)
    (res{1}, AbstractLeakage.leakage{1}) = (res{1}, AbstractLeakage.leakage{2})].
proof.
  move => a s1 s2 sig s1_short s2_short t /=.
admitted.
