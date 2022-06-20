require import List Distr DBool.
clone import Biased.
require Matrix.

type poly_t.
clone import Matrix as PolyMatrix with type ZR.t <- poly_t.

type leak_t = bool list.
type sk_t = matrix * vector * vector.
type pk_t = matrix * vector.
type digest_t.
type commit_t = vector.
type st_t = vector * vector.
type challenge_t = poly_t.
type resp_t = vector * vector.
type sig_t = challenge_t * resp_t.

op [lossless full uniform] dA : matrix distr.
op [lossless uniform] ds1 : vector distr.
op [lossless uniform] ds2 : vector distr.
op hash : digest_t -> commit_t -> challenge_t.
op dy : vector distr.
op dC : challenge_t distr.
op highbits, lowbits : vector -> vector.
op makehint : vector -> vector.
op check_znorm, check_lowbits, checkhint : vector -> bool.

op line12_magicnumber : real.
op dsimz : vector distr.

axiom line12_magic :
  forall c s1, (exists mu w1, c = hash mu w1) => s1 \in ds1 =>
  (dmap dy (fun y =>
      let z = y + (diagc c) *^ s1 in
      if check_znorm z then Some z else None
  )) =
  (dlet (dbiased line12_magicnumber) (fun b => if b then dmap dsimz Some else dunit None)).

op keygen : (pk_t * sk_t) distr =
  dlet dA (fun a =>
    dlet ds1 (fun s1 =>
      dlet ds2 (fun s2 =>
        let t = a *^ s1 + s2 in
        dunit ((a, t), (a, s1, s2))
  ))).

op commit (sk : sk_t) : (commit_t * st_t) distr =
  let (a, s1, s2) = sk in
    dmap dy (fun y =>
      let w = a *^ y in
      (highbits w, (y, w))).

op respond (sk : sk_t) (c : challenge_t) (st : st_t) : resp_t option * leak_t =
  let (a, s1, s2) = sk in
  let t0 = lowbits (a *^ s1 + s2) in
  let (y, w) = st in
  let z = y + (diagc c) *^ s1 in
  if check_znorm z then
    if check_lowbits z then
      let h = makehint ((w + (-(diagc c) *^ s2) + (diagc c) *^ t0)) in
      if checkhint h then
        (Some (z, h), [true; true; true])
      else
        (None, [true; true; false])
    else
      (None, [true; false])
  else
    (None, [false]).

op trans (sk : sk_t) : (sig_t option * leak_t) distr =
  dlet (commit sk) (fun W =>
    let (w1, st) = W in
    dmap dC (fun c =>
      let (resp, leak) = respond sk c st in
      let sig = if resp = None then None else Some (c, oget resp) in
      (sig, leak)
    )
  ).

op simu (pk : pk_t) : (sig_t option * leak_t) distr =
  let (a, t) = pk in
  let t0 = lowbits t in
  dlet (dbiased line12_magicnumber) (fun b =>
    if b then
      dlet dsimz (fun z =>
        if check_lowbits z then
          dlet dy (fun y =>
            let w = a *^ y in
            let w1 = highbits w in
            dlet dC (fun c =>
              let h = makehint (a *^ z + (-(diagc c) *^ t) + (diagc c) *^ t0) in
              if checkhint h then
                dunit (Some (c, (z, h)), [true; true; true])
              else
                dunit (None, [true; true; false])
            )
          )
        else
          dunit (None, [true; false])
      )
    else
      dunit (None, [false])).

lemma zero_knowledge :
  forall sig pk sk, (pk, sk) \in keygen =>
    mu1 (trans sk) (Some sig, [true; true; true]) = mu1 (simu pk) (Some sig, [true; true; true]).
proof.
admitted.

lemma leak_simulable :
  forall leak pk sk, (pk, sk) \in keygen =>
    mu1 (trans sk) (None, leak) = mu1 (simu pk) (None, leak).
proof.
  move => leak pk sk keys_valid.
admitted.

lemma signleak_perfect_simu :
  forall sig leak pk sk, (pk, sk) \in keygen =>
    mu1 (trans sk) (sig, leak) = mu1 (simu pk) (sig, leak).
proof.
admitted.

