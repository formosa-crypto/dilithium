
require import Real RealSeries Distr AllCore.
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
  forall c s1, c \in dC => s1 \in ds1 =>
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

lemma trans_leak_supp :
  forall sk leak,
  leak <> [false] =>
  leak <> [true; false] =>
  leak <> [true; true; false] =>
    (None, leak) \notin trans sk.
proof.
move => sk L notF notTF notTTF /=.
rewrite /support => /=.
suff: mu1 (trans sk) (None, L) = 0%r.
  move => H; rewrite H; by trivial.
rewrite /trans.
rewrite dlet1E; apply sum0_eq => sig /=.
rewrite RField.mulf_eq0; right => /=.
case: sig => /= st.
rewrite dlet1E; apply sum0_eq => /= c.
rewrite RField.mulf_eq0; right => /=.
rewrite /(\o) dunit1E => /=.
suff:
  (let (resp, leak) = respond sk c st in
   (if resp = None then None else Some (c, oget resp), leak)) <>
   (None, L).
  move => H; rewrite H; trivial.
rewrite /respond => /=.
case sk => /= a s1 s2.
case st => /= y w.
case (check_znorm (y + diagc c *^ s1)).
+ move => _ /=.
  case (check_lowbits (y + diagc c *^ s1)) => /=.
  - move => _ /=.
    case (checkhint (makehint
           ((w + (- diagc c *^ s2)) +
             diagc c *^ lowbits (a *^ s1 + s2)))).
    * move => _ => /=; trivial.
    * move => _; rewrite eq_sym; assumption.
  - move => _; rewrite eq_sym; assumption.
+ move => _; rewrite eq_sym; assumption.
qed.

lemma simu_leak_supp :
  forall pk sk leak, (pk, sk) \in keygen =>
  leak <> [false] =>
  leak <> [true; false] =>
  leak <> [true; true; false] =>
    (None, leak) \notin simu pk.
proof.
admitted.

op leakage_simulable (leak : leak_t) =
  forall pk sk, (pk, sk) \in keygen =>
    mu1 (trans sk) (None, leak) = mu1 (simu pk) (None, leak).

lemma valid_keys_decomp :
  forall pk sk, (pk, sk) \in keygen => exists a s1 s2, s1 \in ds1 /\ s2 \in ds2 /\ sk = (a, s1, s2) /\ pk = (a, a *^ s1 + s2).
proof.
  move => pk sk.
  case sk => a s1 s2.
  case pk => a' t.
  move => valid_keys.
  exists a s1 s2.
  
admitted.

lemma trans_F_closedform :
  forall a s1 s2,
    mu1 (trans (a, s1, s2)) (None, [false]) =
    mu1 (dlet dy (fun y =>
      dmap dC (fun c =>
        let z = y + (diagc c) *^ s1 in
        if check_znorm z then Some z else None
      )
    )) None.
proof.
  rewrite /trans => a s1 s2.
  rewrite /commit => /=.
  rewrite dlet_dmap => /=.
  (* questionable stuff below *)

  (* How to rewrite more than 1 times again? *)
  rewrite dlet1E dlet1E => /=.
  apply eq_sum => y /=.
  congr.
  rewrite dmap1E dmap1E => /=.
  congr => /=.
  apply fun_ext => c /=.
  rewrite /(\o) /(\o) => /=.
  rewrite /respond => /=.
  case (check_znorm (y + diagc c *^ s1)) => /=.
  + case (check_lowbits (y + diagc c *^ s1)) => /=.
    - case (checkhint
           (makehint
              ((a *^ y + (- diagc c *^ s2)) +
               diagc c *^ lowbits (a *^ s1 + s2)))) => /=;
      rewrite /pred1 /pred1 /=; by trivial.
    - rewrite /pred1 /pred1 /=; by trivial.
  + by trivial.
qed.

lemma simu_F_closedform :
  forall a t,
    mu1 (simu (a, t)) (None, [false]) =
    mu1 (dlet (dbiased line12_magicnumber) (fun b => if b then dmap dsimz Some else dunit None)) None.
proof.
  rewrite /simu => a t /=.
  rewrite dlet1E dlet1E => /=.
  congr => /=.
  apply fun_ext => b.
  congr.
  case b.
  - move => bT /=.
    rewrite dlet1E sum0_eq => /=.
    + move => z.
      case (check_lowbits z) => /= _.
      * rewrite RField.mulf_eq0; right => /=.
        rewrite dlet1E; apply sum0_eq => /= y.
        rewrite RField.mulf_eq0; right => /=.
        rewrite dlet1E; apply sum0_eq => /= c.
        rewrite RField.mulf_eq0; right => /=.
        case (checkhint
          (makehint
           ((a *^ z + (- diagc c *^ t)) + diagc c *^ lowbits t))) => /= _;
        apply dunit1E.
      * rewrite RField.mulf_eq0; right => /=.
        apply dunit1E.
    + rewrite dmap1E.
      rewrite /(\o) /pred1 mu0; done.
  - move => bF.
    rewrite dunit1xx dunit1xx; done.
qed.

lemma leak_simulable_F :
  leakage_simulable [false].
proof.
  rewrite /leakage_simulable.
  move => pk sk valid_keys.
  apply valid_keys_decomp in valid_keys; case valid_keys => a s1 s2 keys_tuples.
  case keys_tuples => s1_supp keys_tuples.
  case keys_tuples => s2_supp keys_tuples.
  case keys_tuples => sk_val pk_val; subst.
  rewrite /trans => /=.
  rewrite dlet1E => /=.
admitted.

lemma leak_simulable_TF :
  leakage_simulable [true; false].
proof.
admitted.

lemma leak_simulable_TTF :
  leakage_simulable [true; true; false].
proof.
admitted.

lemma leak_simulable :
  forall leak pk sk, (pk, sk) \in keygen =>
    mu1 (trans sk) (None, leak) = mu1 (simu pk) (None, leak).
proof.
  move => leak pk sk keys_valid /=.
  rewrite /trans /simu /=.
  search dlet.

admitted.

lemma signleak_perfect_simu :
  forall sig leak pk sk, (pk, sk) \in keygen =>
    mu1 (trans sk) (sig, leak) = mu1 (simu pk) (sig, leak).
proof.
admitted.

