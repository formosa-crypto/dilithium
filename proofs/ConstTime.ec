require import Real RealSeries Distr AllCore.
require import List Distr DBool Finite.
clone import Biased.
require import FinType.
require import StdBigop.
import Bigreal BRA.

type matrix.
type vector.
type scalar.
op ( *^ ) : matrix -> vector -> vector.
op ( * ) : scalar -> vector -> vector.
op ( + ) : vector -> vector -> vector.
op ( - ) : vector -> vector -> vector.
op [ - ] : vector -> vector.

clone import FinType as FinVector_t with type t <- vector.

axiom vector_move_add :
  forall (u v w : vector), u + v = w <=> u = w - v.

type leak_t = bool list.
type sk_t = matrix * vector * vector.
type pk_t = matrix * vector.
type commit_t = vector.
type st_t = vector * vector.
type challenge_t = scalar.

op [lossless full uniform] dA : matrix distr.
op [lossless uniform] ds1 : vector distr.
op [lossless uniform] ds2 : vector distr.
op [lossless uniform] dy : vector distr.
op dC : challenge_t distr.
op highbits, lowbits : vector -> vector.
op check_znorm : vector -> bool.

op keygen : (pk_t * sk_t) distr =
  dlet dA (fun a =>
    dlet ds1 (fun s1 =>
      dlet ds2 (fun s2 =>
        let t = a *^ s1 + s2 in
        dunit ((a, t), (a, s1, s2))
  ))).

lemma pk_decomp : forall a' t' a s1 s2,
  ((a', t'), (a, s1, s2)) \in keygen =>
  a' = a /\ t' = a *^ s1 + s2.
proof.
move => a' t' a s1 s2 valid_keys.
(* TODO this should be very provable *)
admitted.

op line12_magicnumber : real = (size (to_seq check_znorm))%r / (size (to_seq (support dy)))%r.
op [lossless uniform] dsimz : vector distr.

axiom dsimz_supp :
  forall z, z \in dsimz <=> check_znorm z.

lemma dsimz1E :
  forall z, check_znorm z =>
    mu1 dsimz z = inv (size (to_seq check_znorm))%r.
proof.
(* TODO provable from dsimz_supp and dsimz_ll *)
admitted.

axiom masking_range :
  forall c s1 z0, c \in dC => s1 \in ds1 => check_znorm z0 =>
    z0 - c * s1 \in dy.

(* transcript + leakage
 *
 * Supposedly = sig_t option * leak_t.
 * Probably doesn't matter that it does. *)
type trans_leak_t.

(* Failed on first znorm check *)
op failed_znorm : trans_leak_t.

(* Second half of transcript
 * The actual definition probably doesn't matter here? *)
op trans_second_half (z : vector) (c : scalar) (w' t0 : vector) : trans_leak_t. (* =
  if check_znorm z then
    if check_lowbits w' then
      let h = makehint (w' + c * t0) in
      if checkhint h then
        (Some (c, (z, h)), [true; true; true])
      else
        (None, [true; true; false])
    else
      (None, [true; false])
  else
    (None, [false]). *)

op transz c s1 =
  dmap dy (fun y =>
    let z = y + c * s1 in
    if check_znorm z then Some z else None
  ).

op dsimoz = dlet (dbiased line12_magicnumber) (fun b => if b then dmap dsimz Some else dunit None).

(* print mu1_uni_ll. *)
lemma line12_magic_some :
  forall c s1 z0, c \in dC => s1 \in ds1 => check_znorm z0 =>
    mu1 (transz c s1) (Some z0) = 1%r / (size (to_seq (support dy)))%r.
proof.
  move => c s1 z0 c_valid s1_valid z0_valid.
  rewrite /transz dmap1E /pred1 /(\o) => /=.
  rewrite (mu_eq _ _ (fun y => y + c * s1 = z0)). move => y. smt().
  have -> : (fun y => y + c * s1 = z0) = pred1 (z0 - c * s1).
    apply fun_ext => y. rewrite /pred1.
    by rewrite vector_move_add //.
  rewrite mu1_uni_ll ?dy_uni ?dy_ll.
  suff -> : (z0 - c * s1) \in dy by trivial.
  exact masking_range.
qed.

lemma line12_outofbound :
  forall c s1 z0, c \in dC => s1 \in ds1 => ! (check_znorm z0) =>
    (Some z0) \notin (transz c s1).
proof.
move => c s1 z0 c_valid s1_valid z0_invalid.
rewrite /transz /pred1 /(\o) => /=.
rewrite supp_dmap => /#.
qed.

lemma sumD1_None (f : 'a option -> real) :
  summable f =>
  sum f = sum (fun y => f (Some y)) + f None.
proof.
move => sum_f; rewrite (sumD1 f None) // RField.addrC; congr.
rewrite (sum_partition Some (fun y => f (Some y))).
exact (summable_inj Some).
apply eq_sum => -[|x /=]; 1: by rewrite /= sum0.
rewrite (sumE_fin _ [x]) // /#.
qed.

lemma sum_characteristic (P : 't -> bool) (v : real) :
  is_finite P =>
  sum (fun z => if P z then v else 0%r) = (size (to_seq P))%r * v.
proof.
move => P_finite.
print sumr_const.
print sumE_fin.
rewrite (sumE_fin _ (to_seq P)) /=.
- apply uniq_to_seq => //.
- smt(mem_to_seq).
rewrite -big_mkcond Bigreal.sumr_const; congr.
rewrite count_predT_eq_in => //.
move => z; apply mem_to_seq => //.
qed.

lemma line12_magic_none :
  forall c s1, c \in dC => s1 \in ds1 =>
    mu1 (transz c s1) None = 1%r - (size (to_seq check_znorm))%r / (size (to_seq (support dy)))%r.
proof.
move => c s1 c_valid s1_valid.
have sumz : (sum (fun z => mu1 (transz c s1) z) = 1%r).
  by rewrite - weightE; apply dmap_ll; apply dy_ll.
rewrite sumD1_None /= in sumz.
  by apply summable_mu1.
suff: sum (fun (y : vector) => mu1 (transz c s1) (Some y)) = 
  (size (to_seq check_znorm))%r / (size (to_seq (support dy)))%r by smt().
clear sumz.
have -> :
  (fun z => mu1 (transz c s1) (Some z)) =
  (fun z => if check_znorm z then 1%r / (size (to_seq (support dy)))%r else 0%r).
  apply fun_ext => z; case (check_znorm z).
  + move => z_good.
    rewrite line12_magic_some => /#.
  + move => z_out.
    apply supportPn.
    apply line12_outofbound => //.
apply sum_characteristic.
by apply (finite_leq predT<:vector> check_znorm) => //; apply finite_t.
qed.

lemma sum_over_bool (f : bool -> real):
  sum (fun b => f b) = f true + f false.
proof.
rewrite (sumE_fin _ [true; false]) //.
move => -[|] //.
qed.

axiom mask_size :
  size (to_seq check_znorm) < size (to_seq (support dy)).

axiom mask_nonzero :
  0 < size (to_seq check_znorm).

(* Now 40% less magical! *)
lemma line12_magic :
  forall c s1, c \in dC => s1 \in ds1 =>
  transz c s1 = dsimoz.
proof.
move => c s1 c_valid s1_valid.
apply eq_distr => z.
case z.
- rewrite line12_magic_none //.
  apply eq_sym; rewrite dlet1E sum_over_bool /=.
  rewrite dmap1E /pred1 /(\o) mu0 /=.
  rewrite dunit1E dbiased1E /line12_magicnumber /=.
  rewrite clamp_id; smt(mask_nonzero mask_size).
- move => z.
  case (check_znorm z).
  + move => z_valid.
    rewrite line12_magic_some //.
    rewrite eq_sym /line12_magicnumber dlet1E sum_over_bool /=.
    rewrite dunit1E /=.
    rewrite dmap1E /pred1 /(\o) /=.
    rewrite dsimz1E //=.
    rewrite dbiased1E /=.
    rewrite clamp_id; smt(mask_nonzero mask_size).
  + move => z_invalid.
    have -> : mu1 (transz c s1) (Some z) = 0%r.
      apply supportPn; apply line12_outofbound; by assumption.
    apply eq_sym; apply supportPn.
    rewrite supp_dlet.
    (* abuse of smt? *)
    smt(supp_dmap supp_dunit dsimz_supp).
qed.

op commit (sk : sk_t) : (commit_t * st_t) distr =
  let (a, s1, s2) = sk in
    dmap dy (fun y =>
      let w = a *^ y in
      (highbits w, (y, w))).

op respond (sk : sk_t) (c : challenge_t) (st : st_t) : trans_leak_t =
  let (a, s1, s2) = sk in
  let t0 = lowbits (a *^ s1 + s2) in
  let (y, w) = st in
  let z = y + c * s1 in
  let w' = w - c * s2 in
  if check_znorm z then
    trans_second_half z c w' t0
  else
    failed_znorm.

op trans (sk : sk_t) : trans_leak_t distr =
  dlet (commit sk) (fun W =>
    let (w1, st) = W in
    dmap dC (fun c =>
      respond sk c st
    )
  ).

op simu (pk : pk_t) : trans_leak_t distr =
  let (a, t) = pk in
  let t0 = lowbits t in
  dlet dC (fun c =>
  dlet (dbiased line12_magicnumber) (fun b =>
    if b then
      dmap dsimz (fun z =>
        let w' = a *^ z - c * t in
        trans_second_half z c w' t0
      )
    else
      dunit failed_znorm
  )).

(* HVZK game as found in KLS.
 * Can be generalized for leakage.
 * Commitment-recoverable optimization included *)
module HVZK_Games = {
  (* Adversary gets HVZK transcript *)
  proc game0(sk: sk_t) = {
    var w, c, z, st;
    (w, st) <$ commit sk;
    c <$ dC;
    z <- respond sk c st;
    return (c, z);
  }

  (* Another (equivalent) way to write game0.
   * Mostly just inlining functions and reordering instructions. *)
  proc game1(sk: sk_t) = {
    var a, s1, s2, w, w', y, c, z, t, t0;
    var result;

    (a, s1, s2) <- sk;
    t <- a *^ s1 + s2;
    t0 <- lowbits t;
    c <$ dC;
    y <$ dy;
    w <- a *^ y;
    z <- y + c * s1;
    if(check_znorm z) {
      w' <- w - c * s2;
      result <- trans_second_half z c w' t0;
    } else {
      result <- failed_znorm;
    }
    return result;
  }

  (* Compute w' using only public information *)
  proc game2(sk: sk_t) = {
    var a, s1, s2, w, w', y, c, z, t, t0;
    var result;

    (a, s1, s2) <- sk;
    t <- a *^ s1 + s2;
    t0 <- lowbits t;
    c <$ dC;
    y <$ dy;
    w <- a *^ y;
    z <- y + c * s1;
    w' <- a *^ z + c * t;
    if(check_znorm z) {
      w' <- w - c * s2;
      result <- trans_second_half z c w' t0;
    } else {
      result <- failed_znorm;
    }
    return result;
  }

  (* Rewrite relevant parts of the above as op *)
  proc game3(sk: sk_t) = {
    var a, s1, s2, oz, z, c, t, t0, w';
    var result;
    (a, s1, s2) <- sk;
    t <- a *^ s1 + s2;
    t0 <- lowbits t;
    c <$ dC;
    oz <$ transz c s1;
    if(oz = None) {
      result <- failed_znorm;
    } else {
      z <- oget oz;
      w' <- a *^ z + c * t;
      result <- trans_second_half z c w' t0;
    }
    return result;
  }

  (* Get (a, t) from public key *)
  proc game4(sk: sk_t, pk: pk_t) = {
    var a, a', s1, s2, oz, z, c, t, t0, w';
    var result;
    (a', s1, s2) <- sk;
    (a, t) <- pk;
    t0 <- lowbits t;
    c <$ dC;
    oz <$ transz c s1;
    if(oz = None) {
      result <- failed_znorm;
    } else {
      z <- oget oz;
      w' <- a *^ z + c * t;
      result <- trans_second_half z c w' t0;
    }
    return result;
  }

  (* Now simulate using only public information *)
  proc game5(pk: pk_t) = {
    var a, t, t0, w', c, oz, z;
    var result;
    (a, t) <- pk;
    t0 <- lowbits t;
    c <$ dC;
    oz <$ dsimoz;
    if(oz = None) {
      result <- failed_znorm;
    } else {
      z <- oget oz;
      w' <- a *^ z + c * t;
      result <- trans_second_half z c w' t0;
    }
    return result;
  }
}.

(*
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
case (check_znorm (y + c * s1)).
+ move => _ /=.
  case (check_lowbits (y + c * s1)) => /=.
  - move => _ /=.
    case (checkhint (makehint
           ((w - c * s2) + c * lowbits (a *^ s1 + s2)))).
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
        let z = y + c * s1 in
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
  case (check_znorm (y + c * s1)) => /=.
  + case (check_lowbits (y + c * s1)) => /=.
    - case (checkhint
           (makehint
              ((a *^ y - c * s2) +
               c * lowbits (a *^ s1 + s2)))) => /=;
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
           ((a *^ z - c * t) + c * lowbits t))) => /= _;
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

*)
