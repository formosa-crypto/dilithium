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
(* So much for abusing smt... *)
smt(supp_dlet supp_dunit).
qed.

lemma keys_supp : forall a' t' a s1 s2,
  ((a', t'), (a, s1, s2)) \in keygen =>
  a \in dA /\ s1 \in ds1 /\ s2 \in ds2.
proof.
smt(supp_dlet supp_dunit).
qed.

op line12_magicnumber : real = (size (to_seq check_znorm))%r / (size (to_seq (support dy)))%r.
op [lossless uniform] dsimz : vector distr.

axiom dsimz_supp : support dsimz = check_znorm.

lemma dsimz1E :
  forall z, check_znorm z =>
    mu1 dsimz z = inv (size (to_seq check_znorm))%r.
proof.
  move => z ?.
  rewrite mu1_uni_ll ?dsimz_uni ?dsimz_ll; smt(dsimz_supp).
qed.

op dsimoz = dlet (dbiased line12_magicnumber) (fun b => if b then dmap dsimz Some else dunit None).

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
  proc game0(sk: sk_t) : trans_leak_t = {
    var w1, c, z, st;
    (w1, st) <$ commit sk;
    c <$ dC;
    z <- respond sk c st;
    return z;
  }

  (* Another (equivalent) way to write game0.
   * Mostly just inlining functions and reordering instructions. *)
  proc game1(sk: sk_t) : trans_leak_t = {
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
    if(check_znorm z) {
      w' <- a *^ z + c * t;
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

(* Crutch for `rnd*` tactic reordering variables *)
op swap_yw (wy : vector * vector) = let (w, y) = wy in (y, w).
lemma swap_yw_bij : bijective swap_yw by smt().

(* More crutch; dmap stuff...
 * Is this really not in the standard library?
 *)
lemma dmap_surj ['a 'b 'c] (f: 'a -> 'b) (g: 'b -> 'c) da b :
  bijective g => mu1 (dmap da f) b = mu1 (dmap da (g \o f)) (g b).
proof.
rewrite ?dmap1E ?/pred1 ?/(\o) => /#.
qed.

lemma HVZK_hop1 :
  equiv[HVZK_Games.game0 ~ HVZK_Games.game1 : ={sk} ==> ={res}].
proof.
proc.
swap{1} 1 1.
swap{2} [1..3] 1.
seq 1 1: (={sk, c}).
  rnd => //.
seq 0 1: (#pre /\ sk{2} = (a{2}, s1{2}, s2{2})).
  auto => /#.
seq 0 2: (#pre /\ t{2} = a{2} *^ s1{2} + s2{2} /\ t0{2} = lowbits t{2}).
  auto => /#.
seq 1 2: (#pre /\ st{1} = (y{2}, w{2})).
  rnd swap_yw swap_yw: *0 *0; auto => /=.
  move => &1 &2 H. (* TODO intro pattern? *)
  case H => H H'; case H => H H''; case H => H H'''; subst.
  case H' => H H'; subst.
  split; 1: smt().
  move => _.
  split.
  move => wy _.
  rewrite /commit /swap_yw /=.
  rewrite dmap_comp /=.
  rewrite (dmap_surj _ swap_yw) ?swap_yw_bij.
  congr.
    congr; smt().
    smt().
  move => _ yw.
  case yw => y w.
  move => yw_valid.
  rewrite supp_dmap in yw_valid.
  (* There's gotta be a better way about these next 3 lines *)
  case yw_valid => w1yw.
  case w1yw => w1 yw.
  case yw => y' w'.
  move => H /=; case H.
  move => H H'; case H' => ? ?; subst.
  rewrite /commit /= supp_dmap /= in H.
  smt(supp_dmap).
auto => /#.
qed.

lemma HVZK_hop2 :
  equiv[HVZK_Games.game2 ~ HVZK_Games.game3 : ={sk} ==> ={res}].
proof.
admitted.

lemma HVZK_hop3 :
  equiv[HVZK_Games.game2 ~ HVZK_Games.game3 : ={sk} ==> ={res}].
proof.
admitted.

lemma HVZK_hop4 :
  equiv[HVZK_Games.game3 ~ HVZK_Games.game4 : ={sk} /\ (pk{2}, sk{2}) \in keygen ==> ={res}].
proof.
admitted.

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

lemma HVZK_hop5 :
  equiv[HVZK_Games.game4 ~ HVZK_Games.game5 : (pk{1}, sk{1}) \in keygen /\ ={pk} ==> ={res}].
proof.
proc.
seq 4 3 : (#pre /\ ={a, t, t0, c} /\ a{1} = a'{1} /\ sk{1} = (a'{1}, s1{1}, s2{1}) /\ pk{1} = (a{1}, t{1}) /\ c{1} \in dC).
  auto; smt(pk_decomp).
seq 1 1 : (#pre /\ ={oz}).
  rnd; auto => //= &1 &2.

  (* The following "housekeeping" is just annoying... *)
  move => H; case H => H H'.
  case H => H H''; subst.
  case H' => H' H''; subst.
  case H' => H' H'''; subst.
  case H''' => H' H'''; subst.
  case H''' => H' H'''; subst.
  case H'' => H' H''; subst.
  case H'' => H' H''; subst.
  case H'' => H' c_valid; subst.
  have a_supp : a'{1} \in dA by smt(keys_supp).
  have s1_supp : s1{1} \in ds1 by smt(keys_supp).
  have s2_supp : s2{1} \in ds2 by smt(keys_supp).
  apply pk_decomp in H.
  case H => H H'; subst.
  clear H.

  (* Now comes the actual proof *)
  split.
  rewrite line12_magic //=.
  move => H oz ?.
  split; 1: smt(line12_magic).
  move => _.
  split.
  split; 2: trivial.
    (* keygen support... *)
    rewrite /keygen.
    apply supp_dlet => /=.
    exists a'{1}.
    split; 1: assumption.
    apply supp_dlet => /=.
    exists s1{1}.
    split; 1: assumption.
    apply supp_dlet => /=.
    exists s2{1}.
    split; 1: assumption.
    by apply supp_dunit.
  smt().
by auto.
qed.
