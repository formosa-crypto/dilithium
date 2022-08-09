require import AllCore RealLub RealFLub RealExp Distr.
require import AllCore Bool StdRing StdOrder RealLub.
require import Finite FinType List Binomial.
require import Ring StdRing StdOrder StdBigop Discrete.
require import RealFun RealSeq RealSeries.
(*---*) import RField RealOrder.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.

lemma nosmt predIpp (p: 'a -> bool) :
  predI p p = p.
proof.
by apply/fun_ext=> x; rewrite /predI; case (p x) => //. qed.

lemma nosmt predUpp (p: 'a -> bool) :
  predU p p = p.
proof.
by apply/fun_ext=> x; rewrite /predU; case (p x) => //. qed.

lemma lub1 c :
  lub (fun x => x = c) = c.
proof.
apply eqr_le; split => [|_].
- apply lub_le_ub; smt().
- apply lub_upper_bound; smt().
qed.

op scale_rset (E: real -> bool) c x =
  exists x0, E x0 /\ c * x0 = x.

lemma has_lub_scale E c :
  c > 0%r =>
  has_lub E =>
  has_lub (scale_rset E c).
proof.
move => gt0_c has_lubE; split; 1: smt().
exists (c * lub E) => cx; smt(lub_upper_bound).
qed.

lemma lub_scale0 E :
  nonempty E =>
  lub (scale_rset E 0%r) = 0%r.
proof. smt(lub1). qed.

lemma lub_scaleE E c :
  has_lub E =>
  c >= 0%r =>
  lub (scale_rset E c) = c * lub E.
proof.
move => has_lubE ge0_c; case (c > 0%r) => [gt0_c|]; last by smt(lub_scale0).
apply eqr_le; split => [|_].
- apply lub_le_ub; first by apply has_lub_scale.
  smt(lub_upper_bound).
- rewrite -ler_pdivl_mull //.
  apply lub_le_ub => // x Ex.
  rewrite ler_pdivl_mull //.
  smt(lub_upper_bound has_lub_scale). 
qed.

lemma log_le1 b x :
  b >= 1%r => 0%r < x <= 1%r => log b x <= 0%r.
proof.
rewrite /log => ge1_b bound_x.
case (ln b = 0%r); first (move => -> /#).
smt(lnV ln_ge0).
qed.

lemma le0_log b x :
  x <= 0%r => log b x = 0%r.
proof.
move => le0_x; suff: (ln x = 0%r) by smt().
exact ln_le0.
qed.

op is_fub (f: 'a -> real) r = forall x, f x <= r.
op has_fub (f: 'a -> real) = exists r, is_fub f r.

lemma has_fub_lub (f: 'a -> real) :
  has_fub f <=> has_lub (fun r => exists a, f a = r).
proof.
split.
- move => [r ub_r]; split; first (exists (f witness) => /#).
  exists r => /#.
- move => has_lub_imgf; exists (flub f) => ?.
  apply lub_upper_bound => /#.
qed.

lemma flub_upper_bound (F : 'a -> real) x : 
    has_fub F => F x <= flub F.
proof.
move => H; rewrite has_fub_lub in H.
apply lub_upper_bound => /#.
qed.

lemma flub_le_ub (F : 'a -> real) r :
    is_fub F r => flub F <= r.
proof.
move => H.
have ub_r : ub (fun (x : real) => exists (a : 'a), F a = x) r.
  move => y [a] <-; exact H.
apply lub_le_ub => //. 
split; [by exists (F witness) witness| by exists r].
qed.
lemma flub_le (f g: 'a -> real) :
  has_fub g =>
  (forall x, f x <= g x) => flub f <= flub g.
proof.
move => [ym is_ub_ym] le_fg; rewrite ler_lub //=; 1: smt(); 2: exists (f witness) => /#.
split; first exists (g witness) => /#.
exists ym; smt(has_fub_lub).
qed.

lemma flub_scale (f: 'a -> real) c :
  has_fub f =>
  c >= 0%r =>
  flub (fun x => c * f x) = c * flub f.
proof.
move => H ge0_c; rewrite -lub_scaleE => //.
rewrite has_fub_lub in H => //.
apply eq_lub => /#.
qed.
lemma flub_const c :
  flub (fun _ : 'a => c) = c.
proof.
apply eqr_le; split; first apply flub_le_ub => /#.
move => _; apply (@flub_upper_bound (fun _ => c) witness) => /#.
qed.

lemma has_fub_leq (f g: 'a -> real) :
  has_fub g =>
  (forall x, f x <= g x) =>
  has_fub f.
proof. move => [??] /#. qed.
lemma has_fub_scale (f: 'a -> real) c:
  has_fub f =>
  c >= 0%r =>
  has_fub (fun x => c * f x).
proof. move => [ym ub_ym] ge0_c; exists (c * ym) => /#. qed.

lemma has_fub_mu1 (d: 'a distr) :
  has_fub (mu1 d).
proof.
apply (@has_fub_leq _ (fun _ => 1%r)) => // /#.
qed.

(* -------------------------------------------------------------------- *)

(* probability of the most likely output *)
op p_max (p: 'a distr) = flub (mu1 p).
op min_entropy (p: 'a distr) = -log2 (p_max p).

lemma ge0_pmax (p: 'a distr) :
  0%r <= p_max p.
proof.
suff: mu1 p witness <= p_max p by smt(ge0_mu).
apply (@flub_upper_bound (mu1 p)); smt(le1_mu).
qed.
lemma gt0_pmax (p: 'a distr) x :
  x \in p => 0%r < p_max p.
proof.
move => in_xp; suff: p_max p >= mu1 p x by smt(ge0_mu).
apply (@flub_upper_bound (mu1 p)); smt(le1_mu).
qed.

lemma le1_pmax (p: 'a distr) :
  p_max p <= 1%r.
proof. by rewrite flub_le_ub. qed.
lemma ge0_me (p: 'a distr) :
  min_entropy p >= 0%r.
proof.
suff: log2 (p_max p) <= 0%r by smt().
case (p_max p > 0%r) => [gt0_p|]; 2: smt(le0_log).
apply log_le1 => //=; smt(le1_pmax).
qed.

lemma me_boundE alpha (d: 'a distr) x :
  x \in d =>
  min_entropy d >= alpha <=> p_max d <= 2%r ^ (-alpha).
proof.
move => in_xd.
have ->: (p_max d <= 2%r ^ -alpha) <=>
         (log2 (p_max d) <= log2 (2%r ^ -alpha))
  by smt(log_mono gt0_pmax exp_gt0).
have ->: log2 (2%r ^ -alpha) = -alpha by apply logK.
smt().
qed.

lemma uniform_pmax (d: 'a distr) :
  is_uniform d =>
  p_max d = weight d / (size (to_seq (support d)))%r.
proof.
move => unif_d; apply eqr_le; split.
- apply flub_le_ub => /= x.
  rewrite mu1_uni //.
  case (x \in d) => _; first by trivial.
  apply divr_ge0; first exact ge0_weight.
  smt(size_ge0).
- move => _; case (weight d = 0%r) => ?; first by smt(ge0_pmax).
  have [x in_xd]: exists x, x \in d by smt(witness_support ge0_mu).
  have <-: mu1 d x = weight d / (size (to_seq (support d)))%r by smt(mu1_uni).
  apply (@flub_upper_bound (mu1 d)) => /=; smt(le1_mu).
qed.

lemma dnull_pmax ['a] :
  p_max dnull<:'a> = 0%r.
proof.
rewrite /p_max.
have ->: (mu1 dnull<:'a>) = fun _ => 0%r by smt(dnull1E).
exact flub_const.
qed.

lemma dunit_pmax (x: 'a) :
  p_max (dunit x) = 1%r.
proof.
apply eqr_le; split => [|_]; first apply flub_le_ub => x'; by apply le1_mu.
have @/b2r /= <- := dunit1E x x.
apply (@flub_upper_bound (mu1 (dunit x))); smt(le1_mu).
qed.

lemma dunit_me (x: 'a) :
  min_entropy (dunit x) = 0%r.
proof. smt(ln_eq0 dunit_pmax). qed.

op dcond (d : 'a distr) (p : 'a -> bool) = dscale (drestrict d p).
lemma weight_drestrict (d: 'a distr) (p: 'a -> bool) :
  weight (drestrict d p) = mu d p.
admitted. (* in PR 235 *)
lemma dcond_supp (d: 'a distr) (p: 'a -> bool) (x: 'a):
  x \in dcond d p <=> x \in d /\ p x.
proof.
rewrite supp_dscale supp_drestrict => //.
qed.

lemma dcond_ll (d: 'a distr) (p: 'a -> bool):
  mu d p > 0%r => is_lossless (dcond d p).
proof.
move => dcond_valid; apply dscale_ll; smt(weight_drestrict).
qed.

(* Chain rule of probability *)
lemma dcondE (d : 'a distr) (p : 'a -> bool) (p' : 'a -> bool) :
  mu (dcond d p) p' = mu d (predI p p') / mu d p.
proof.
by rewrite dscaleE drestrictE weight_drestrict.
qed.
lemma dcond1E (d : 'a distr) (p : 'a -> bool) (x : 'a):
  mu1 (dcond d p) x = if p x then mu1 d x / mu d p else 0%r.
proof.
rewrite dcondE; case: (p x) => [pxT|pxF]; last by rewrite mu0_false /#.
by congr; apply mu_eq => /#.
qed.

lemma dcondZ (d: 'a distr) (P: 'a -> bool) :
  mu d P = 0%r <=> dcond d P = dnull.
proof.
split => H.
- apply eq_distr => a; rewrite dnull1E.
  suff: a \notin (dcond d P) by smt(ge0_mu).
  rewrite dcond_supp; smt(mu_sub).
- have H': (mu (dcond d P) P = 0%r) by smt(dnullE).
  rewrite dcondE // in H'.
  smt(predIpp).
qed.

lemma dcond_dnull (P: 'a -> bool) :
  dcond dnull P = dnull.
proof.
apply eq_distr; smt(dnull1E dcond_supp supp_dnull ge0_mu).
qed.
lemma marginal_sampling (d : 'a distr) (f : 'a -> 'b) :
  d = dlet (dmap d f) (fun b => dcond d (fun a => f a = b)).
proof.
apply eq_distr => a; rewrite dlet1E /=.
rewrite (@sumE_fin _ [f a]) ?big_seq1 //=; 1: smt(dcond1E).
rewrite dcond1E dmap1E /(\o) /pred1 -/(pred1 a) /=.
case (a \in d) => [a_d|]; 2: smt(ge0_mu).
suff : mu d (fun (a0 : 'a) => f a0 = f a) > 0%r; smt(mu_sub).
qed.
lemma dcond_pmax (d: 'a distr) P :
  p_max (dcond d P) <= p_max d / mu d P.
proof.
rewrite /p_max.
have ->: (fun x => mu1 (dcond d P) x) =
         (fun x => if P x then mu1 d x / mu d P else 0%r).
  by apply fun_ext; apply dcond1E.
rewrite -(@flub_scale (mu1 d) (inv (mu d P))) //=; first smt(le1_mu).
- apply invr_ge0; by apply ge0_mu.
apply flub_le => /= [|x].
- rewrite (@has_fub_scale (mu1 d) (inv (mu d P))) => //; first by apply has_fub_mu1.
  apply invr_ge0; by apply ge0_mu.
case (P x) => [|_]; first smt(ge0_mu).
rewrite (@mulr_ge0 (mu1 d x) (inv (mu d P))) ?ge0_mu //.
apply invr_ge0; by apply ge0_mu.
qed.

lemma dcond_me (d: 'a distr) P :
  mu d P > 0%r =>
  min_entropy (dcond d P) >= -log2 (p_max d) + log2 (mu d P).
proof.
move => dcond_valid.
have [x x_supp]: exists x, x \in dcond d P by smt(witness_support dcond_supp).
have H: p_max (dcond d P) <= p_max d / mu d P by apply dcond_pmax.
rewrite -(@log_mono 2%r) in H => //=; first smt(gt0_pmax).
- apply divr_gt0 => //; first smt(dcond_supp gt0_pmax).
rewrite logM in H; first smt(dcond_supp gt0_pmax).
- smt(dcond_supp gt0_pmax).
suff: log 2%r (inv (mu d P)) = -log 2%r (mu d P); smt(lnV ge0_mu).
qed.
