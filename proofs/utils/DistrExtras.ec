require import AllCore RealLub RealFLub RealExp Distr SDist.
require import AllCore Bool StdRing StdOrder RealLub.
require import Finite FinType List Binomial DBool.
require import Ring StdRing StdOrder StdBigop Discrete.
require import RealFun RealSeq RealSeries.
(*---*) import RField RealOrder.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
(*---*) import Biased.


lemma mu_eq_l (d2 d1 : 'a distr) p : d1 = d2 => mu d1 p = mu d2 p by smt().

lemma dletEunit (d : 'a distr) F : F == dunit => dlet d F = d by smt(dlet_d_unit).

lemma dletEconst (d2 : 'b distr) (d1 : 'a distr) (F : 'a -> 'b distr) :
  is_lossless d1 => 
  (forall x, F x = d2) => dlet d1 F = d2.
proof.
move => d1_ll F_const; apply/eq_distr => b; rewrite dletE.
rewrite (eq_sum _ (fun x : 'a => mu1 d1 x * mu1 d2 b)) 1:/#.
by rewrite sumZr -weightE d1_ll. 
qed.

(* -------------------------------------------------------------------- *)

(* not used but also not merged yet *)

lemma pmax_dcond (d: 'a distr) P :
  p_max (dcond d P) <= p_max d / mu d P.
proof.
rewrite /p_max.
have ->: (fun x => mu1 (dcond d P) x) =
         (fun x => if P x then mu1 d x / mu d P else 0%r).
  by apply fun_ext; apply dcond1E.
rewrite -(@flubZ (mu1 d) (inv (mu d P))) //=; first smt(le1_mu).
- apply invr_ge0; by apply ge0_mu.
apply ler_flub => /= [|x].
- rewrite (@has_fubZ (mu1 d) (inv (mu d P))) => //; first by apply has_fub_mu1.
  apply invr_ge0; by apply ge0_mu.
case (P x) => [|_]; first smt(ge0_mu).
rewrite (@mulr_ge0 (mu1 d x) (inv (mu d P))) ?ge0_mu //.
apply invr_ge0; by apply ge0_mu.
qed.


op min_entropy (p: 'a distr) = -log2 (p_max p).

lemma me_boundE alpha (d: 'a distr) x :
  x \in d =>
  min_entropy d >= alpha <=> p_max d <= 2%r ^ (-alpha).
proof.
move => in_xd.
have ->: (p_max d <= 2%r ^ -alpha) <=>
         (log2 (p_max d) <= log2 (2%r ^ -alpha))
  by smt(log_mono pmax_gt0 exp_gt0).
have ->: log2 (2%r ^ -alpha) = -alpha by apply logK.
smt().
qed.

lemma dunit_me (x: 'a) :
  min_entropy (dunit x) = 0%r.
proof. smt(ln_eq0 pmax_dunit). qed.

lemma dcond_me (d: 'a distr) P :
  mu d P > 0%r =>
  min_entropy (dcond d P) >= -log2 (p_max d) + log2 (mu d P).
proof.
move => dcond_valid.
have [x x_supp]: exists x, x \in dcond d P by smt(witness_support dcond_supp).
have H: p_max (dcond d P) <= p_max d / mu d P by apply pmax_dcond.
rewrite -(@log_mono 2%r) in H => //=; first smt(pmax_gt0).
- apply divr_gt0 => //; first smt(dcond_supp pmax_gt0).
rewrite logM in H; first smt(dcond_supp pmax_gt0).
- smt(dcond_supp pmax_gt0).
suff: log 2%r (inv (mu d P)) = -log 2%r (mu d P); smt(lnV ge0_mu).
qed.

lemma ge0_me (p: 'a distr) :
  min_entropy p >= 0%r.
proof.
suff: log2 (p_max p) <= 0%r by smt().
case (p_max p > 0%r) => [gt0_p|?]; 1:smt(log_le0 pmax_le1).
rewrite /log2 /log (_: p_max p = 0%r); smt(pmax_ge0 ln_le0).
qed.
