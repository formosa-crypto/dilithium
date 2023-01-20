require import AllCore List RealSeries Finite.
require import StdBigop.
import Bigreal BRA.

pred image (f : 'a -> 'b) y = exists x, f x = y.
pred injective_in P (f : 'a -> 'b) = 
  forall x y, P x => P y => f x = f y => x = y.

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

lemma sum_over_bool (f : bool -> real):
  sum (fun b => f b) = f true + f false.
proof.
rewrite (sumE_fin _ [true; false]) /#.
qed.

lemma sum_characteristic (P : 't -> bool) (v : real) :
  is_finite P =>
  sum (fun z => if P z then v else 0%r) = (size (to_seq P))%r * v.
proof.
move => P_finite.
rewrite (sumE_fin _ (to_seq P)) /=.
- apply uniq_to_seq => //.
- smt(mem_to_seq).
rewrite -big_mkcond Bigreal.sumr_const; congr.
rewrite count_predT_eq_in => //.
move => z; apply mem_to_seq => //.
qed.

lemma map_mkseq (f : 'a -> 'b) (g: int -> 'a) (n : int) :
  0 <= n =>
  map f (mkseq g n) = mkseq (f \o g) n.
proof.
move => ge0_n.
apply (eq_from_nth witness).
rewrite size_map !size_mkseq //.
move => i rg_i.
rewrite size_map size_mkseq in rg_i.
rewrite (nth_map witness); first smt(size_mkseq).
by rewrite !nth_mkseq /#.
qed.


lemma leq_size_to_seq (p q : 'a -> bool) : 
  p <= q => is_finite q =>
  size (to_seq p) <= size (to_seq q).
proof.
move => sub_p_q fin_q.
have fin_p : is_finite p by apply (finite_leq _ _ sub_p_q).
apply uniq_leq_size; 1: exact uniq_to_seq.
by move => x; rewrite !mem_to_seq //; exact sub_p_q.
qed.

lemma maxrr (z : int) : max z z = z by smt().

op locked (x : 'a) = x axiomatized by unlock.
lemma lock (x : 'a) : x = locked x by rewrite unlock.
