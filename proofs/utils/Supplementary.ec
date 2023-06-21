require import AllCore List RealSeries Finite.
require import StdBigop.
import Bigreal BRA StdOrder.RealOrder.

op image (f : 'a -> 'b) y = exists x, f x = y.
op injective_in P (f : 'a -> 'b) = 
  forall x y, P x => P y => f x = f y => x = y.


lemma fin_sum_cond (P : 't -> bool) f :
  is_finite P => 
  sum (fun z => if P z then f z else 0%r) = big predT f (to_seq P).
proof.
move => P_finite; rewrite (sumE_fin _ (to_seq P)) /= ?uniq_to_seq //.
- smt(mem_to_seq).
by apply eq_big_seq => x; smt(mem_to_seq).
qed.

lemma fin_sum_const (P : 't -> bool) (v : real) :
  is_finite P =>
  sum (fun z => if P z then v else 0%r) = (size (to_seq P))%r * v.
proof.
move => P_finite.
by rewrite fin_sum_cond // sumr_const RField.intmulr count_predT RField.mulrC.
qed.

lemma maxrr (z : int) : max z z = z by smt().
