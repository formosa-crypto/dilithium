require import AllCore.
require import Li2_params.
import Li2_PolyReduceZp Zp ZModpRing.

op root_of_unity = inzmod 1753.

lemma root_of_unity_correct :
  exp root_of_unity 512 = inzmod 1.
proof.
suff: exp root_of_unity 256 = inzmod (-1) by smt(exprM expr2 inzmodM).
suff: exp root_of_unity 128 = inzmod 4808194 by smt(exprM expr2 inzmodM).
suff: exp root_of_unity 64 = inzmod 3765607 by smt(exprM expr2 inzmodM).
suff: exp root_of_unity 32 = inzmod 5178923 by smt(exprM expr2 inzmodM).
suff: exp root_of_unity 16 = inzmod 7778734 by smt(exprM expr2 inzmodM).
suff: exp root_of_unity 8 = inzmod 5010068 by smt(exprM expr2 inzmodM).
suff: exp root_of_unity 4 = inzmod 3602218 by smt(exprM expr2 inzmodM).
suff: exp root_of_unity 2 = inzmod 3073009.
  have -> : 4 = 2 * 2 by trivial.
  rewrite exprM => H; rewrite H.
  rewrite expr2 -inzmodM => //=.
smt(exprM expr2 inzmodM).
qed.
