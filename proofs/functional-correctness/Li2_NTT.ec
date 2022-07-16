require import AllCore.
require import Li2_params.
import Li2_PolyReduceZp Zp ZModpRing.

op root_of_unity = inzmod 1753.

lemma root2_correct :
  exp root_of_unity 2 = inzmod 3073009.
proof.
  rewrite expr2 -inzmodM => //=.
qed.

lemma root4_correct :
  exp root_of_unity 4 = inzmod 3602218.
proof.
  have -> : 4 = 2 * 2 by trivial.
  rewrite exprM expr2 root2_correct -inzmodM => //=.
qed.

lemma root8_correct :
  exp root_of_unity 8 = inzmod 5010068.
proof.
  have -> : 8 = 4 * 2 by trivial.
  rewrite exprM expr2 root4_correct -inzmodM => //=.
qed.

lemma root16_correct :
  exp root_of_unity 16 = inzmod 7778734.
proof.
  have -> : 16 = 8 * 2 by trivial.
  rewrite exprM expr2 root8_correct -inzmodM => //=.
qed.

lemma root32_correct :
  exp root_of_unity 32 = inzmod 5178923.
proof.
  have -> : 32 = 16 * 2 by trivial.
  rewrite exprM expr2 root16_correct -inzmodM => //=.
qed.

lemma root64_correct :
  exp root_of_unity 64 = inzmod 3765607.
proof.
  have -> : 64 = 32 * 2 by trivial.
  rewrite exprM expr2 root32_correct -inzmodM => //=.
qed.

lemma root128_correct :
  exp root_of_unity 128 = inzmod 4808194.
proof.
  have -> : 128 = 64 * 2 by trivial.
  rewrite exprM expr2 root64_correct -inzmodM => //=.
qed.

lemma root256_correct :
  exp root_of_unity 256 = inzmod (-1).
proof.
  have -> : 256 = 128 * 2 by trivial.
  rewrite exprM expr2 root128_correct -inzmodM => //=.
qed.

lemma root_of_unity_correct :
  exp root_of_unity 512 = inzmod 1.
proof.
  have -> : 512 = 256 * 2 by trivial.
  rewrite exprM expr2 root256_correct -inzmodM => //=.
qed.
