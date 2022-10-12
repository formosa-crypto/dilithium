(* Natural Numbers as a subtype of [int] *)

require import StdOrder List.
require Int Subtype Bigop.

type nat.

clone import Subtype as StNat with
  type T <- int,
  type sT <- nat,
  op wsT <- 0,
  pred P <- (fun n : int => Int.(<=) 0 n).

(* Lifting operators *)
op (+) = Lift.lift2 Int.(+).
op max = Lift.lift2 Int.max.
op (<=) = fun n m => Int.(<=) (val n) (val m).

op ofint = insubd.
op ofnat = val.

const zero = ofint 0.

lemma ofintK (x : int) : 
  Int.(<=) 0 x => ofnat (ofint x) = x. 
proof. exact insubdK. qed.

lemma zeroP : ofnat zero = 0. 
proof. by rewrite ofintK. qed.

lemma zeroPv : val zero = 0. 
proof. exact ofintK. qed.


lemma ofnatK : cancel ofnat ofint.
proof. exact valKd. qed.

lemma natW P : 
  (forall x, Int.(<=) 0 x => P (ofint x)) => forall (n : nat), P n.
proof.
by move=> Hsub n; rewrite -ofnatK Hsub valP.
qed.

lemma natW2 P : 
  (forall x y, Int.(<=) 0 x => Int.(<=) 0 y => P (ofint x) (ofint y)) => 
  forall (n m : nat), P n m.
proof.
by move=> Hsub; apply natW => x ? /=; apply natW => y ? /=; exact Hsub.
qed.

lemma natW3 P : 
  (forall x y z, Int.(<=) 0 x => Int.(<=) 0 y => Int.(<=) 0 z => 
    P (ofint x) (ofint y) (ofint z)) => 
  forall (n m o: nat), P n m o.
proof.
by move=> Hsub; apply natW => x ? /=; apply natW2 => y z ? ? /=; exact Hsub.
qed.

lemma maxrC : commutative max. 
proof. smt(). qed.

lemma maxrA : associative max. 
proof. 
by apply natW3 => * /=; apply val_inj; rewrite !Lift.lift2E /#.
qed.

lemma max0r : left_id zero max.
proof.
apply natW => x _ /=. apply val_inj.
rewrite !Lift.lift2E ?zeroPv; smt(valP). 
qed.

clone Monoid as Max0Monoid with
  type t <- nat,
  op (+) <- max,
  op idm <- zero proof* by smt(maxrC maxrA max0r).

lemma max_ofnat n m : Int.max (ofnat n) (ofnat m) = ofnat (max n m) by smt. 

lemma ofnat_inj : injective ofnat by smt. 

lemma le0n n : zero <= n by smt. 

lemma le_maxn (n m o : nat) : max n m <= o <=> n <= o /\ m <= o by smt.

lemma maxnn (n : nat) : max n n = n.
proof. 
move: n. apply natW => //= x x_ge0. 
by apply StNat.val_inj; rewrite StNat.Lift.lift2E /#.
qed.

clone import Bigop as BigMax with 
  type t <= nat,
  op Support.idm <- zero,
  op Support.(+) <- max
proof* by smt(maxrC maxrA max0r).

import Int.

lemma ler_ofnat (n : nat) m : ofnat n <= m <=> 0 <= m /\ n <= ofint m by smt.

lemma ler_ofint i j : 0 <= i <= j => (ofint i <= ofint j) by smt.

lemma ler_ofint_ofnat (n : int) (m : nat) :
  0 <= n =>
  (ofint n <= m) <=> (n <= ofnat m).
proof. smt(ofintK). qed.

lemma ub_elem_is_ub_big (P : 'a -> bool) F (s : 'a list) (n : nat) :
  (forall x, x \in s => P x => F x <= n) => big P F s <= n.
proof.
elim: s  => [|x s IHs le_s_n] ; first by rewrite big_nil le0n. 
rewrite big_cons /=; case (P x) => [Px|/#].
by rewrite le_maxn le_s_n //= IHs /#.
qed.

lemma ub_big_is_ub_elem (P : 'a -> bool) F (s : 'a list) (n : nat) :
  BigMax.big P F s <= n => (forall x, x \in s => P x => F x <= n).
proof.
elim: s => [|head tail IHs le_s_n]; first by auto.
rewrite BigMax.big_cons in le_s_n.
smt(StNat.Lift.lift2E).
qed.

lemma ler_bigmax (P : 'a -> bool) F (s : 'a list) (n : nat) :
  (forall x, x \in s => P x => F x <= n) <=> big P F s <= n.
proof. smt(ub_big_is_ub_elem ub_elem_is_ub_big). qed.

lemma eq_bigmax x0 (n : nat) (P : 'a -> bool) F (s : 'a list) :
  (x0 \in s) => P x0 => (forall x, x \in s => P x => F x = n) => big P F s = n.
proof.
move => x0_s Px0 Hs; rewrite -big_filter; pose s' := filter P s.
have [] {x0_s Px0 Hs} : x0 \in s' /\ forall x, x \in s' => F x = n.
  smt(mem_filter).
case s' => {s} // x s _; elim: s => [|y s IHs Hs]; first by rewrite big_seq1 /#.
rewrite (eq_big_perm _ _ _ (y :: x :: s)) 1?perm_consCA ?perm_eq_refl.
rewrite big_cons {1}/predT /= Hs // IHs; smt(maxnn).
qed.
