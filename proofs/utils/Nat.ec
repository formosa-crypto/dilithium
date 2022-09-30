(* Natural Numbers as a subtype of [int] *)

require import StdOrder.
require Int Subtype.

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
