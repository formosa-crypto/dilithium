require import AllCore Distr DBool PROM List.
import Biased.
require import Dexcepted.
require import Dfilter.
require import Real RealSeries.
import SmtMap.
import Biased.

require import DistrExtras.
require Guessing.

type X, Y, Z, M.

op [lossless] dXYZ_acc (m : M) : (X * Y * Z) distr.
op [lossless] dXY_rej (m : M) : (X * Y) distr.
op [lossless uniform] dY : Y distr.
op alpha : real.
op qH, qR : int.

op dXr m = dfst (dXY_rej m).
axiom dX_pmax m :
  p_max (dXr m) <= alpha.

clone import FullRO with
  type in_t <- X,
  type out_t <- Y,
  op dout <- (fun _ => dY)
proof *.

op qh, qr : int.
axiom qh_gt0 : 0 < qh.
axiom qr_gt0 : 0 < qr.

clone import Guessing as RejGuessing with
  type in_t <- M,
  type out_t <- X,
  op d <- fun m => dXr m,
  op qs <- qr,
  op qg <- qh,
  op alpha <- alpha
proof *.
realize d_pmax by apply dX_pmax.
realize qs_gt0 by apply qr_gt0.
realize qg_gt0 by apply qh_gt0.

module type ReprogRejO = {
  proc h(x: X) : Y
  proc reprog_acc(m: M) : X * Y * Z
  proc reprog_rej(m: M) : unit
}.

module type ReprogRejOI = {
  include ReprogRejO
  proc init() : unit
}.

(*
 * ReprogRej: Basic RO games that we plan to reduce to.
 * Adversary can make three possible queries, as discussed on the notes.
 * Only third query (reprog_rej) is different between GameA and GameB.
 *
 * The games are indistinguishable in ROM.
 * I hope same is true in QROM.
 *)
module ReprogRejO0 : ReprogRejOI = {
  proc init() = {}

  proc h(x) = {
    var y;
    y <@ RO.get(x);
    return y;
  }

  proc reprog_acc(m) = {
    var x, y, z;
    (x, y, z) <$ dXYZ_acc m;
    RO.set(x, y);
    return (x, y, z);
  }

  proc reprog_rej(m: M) = { }
}.

module ReprogRejO1 : ReprogRejOI = {
  include var ReprogRejO0 [init, h, reprog_acc]

  proc reprog_rej(m) = {
    var x, y;
    (x, y) <$ dXY_rej m;
    (* reprog *)
    RO.set(x, y);
    (* no return *)
  }
}.

module type AdvReprogRej(O: ReprogRejO) = {
  proc distinguish() : bool
}.

module GReprogRej (O: ReprogRejOI) (Adv: AdvReprogRej) = {
  proc main() = {
    var b;
    O.init();
    b <@ Adv(O).distinguish();
    return b;
  }
}.

module Count (O: ReprogRejO) : ReprogRejO = {
  var countR, countH : int
  (*
  proc init() = {
    countR <- 0;
    countH <- 0;
    O.init();
  }
  *)
  proc reprog_acc(x) = {
    var y;
    y <@ O.reprog_acc(x);
    return y;
  }
  proc h(x) = {
    var y;
    countH <- countH + 1;
    y <@ O.h(x);
    return y;
  }
  proc reprog_rej(x) = {
    var y;
    countR <- countR + 1;
    y <@ O.reprog_rej(x);
    return y;
  }
}.

section.

module ReprogRejO0_rec : ReprogRejOI = {
  include var ReprogRejO0 [reprog_acc]

  var bad : bool
  var rej_lst : X list

  proc init() = {
    bad <- false;
  }

  proc h(x) = {
    var y;
    if(x \in rej_lst)
      bad <- true;
    y <@ RO.get(x);
    return y;
  }

  proc reprog_rej(m: M) = {
    var x, y;
    (x, y) <$ dXY_rej m;
    rej_lst <- x :: rej_lst;
  }
}.

module ReprogRejO1_rec : ReprogRejOI = {
  include var ReprogRejO0_rec[init, h, reprog_acc]

  proc reprog_rej(m) = {
    var x, y;
    (x, y) <$ dXY_rej m;
    (* reprog *)
    RO.set(x, y);
    rej_lst <- x :: rej_lst;
    (* no return *)
  }
}.

declare module A <: AdvReprogRej {-ReprogRejO0_rec, -RO, -Count}.
declare axiom A_ll : (forall (O <: ReprogRejO{-A}),
  islossless O.h =>
  islossless O.reprog_acc =>
  islossless O.reprog_rej =>
  islossless A(O).distinguish).
declare axiom A_bound : forall (O <: ReprogRejO{-A}), 
  hoare [ A(Count(O)).distinguish : Count.countR = 0 /\ Count.countH = 0 ==> 
                                    Count.countR <= qr /\ Count.countH = qh ].

lemma ReprogRejBound &m :
  `| Pr[GReprogRej(ReprogRejO0_rec, A).main() @ &m : res]
   - Pr[GReprogRej(ReprogRejO1_rec, A).main() @ &m : res] |
  <= Pr[GReprogRej(ReprogRejO1_rec, A).main() @ &m : ReprogRejO0_rec.bad].
proof.
byequiv (_: ={glob A, RO.m, ReprogRejO0_rec.bad, ReprogRejO0_rec.rej_lst} ==>
  ={ReprogRejO0_rec.bad} /\ (!ReprogRejO0_rec.bad{1} => ={res})) :
  ReprogRejO0_rec.bad; 2, 3: smt().
proc.
seq 1 1: (#pre /\ !ReprogRejO0_rec.bad{1} /\ !ReprogRejO0_rec.bad{2}).
- inline ReprogRejO0_rec.init; by auto.
call (_: ReprogRejO0_rec.bad,
     ={ReprogRejO0_rec.bad, ReprogRejO0_rec.rej_lst} /\
     (forall x, (!(x \in ReprogRejO0_rec.rej_lst{1}) => RO.m{1}.[x] = RO.m{2}.[x])),
     ={ReprogRejO0_rec.bad}); 1: by apply A_ll.
(* H *)
- proc; inline RO.get; auto => />.
  smt(get_setE get_set_sameE).
- move => *; proc.
  inline RO.get; auto => />.
  smt(dY_ll).
- move => *; proc.
  inline RO.get; auto => />.
  smt(dY_ll).
(* acc *)
- proc. inline RO.set; auto => />.
  smt(get_setE get_set_sameE).
- move => *; proc.
  inline RO.set; auto => />.
  smt(dXYZ_acc_ll).
- move => *; proc.
  inline RO.set; auto => />.
  smt(dXYZ_acc_ll).
(* rej *)
- proc; inline RO.set; auto => />.
  smt(get_setE get_set_sameE).
- move => *; proc; auto => />.
  smt(dXY_rej_ll).
- move => *; proc.
  inline RO.set; auto => />.
  smt(dXY_rej_ll).
(* after call *)
- skip => />; smt().
qed.

end section.
