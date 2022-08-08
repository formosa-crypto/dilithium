require import AllCore Distr DBool PROM List.
import Biased.

require import Dexcepted.
require import Dfilter.
require import Real RealSeries.

type X, Y, Z, M.

op [lossless] dXYZ_acc (m : M) : (X * Y * Z) distr.
op [lossless] dXY_rej (m : M) : (X * Y) distr.
op [lossless uniform] dY : Y distr.

(* TODO min-entropy axioms... *)

clone import FullRO with
  type in_t <- X,
  type out_t <- Y,
  op dout <- (fun _ => dY).

module type ReprogRejO = {
  proc h(x: X) : Y
  proc reprog_acc(m: M) : X * Y * Z
  proc reprog_rej(m: M) : unit
}.

(*
 * ReprogRej: Basic RO games that we plan to reduce to.
 * Adversary can make three possible queries, as discussed on the notes.
 * Only third query (reprog_rej) is different between GameA and GameB.
 *
 * The games are indistinguishable in ROM.
 * I hope same is true in QROM.
 *)
module GReprogRej0 : ReprogRejO = {
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

(* Should this actually be a different module,
 * or should I just let the above take a coin?
 *)
module GReprogRej1 : ReprogRejO = {
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

section.

declare module A <: AdvReprogRej.

axiom test &m :
  Pr[A(GReprogRej0).distinguish() @ &m : res] = 0%r.

end section.
