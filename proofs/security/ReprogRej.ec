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

(*
 * ReprogRej: Basic RO games that we plan to reduce to.
 * Adversary can make three possible queries, as discussed on the notes.
 * Only third query (reprog_rej) is different between GameA and GameB.
 *
 * The games are indistinguishable in ROM.
 * I hope same is true in QROM.
 *)
module GReprogRej0 = {
  var good : bool

  proc init() = {
    good <- true;
  }

  proc h(x) = {
    var y;
    y <@ RO.get(x);
    return y;
  }

  proc reprog_acc(dXYZ_acc : (X * Y * Z) distr) = {
    var x, y, z;
    (x, y, z) <$ dXYZ_acc;
    RO.set(x, y);
    return (x, y, z);
  }

  proc reprog_rej(dXY_rej : (X * Y) distr) = { }
}.

(* Should this actually be a different module,
 * or should I just let the above take a coin?
 *)
module GReprogRej1 = {
  var good : bool

  proc init() = {
    good <- true;
  }

  proc h(x) = {
    var y;
    y <@ RO.get(x);
    return y;
  }

  proc reprog_acc(dXYZ_acc : (X * Y * Z) distr) = {
    var x, y, z;
    (x, y, z) <$ dXYZ_acc;
    RO.set(x, y);
    return (x, y, z);
  }

  proc reprog_rej(dXY_rej : (X * Y) distr) = {
    var x, y;
    (x, y) <$ dXY_rej;
    (* reprog *)
    RO.set(x, y);
    (* no return *)
  }
}.
