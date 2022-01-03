require import AllCore List.
require import Li2_params Li2_rounding.

(* entry type and vectors? *)

import Li2_Matrix Li2_Matrix.Matrix.
type entry_t = Li2_ring.qT.

import PolyModQ.
import Li2_field.

module Poly_impl = {
  proc power2round(p : entry_t, d : int) : entry_t * entry_t = {
    var deg;
    var result1, result0;
    var val, val1, val0;

    result1 <- poly0;
    result0 <- poly0;
    deg <- 0;
    while(deg < Li2_n) {
      val <- asint ((Li2_ring.repr p).[deg]);
      (val1, val0) <@ Rounding_impl.power2round(val, d);
      result1 <- result1 + polyZ (inzmod val1) (polyXn deg);
      result0 <- result0 + polyZ (inzmod val0) (polyXn deg);
      deg <- deg + 1;
    }

    return (Li2_ring.pi result1, Li2_ring.pi result0);
  }
}.

module Polyvec_impl = {
  proc power2round_veck(v : vector, d : int) : vector * vector = {
    var i;
    var result1, result0;
    var entry, entry1, entry0;

    result1 <- fun _ => Li2_ring.pi poly0;
    result0 <- fun _ => Li2_ring.pi poly0;
    i <- 0;
    while(i < Li2_n) {
      entry <- v.[i];
      (entry1, entry0) <@ Poly_impl.power2round(entry, d);
      result1 <- fun x => if x = i then entry1 else result1 x;
      result0 <- fun x => if x = i then entry0 else result0 x;
    }
    return (offunv result1, offunv result0);
  }
}.
