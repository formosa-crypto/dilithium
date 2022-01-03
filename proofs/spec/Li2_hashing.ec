require import AllCore.
require import Li2_params.
require import List.
require import IntDiv.

type hash_t = [SHAKE128 | SHAKE256].

(* Not sure how compatible is this with existing work... *)
module type RO = {
  proc init(t : hash_t) : unit
  proc absorb(data : int list) : unit
  proc squeeze(len : int) : int list
}.

import PolyModQ.
import Li2_field.
import Li2_Matrix.
import Li2_Matrix.Matrix.
type entry_t = Li2_ring.qT.

module Expand_impl(H : RO) = {
  proc expandA_entry(rho : int list, i j : int) : entry_t = {
    var deg : int;
    var p : poly;
    var ext;
    var val;

    H.init(SHAKE128);
    H.absorb(rho);
    H.absorb([j; i]);
    deg <- 0;
    p <- poly0;
    while(deg < Li2_n) {
      ext <@ H.squeeze(3);
      val <- (nth 0 ext 0) + (nth 0 ext 1) * (2 ^ 8) + ((nth 0 ext 2) %% 128) * (2 ^ 16);
      if(val < Li2_q) {
        p <- p + polyZ (inzmod val) (polyXn deg);
        deg <- deg + 1;
      }
    }
    return Li2_ring.pi p;
  }

  proc expandA(rho : int list) : matrix = {
    var result : (int -> int -> entry_t);
    var i, j : int;
    var entry;
    result <- fun _ _ => Li2_ring.pi poly0;
    i <- 0;
    j <- 0;
    while(i < Li2_k) {
      while(j < Li2_l) {
        entry <@ expandA_entry(rho, i, j);
        result <- fun r c => if r = i && c = j then entry else result r c;
        j <- j + 1;
      }
      i <- i + 1;
    }
    return offunm result;
  }

  proc expandS_entry(rho' : int list, i : int) : entry_t = {
    var deg : int;
    var p : poly;
    var ext;
    var val;

    p <- poly0;

    H.init(SHAKE256);
    H.absorb(rho');
    H.absorb([i; 0]);
    deg <- 0;
    while(deg < Li2_n) {
      ext <@ H.squeeze(1);
      val <- (nth 0 ext 0) %% 16;
      if(val <= 2 * Li2_eta) {
        p <- p + polyZ (inzmod val) (polyXn deg);
        deg <- deg + 1;
      }
      if(deg < Li2_n) {
        val <- (nth 0 ext 0) %/ 16;
        if(val <= 2 * Li2_eta) {
          p <- p + polyZ (inzmod val) (polyXn deg);
          deg <- deg + 1;
        }
      }
    }
    return Li2_ring.pi poly0;
  }

  proc expandS(rho' : int list) : vector * vector = {
    var s1, s2 : (int -> entry_t);
    var i : int;
    var entry;

    s1 <- fun _ => Li2_ring.pi poly0;
    i <- 0;
    while(i < Li2_l) {
      entry <@ expandS_entry(rho', i);
      s1 <- fun x => if x = i then entry else s1 x;
      i <- i + 1;
    }

    s2 <- fun _ => Li2_ring.pi poly0;
    i <- 0;
    while(i < Li2_k) {
      entry <@ expandS_entry(rho', Li2_l + i);
      s1 <- fun x => if x = i then entry else s1 x;
      i <- i + 1;
    }

    return (offunv s1, offunv s2);
  }
}.
