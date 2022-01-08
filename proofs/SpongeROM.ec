require import AllCore List.

type hash_t = [SHAKE128 | SHAKE256 | IDEAL].

(* Not sure how compatible is this with existing work... *)
module type RO = {
  proc init(t : hash_t) : unit
  proc absorb(data : int list) : unit
  proc squeeze(len : int) : int list
}.
