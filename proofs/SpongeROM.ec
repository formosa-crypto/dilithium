require import AllCore List Li2_params.

type hash_t = [SHAKE128 | SHAKE256 | IDEAL].

(* Not sure how compatible is this with existing work... *)
module type RO = {
  proc init(t : hash_t) : unit
  proc absorb(data : byte list) : unit
  proc squeeze(len : int) : byte list
}.
