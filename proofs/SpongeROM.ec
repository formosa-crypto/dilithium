require import AllCore List Li2_params.

type hash_domain_t = [SHAKE128 | SHAKE256].

(* Not sure how compatible is this with existing work... *)
module type SpongeRO = {
  proc reset(domain : hash_domain_t) : unit
  proc absorb(data : byte list) : unit
  proc squeeze(len : int) : byte list
}.
