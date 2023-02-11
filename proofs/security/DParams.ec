require import AllCore IntDiv.

(* Note: eta and beta are keywords in EC, so we use a trailing _ *)

op q : {int | prime q} as prime_q.       (* modulo *)
op n : {int | 0 < n} as gt0_n.           (* poly degrees *)

op eta_ : {int | 0 < eta_} as gt0_eta.   (* secrect key range *)
op k    : {int | 0 < k} as gt0_k.        (* matrix rows *)
op l    : {int | 0 < l} as gt0_l.        (* matrix cols *)

op gamma1 : int.                         (* commitment range *)
op gamma2 : int.                         (* high- and lowbits rounding range *)

op beta_ : {int | 0 < beta_} as gt0_beta.      (* ??? *)
op tau : { int | 1 <= tau <= n } as tau_bound. (* challenge weight *)

op d : { int | 0 < d } as gt0_d.        (* bits dropped from public key *)

axiom eta_tau_leq_b : eta_ * tau <= beta_.
axiom ub_d : tau * 2 ^ d <= 2 * gamma2.

axiom gamma2_bound  : 2 <= gamma2 <= q %/ 4.
axiom gamma2_div : 2 * gamma2 %| (q - 1).

axiom beta_gamma1_lt : beta_ < gamma1.
axiom beta_gamma2_lt : beta_ < gamma2.
