require import AllCore IntDiv CoreMap List.
require import Montgomery.
from Jasmin require import JModel.

(* TODO consider factor out some of these into generic Easycrypyt utils *)

op dilithium_modulo = 8380417.
op dilithium_modulo_left_shift41 = 18428731874223325184.
op dilithium_modulo_inv = 58728449.
op dilithium_modulo_minus_inv = 4236238847.

lemma dilithium_mod_inv_correct:
    dilithium_modulo_inv * dilithium_modulo %% (2 ^ 32) = 1.
proof.
    trivial.
qed.

lemma dilithium_mod_minus_inv_correct:
    dilithium_modulo_minus_inv = (-dilithium_modulo_inv) %% (2 ^ 32).
proof.
    trivial.
qed.
  
  
op montgomery = fun (x : int) => (2 ^ 32 * x) %% dilithium_modulo.

op montgomery_redc_m = fun (a' : int) => (-a' * dilithium_modulo_inv) %% (2 ^ 32).

lemma montgomery_redc_m_lower_bounded:
    forall x, 0 <= montgomery_redc_m x.
proof.
    (* One of these days I'll stop abusing smt... *)
    smt.
qed.

lemma montgomery_redc_m_upper_bounded:
    forall x, montgomery_redc_m x < 2 ^ 32.
proof.
    (* One of these days I'll stop abusing smt... *)
    smt.
qed.

op montgomery_redc_t = fun (a' : int) =>
    let m = montgomery_redc_m(a') in
    (a' + m * dilithium_modulo) %/ (2 ^ 32).

lemma montgomery_redc_t_lower_bounded:
    forall x, 0 <= x < dilithium_modulo => 0 <= montgomery_redc_t x.
proof.
    move => x.
    case.
    move => x_lower x_upper.
    rewrite /montgomery_redc_t.
    simplify.
    (* Ayyy more abusing of smt... *)
    smt.
qed.
    
lemma montgomery_redc_t_upper_bounded:
    forall x, 0 <= x < dilithium_modulo => montgomery_redc_t x < 2 ^ 64.
proof.
    move => x.
    case.
    move => x_lower x_upper.
    rewrite /montgomery_redc_t.
    simplify.
    (* Ayyy more abusing of smt... *)
    smt.
qed.

op montgomery_redc = fun (a' : int) => 
    let m = montgomery_redc_m(a') in
    let t = montgomery_redc_t(a') in
    if t < dilithium_modulo then t else t - dilithium_modulo.

lemma W64_AND_mod32 x:
    (W64.of_int x) `&` (W64.of_int 4294967295) = W64.of_int (x %% 4294967296).
proof.
    have twoTo32: 4294967295 = 2 ^ 32 - 1 by trivial.
    rewrite twoTo32.
    rewrite and_mod.
    trivial.
    rewrite of_uintK.
    rewrite modz_dvd.
    simplify.
    auto.
    simplify.
    trivial.
qed.

lemma montgomery_redc_impl_correct:
    forall x_, 0 <= x_ < dilithium_modulo =>
    hoare[M.montgomery_REDC : x = W64.of_int x_ ==> res = W64.of_int (montgomery_redc x_)].
proof.
    move => x_.
    case.
    move => x_lower_bound x_upper_bound.
    proc.
    seq 4 : (x = (of_int x_) % W64 /\ m = W64.of_int (montgomery_redc_m x_)).
    sp.
    skip.
    rewrite andbC.
    move => &hr.
    case.
    move => xhr_def mhr_def.
    rewrite xhr_def in mhr_def.
    rewrite W64_AND_mod32 in mhr_def.
    rewrite pmod_small in mhr_def.
    split.
    apply x_lower_bound.
    move => unused.
    have mod_lt_2to32: dilithium_modulo < 4294967296 by trivial.
    (* Using smt since I somehow can't get transitivity to work... *)
    (* datatypes/Int.ec *)
    (* 47 axiom nosmt ltz_trans : forall y x z, x < y => y < z => x < z. *)
    smt.
    split.
    apply xhr_def.
    rewrite W64.of_intM' in mhr_def.
    rewrite - /dilithium_modulo_minus_inv in mhr_def.
    rewrite dilithium_mod_minus_inv_correct in mhr_def.
    rewrite W64_AND_mod32 in mhr_def.
    rewrite /montgomery_redc_m.
    rewrite modzMmr in mhr_def.
    (* Minus signs and stuff... *)
    smt.
    seq 3 : (m = W64.of_int (montgomery_redc_t x_)).
    wp.
    skip.
    move => &hr.
    case.
    move => xdef mdef.
    rewrite xdef.
    rewrite mdef.
    rewrite /(`>>`).
    simplify.
    rewrite /montgomery_redc_t.
    simplify.
    rewrite shrDP.
    trivial.
    have no_overflow : montgomery_redc_m x_ * 8380417 + x_ < W64.modulus.
    (* I still don't know how to prove inequalities... *)
    smt.
    rewrite pmod_small.
    split.
    (* Inequality... *)
    (* At a certain point I just get tilted and want to steamroll everything with smt. :( *)
    (* Hey, if it works, it works... *)
    smt.
    move => unused.
    assumption.
    simplify.
    rewrite /dilithium_modulo.
    rewrite addrC.
    reflexivity.
    rewrite /montgomery_redc.
    simplify.
    if.
    wp.
    skip.
    move => &hr.
    case.
    move => tdef.
    rewrite tdef.
    move => t_bound.
    rewrite ule_of_int in t_bound.
    rewrite pmod_small in t_bound.
    trivial.
    rewrite pmod_small in t_bound.
    split.
    rewrite montgomery_redc_t_lower_bounded.
    split.
    rewrite x_lower_bound.
    move => unused.
    rewrite x_upper_bound.
    move => unused'.
    rewrite montgomery_redc_t_upper_bounded.
    split.
    rewrite x_lower_bound.
    move => unused''.
    rewrite x_upper_bound.
    (* No idea how to deal with "if" using ambient logic. *)
    (* More smt it is. *)
    smt.
    skip.
    move => &hr.
    case.
    move => tdef.
    rewrite tdef.
    rewrite uleNgt.
    simplify.
    rewrite ult_of_int.

    move => t_bound.
    rewrite pmod_small in t_bound.
    split.
    rewrite montgomery_redc_t_lower_bounded.
    split.
    rewrite x_lower_bound.
    move => unused.
    rewrite x_upper_bound.
    move => unused'.
    rewrite montgomery_redc_t_upper_bounded.
    split.
    rewrite x_lower_bound.
    move => unused.
    rewrite x_upper_bound.
    (* More "if" in ambient logic. *)
    (* smt time *)
    smt.
qed.

lemma montgomery_correct_div_t:
    forall a', 0 <= a' < dilithium_modulo =>
    montgomery_redc_t(a') * (2 ^ 32) = a' + montgomery_redc_m(a') * dilithium_modulo.
proof.
    move => a' a'_range.
    have r_divides_mN: (a' + montgomery_redc_m(a') * dilithium_modulo) %% 2 ^ 32 = 0.
        rewrite /montgomery_redc_m.
        rewrite - modzDmr.
        rewrite modzMml.

        have move_a':
            (- a' * dilithium_modulo_inv) * dilithium_modulo =
            dilithium_modulo_inv * dilithium_modulo * (-a').
            (* I really didn't want to hit associativity with smt... *)
            smt.
        rewrite move_a'.
        rewrite - modzMml .
        rewrite dilithium_mod_inv_correct.
        apply modzDmr.
    rewrite /montgomery_redc_t.
    simplify.
    rewrite divzE.
    rewrite r_divides_mN.
    simplify.
done.





lemma montgomery_redc_is_left_inv:
    forall x, 0 <= x < 2 ^ 32 => montgomery_redc(montgomery(x)) = x.
proof.
    move => x x_range.
    





