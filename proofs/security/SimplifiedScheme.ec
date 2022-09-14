require import AllCore Distr List DistrExtras.
require DigitalSignaturesRO.
require NonSquareMatrix.
require import PolyReduce.
require import IntDiv.
require ZqRounding.
require ZModFieldExtras.

type M.

(* Dilithium-specific parameters *)

(* secret key range.
 * Typically "eta" but that's a reserved keyword in EC. *)
op e : int.

(* Rounding stuff *)
op gamma1 : int.
op gamma2 : int.
(* beta in spec.
 * beta is again a reserved keyword in EC. *)
op b : int.

(* challenge weight *)
op tau : int.

(* upper bound on number of itertions. *)
op kappa : int.

(* Modulo *)
op q : {int | prime q} as prime_q.

(* Poly degrees *)
op n : {int | 0 < n} as gt0_n.

(* matrix dimensions *)
op k : {int | 0 < k} as gt0_k.
op l : {int | 0 < l} as gt0_l.

clone import ZModFieldExtras as ZModQ with
  op p <= q
proof prime_p by exact prime_q.

clone import PolyReduceZp as PolyReduceZq with
  op p <= q,
  op n <= n,
  type Zp <= ZModQ.zmod,
  theory Zp <= ZModQ
proof ge2_p, gt0_n.
realize ge2_p by smt(prime_q gt1_prime).
realize gt0_n by exact gt0_n.

clone import NonSquareMatrix as PolyMatrix with
  theory ZR <= PolyReduceZq.ComRing,
  op in_size <= l,
  op out_size <= k
proof ge0_in_size by smt(gt0_l),
      ge0_out_size by smt(gt0_k).

import VecOut.
import VecOut.ZModule.
import VecIn.

clone import ZqRounding as Round with
  op q <= q,
  op n <= n,
  op l <= l,
  op k <= k,
  theory ZModQ <= ZModQ,
  theory PolyReduceZq <= PolyReduceZq,
  theory PolyMatrix <= PolyMatrix
proof *.
realize prime_q by exact prime_q.
realize gt0_n by exact gt0_n.
realize gt0_k by exact gt0_k.
realize gt0_l by exact gt0_l.
(* TODO see if anything else is provable *)

(* This `vec_in` and `vec_out` business is such a mess *)
type vecl = vec_in.
type veck = vec_out.

type challenge_t = R.

type SK = matrix * vecl * veck.
type PK = matrix * veck.
type commit_t = int_polyvec.
type response_t = vecl.

op dC : challenge_t distr = dcond dpolyXnD1 (fun p => poly_weight p = tau).

(* Just storing `y` should be good here. *)
type pstate_t = vecl.

(* Unsure if this is intended usage;
 * can't recall from the meeting the other day *)
require FSabort.
clone import FSabort as OpFSA with
  type ID.PK <= PK,
  type ID.SK <= SK,
  type ID.W <= commit_t,
  type ID.C <= challenge_t,
  type ID.Z <= response_t,
  type ID.Pstate <= pstate_t,
  type M <= M,
  op dC <= dC.
(* TODO proof *. *)

(* -- Procedure-based -- *)

op recover (pk : PK) (c : challenge_t) (z : response_t) : commit_t =
  let (mA, t) = pk in
  polyveck_highbits (mA *^ z - c ** t) (2 * gamma2).

clone import CommRecov with
  op recover <= recover,
  op kappa <= kappa.
(* TODO instantiate a couple more things and prove axioms
 * TODO at least `recover` has to be defined for things to be provable *)
import DSS.

(* TODO... should be straightforward to implement.
 * also TODO move this somewhere else.
 *)
op int_poly_max : int_poly -> int.
op int_polyvec_max : int_polyvec -> int.

module (SimplifiedDilithium : SchemeRO)(H: Hash) = {
  proc keygen() : PK * SK = {
    var pk, sk;
    var mA, s1, s2;
    mA <$ dmatrix dpolyXnD1;
    s1 <$ VecIn.dvector (dpolyX (dball_zp e));
    s2 <$ VecOut.dvector (dpolyX (dball_zp e));
    pk <- (mA, mA *^ s1 + s2);
    sk <- (mA, s1, s2);
    return (pk, sk);
  }

  proc sign(sk: SK, m: M) : Sig = {
    var z : vecl option;
    var c : R;
    var ctr : int;
    var y, w, w1;
    var mA, s1, s2;
    (* silences unused variable warning *)
    c <- witness;

    (mA, s1, s2) <- sk;
    ctr <- 0;
    z <- None;
    while(ctr < kappa /\ z = None) {
      y <$ VecIn.dvector (dpolyX (dball_zp (gamma1 - 1)));
      w <- mA *^ y;
      w1 <- polyveck_highbits w (2 * gamma2);
      c <@ H.get((w1, m));
      z <- Some (y + c ** s1);
      if(gamma1 - b <= polyvecl_max (oget z) \/
         gamma2 - b <= int_polyvec_max (polyveck_lowbits (mA *^ y - c ** s2) (2 * gamma2))) {
        z <- None;
      }
      ctr <- ctr + 1;
    }
    return if z = None then None else Some (c, oget z);
  }

  proc verify(pk: PK, m : M, sig : Sig) = {
    var w, c, z, c';
    var mA, t1;
    var good;
    (mA, t1) <- pk;
    good <- (sig = None);
    (c, z) <- oget sig;
    w <- polyveck_highbits (mA *^ z - c ** t1) (2 * gamma2);
    c' <@ H.get((w, m));
    return good /\ polyvecl_max z < gamma1 - b /\ c = c';
  }
}.

(* -- Operator-based -- *)

op keygen : (PK * SK) distr =
  dlet (dmatrix dpolyXnD1) (fun mA =>
  dlet (VecIn.dvector (dpolyX (dball_zp e))) (fun s1 =>
  dlet (VecOut.dvector (dpolyX (dball_zp e))) (fun s2 =>
  let pk = (mA, mA *^ s1 + s2) in
  let sk = (mA, s1, s2) in
  dunit (pk, sk)))).

op commit (sk : SK) : (commit_t * pstate_t) distr =
  let (mA, s1, s2) = sk in
  dmap (VecIn.dvector (dpolyX (dball_zp (gamma1 - 1)))) (fun y =>
  let w1 = polyveck_highbits (mA *^ y) (2 * gamma2) in
  (w1, y)).

op respond (sk : SK) (c : challenge_t) (y: pstate_t) : response_t option =
  let (mA, s1, s2) = sk in
  let z = y + c ** s1 in
  if gamma1 - b <= polyvecl_max z \/
     gamma2 - b <= int_polyvec_max (polyveck_lowbits (mA *^ y - c ** s2) (2 * gamma2)) then
    None else
    Some z.

clone import OpBased with
  op keygen <= keygen,
  op commit <= commit,
  op response <= respond.
(* TODO proof *. *)

(* -- proofs -- *)

module OpBasedSig = IDS_Sig(OpBased.P, OpBased.V).

section OpBasedCorrectness.

declare module H <: Hash {-OpBased.P}.

equiv keygen_opbased_correct :
  OpBasedSig(H).keygen ~ SimplifiedDilithium(H).keygen :
  true ==> ={res}.
proof.
proc; inline *.
rnd: *0 *0; skip => />.
(* terrifying *)
admitted.

equiv sign_opbased_correct :
  OpBasedSig(H).sign ~ SimplifiedDilithium(H).sign :
  ={arg} ==> ={res}.
proof.
proc; inline *.
(* Is it just me or is this not any better than the one before... *)
admitted.

equiv verify_opbased_correct :
  OpBasedSig(H).verify ~ SimplifiedDilithium(H).verify :
  ={arg} ==> ={res}.
proof.
proc; inline *.
(* We'll save this for next time. *)
admitted.

end section OpBasedCorrectness.
