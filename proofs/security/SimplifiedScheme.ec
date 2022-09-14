require import AllCore Distr.
require DigitalSignaturesRO.
require NonSquareMatrix.
require import PolyReduce.
require import IntDiv.
require ZqRounding.
require ZModFieldExtras.

type M.

op q : {int | prime q} as prime_q.

op n : {int | 0 < n} as gt0_n.

(* matrix dimensions *)
op k : {int | 0 < k} as gt0_k.
op l : {int | 0 < l} as gt0_l.
axiom l_k_le : l <= k.

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
type SIG = (response_t * challenge_t) option.

clone import DigitalSignaturesRO as DilithiumDS with
  type DS.msg_t <= M,
  type DS.sig_t <= SIG,
  type DS.pk_t <= PK,
  type DS.sk_t <= SK,
  type PRO.in_t <= commit_t * M,
  type PRO.out_t <= challenge_t.

(* Dilithium-specific parameters *)
(* power2round rounding range *)
op d : int.
(* secret key range.
 * Typically "eta" but that's a reserved keyword in EC. *)
op e : int.

(* Rounding stuff *)
op gamma1 : int.
op gamma2 : int.
(* beta in spec.
 * beta is reserved keyword in EC. *)
op b : int.

(* upper bound on number of itertions. *)
op kappa : int.

require import List.

(* TODO... should be straightforward.
 * also TODO move this to ZqRounding theory.
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

  proc sign(sk: SK, m: M) : SIG = {
    var z : vecl option;
    var c : R;
    var ctr : int;
    var y, w, w1;
    var mA, s1, s2;
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
    return witness;
  }

  proc verify(pk: PK, m : M, sig : SIG) = {
    var w, c, z, c';
    var mA, t1;
    var good;
    (mA, t1) <- pk;
    good <- sig = None;
    (z, c) <- oget sig;
    w <- polyveck_highbits (mA *^ z - c ** t1) (2 * gamma2);
    c' <@ H.get((w, m));
    return good /\ polyvecl_max z < gamma1 - b /\ c = c';
  }
}.

(* Just storing `y` should be good here. *)
type pstate_t = vecl.

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

(* TODO dC *)

(* op respond (sk : SK) : *)
