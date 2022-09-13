require import AllCore.
require DigitalSignaturesRO.
require NonSquareMatrix.
require import PolyReduce.
require import IntDiv.
require ZqRounding.

type M.

op q : {int | prime q} as prime_q.
op n : {int | 0 < n} as gt0_n.

(* matrix dimensions *)
op k : {int | 0 < k} as gt0_k.
op l : {int | 0 < l} as gt0_l.
axiom l_k_le : l <= k.

clone import PolyReduceZp as PolyReduceZq with
  op p <= q,
  op n <= n
proof ge2_p, gt0_n.
realize ge2_p by smt(prime_q gt1_prime).
realize gt0_n by exact gt0_n.

clone import NonSquareMatrix as PolyMatrix with
  theory ZR <= PolyReduceZq.ComRing,
  op in_size <= l,
  op out_size <= k
proof ge0_in_size by smt(gt0_l),
      ge0_out_size by smt(gt0_k).

print vec_in.

clone import ZqRounding as Round with
  op q <= q,
  op n <= n,
  op l <= l,
  op k <= k,
  theory PolyReduceZq <= PolyReduceZq,
  theory PolyMatrix <= PolyMatrix
proof *.
realize prime_q by exact prime_q.
realize gt0_n by exact gt0_n.
realize gt0_k by exact gt0_k.
realize gt0_l by exact gt0_l.
(* TODO Proof whatever applicable *)
(* TODO There's an argument to re-instantiate some theories *)

import Zp.

type vecl = vec_in.
type veck = vec_out.
type challenge_t = R.

type SK = matrix * vecl * veck.
type PK = matrix * veck.
type commit_t = int_polyvec.
type response_t = vecl * bool_polyvec.
type SIG = commit_t * response_t.

clone import DigitalSignaturesRO as DilithiumDS with
  type DS.msg_t <= M,
  type DS.sig_t <= SIG,
  type DS.pk_t <= PK,
  type DS.sk_t <= SK,
  type PRO.in_t <= commit_t * M,
  type PRO.out_t <= challenge_t.

import VecOut.
import VecOut.ZModule.

(* power2round rounding range...? *)
op d : int.

module (SimplifiedDilithium : SchemeRO)(H: Hash) = {
  proc keygen() : PK * SK = {
    var pk, sk;
    var mA, s1, s2;
    mA <$ dmatrix dpolyXnD1;
    s1 <$ VecIn.dvector dpolyXnD1;
    s2 <$ VecOut.dvector dpolyXnD1;
    pk <- (mA, mA *^ s1 + s2);
    sk <- (mA, s1, s2);
    return (pk, sk);
  }

  proc sign(sk: SK, m: M) : SIG = {
    (* Not yet implemented *)
    (* Not necessary for NMA *)
    return witness;
  }

  proc verify(pk: PK, m : M, sig : SIG) = {
    var w, w', c, resp, z, h;
    var mA, t1;
    (mA, t1) <- pk;
    (w, resp) <- sig;
    (z, h) <- resp;
    c <@ H.get((w, m));
    w' <- polyveck_useHint h (mA *^ z - polyCX (inzmod (2 ^ d)) * c ** t1);
    return false;
  }
}.
