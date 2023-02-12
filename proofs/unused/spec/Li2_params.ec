require import AllCore IntDiv List.
require import PolyReduce.
require ZModP Matrix BitWord.

clone import BitWord as Byte with op n = 8.
(* -- TODO proof *. -- *)

op Li2_q : int = 8380417.
op Li2_d : int = 13.
op Li2_tau : int.
op Li2_gamma1 : int.
op Li2_gamma2 : int.
op Li2_k : int.
op Li2_l : int.
op Li2_eta : int.
op Li2_beta : int = Li2_tau * Li2_eta.
op Li2_omega : int.
op Li2_n : int = 256.
axiom Li2_matrix_size : 4 <= Li2_l <= Li2_k.

clone import PolyReduceZp as Li2_PolyReduceZp with
  op p = Li2_q,
  op n = Li2_n.
(* -- TODO proof *. -- *)

import Zp ZModpRing.

type byte = Byte.word.

clone import Matrix as Li2_Matrix with type ZR.t = polyXnD1.
(* -- TODO proof *. -- *)

type pk_t = byte list * vector.
type sk_t = byte list * byte list * byte list * vector * vector * vector.
type sig_t = byte list * vector * vector.

(** NTT stuff **)

clone import Word as NTT_Domain with
  op n = Li2_n,
  type Alphabet.t = Zp.
(* -- TODO proof *. -- *)
type NTT_t = NTT_Domain.word.

op primitive_root = inzmod 1753.

(* We'll worry about fast, butterflies-based implementations later *)

op ntt (p : polyXnD1) : NTT_t =
  offun (fun i => pevalX p (exp primitive_root (2 * i - 1))).

op invntt : NTT_t -> polyXnD1.
axiom invntt_correct :
  cancel ntt invntt /\ cancel invntt ntt.
