require import AllCore Distr List IntDiv StdOrder.
require import DistrExtras.
import RealOrder Finite.
require DParams ConcreteDRing.

require DRing DVect MLWE SelfTargetMSIS.
require SimplifiedScheme.

(** Abstract Version using DRing *)

abstract theory AbstractDilithium.

(* We assume some parameter set; this defines:
   n, q, k, l, eta, gamma1, gamma2, beta, tau, and d. *)
clone import DParams as Params.

(* Abstract data structure for Rq; this defines:         *)
(* An abstract type Rq representing ℤq[X]/(X^n + 1)      *)
(* highBits and lowBits operations on Rq                 *)
clone import DRing as DR with
  op n <= n,
  op q <= q
proof prime_q by exact prime_q
proof gt0_n by exact gt0_n.

(* Generate a theory of matrices/vectors over Rq           *)
(* This includes vector versions of highBits and lowBits   *)
(* NOTE: We prove everything except the subType axioms     *)
(*       The subtype axioms are consistent but not provabe *) 
clone import DVect as DV with 
  theory DR <= DR,
  op HL.alpha <- 2*gamma2,
  op HL.d     <- d
proof 
  HL.ge2_alpha, 
  HL.alpha_halfq_le, 
  HL.even_alpha, 
  HL.alpha_almost_divides_q.
realize HL.ge2_alpha by smt(gamma2_bound).
realize HL.even_alpha by smt().
realize HL.alpha_halfq_le by smt(gamma2_bound).
realize HL.alpha_almost_divides_q by apply gamma2_div.

import DV.MatRq. (* Matrices and Vectors over Rq *)
import DV.HL.    (* highBitsV and lowBitsV with HL.alpha = 2 * gamma2 and HL.d = d *)

type M.                                       (* The type of messages to be signed *)
type SK = matrix * vector * vector * vector.  (* The type of secret keys           *)
type PK = matrix * high2 list.                (* The type of public keys           *)
type commit_t = high list.                    (* The type of commitments (for IDS) *)
type challenge_t = Rq.                        (* The type of challenges  (for IDS) *)
type response_t = vector * hint_t list.       (* The type of responses   (for IDS) *)
type Sig = challenge_t * response_t.          (* The type of signatues (of scheme) *)

(* Abstract module type for hash functions or random oracles *)
module type Hash  = {
  proc get(x : high list * M) : challenge_t
}.

(*************************************)
(**** The Dilithium Scheme    ********)
(*************************************)

(* We define the Dilithium scheme parametric in the hash function/oracle *)
(* TOTHINK: There's `Logic.eta_` that conflicts with `DParams.eta_`. *)
module Dilithium (H: Hash) = {
  proc keygen() : PK * SK = {
    var pk, sk;
    var mA, s1, s2,t, t1,t0;
    mA <$ dmatrix dRq k l;
    s1 <$ dvector (dRq_ Params.eta_) l;
    s2 <$ dvector (dRq_ Params.eta_) k;
    t  <- mA *^ s1 + s2;
    t1 <- base2highbitsV t;
    t0 <- base2lowbitsV t;
    pk <- (mA, t1);
    sk <- (mA, s1, s2, t0);
    return (pk, sk);
  }

  proc sign(sk: SK, m: M) : Sig = {
    var z : vector;
    var h : hint_t list;
    var response : response_t option;
    var c : R <- witness;
    var ctr : int;
    var y, w, w1;
    var mA, s1, s2;
    var t0;

    (mA, s1, s2, t0) <- sk;

    response <- None;
    while(response = None) {
      y <$ dvector (dRq_ (gamma1 - 1)) l;
      w <- mA *^ y;
      w1 <- highBitsV w;
      c <@ H.get((w1, m));
      z <- y + c ** s1;
      if(inf_normv z < gamma1 - beta_ /\
         inf_normv (lowBitsV (mA *^ y - c ** s2)) < gamma2 - beta_) {
        h <- makeHintV (- c ** t0) (w - c ** s2 + c ** t0);
        response <- Some(z,h);
      }
    }
    return (c, oget response);
  }

  proc verify(pk: PK, m : M, sig : Sig) = {
    var w1, c;
    var response;
    var z, h;
    var c';
    var mA, t1;
    (mA, t1) <- pk;

    (c, response) <- sig;
    (z, h) <- response;
    w1 <- useHintV h (mA *^ z - c ** base2shiftV t1);
    c' <@ H.get((w1, m));
    return size z = l /\ size h = k /\ inf_normv z < gamma1 - beta_ /\ c = c';
  }
}.

(*************************************)
(**** Parameters of the proof ********)
(*************************************)

(*** Query Bounds ***)
const qS : { int | 0 <= qS } as qS_ge0. (* number of queries to "sign"  *)
const qH : { int | 0 <= qH } as qH_ge0. (* number of queries to "H.get" *)

(*** Entropy Bounds ***) 

(** We require a check on the matrix component of public and secrect
key that ensures:

- sufficiently high (expected) commitment entropy
- sufficiently high probability that respond succeeds *)

(* Abbreviations for the way A, y, and z are sampled *)
op dA = dmatrix dRq k l.
op dy = dvector (dRq_ (gamma1 - 1)) l.
op dz = dvector (dRq_ (gamma1 - beta_ - 1)) l.

(* The check on the matrix component of the keys                           *)
(* This is just predicate used in the proofs, we never compute with it     *)
op check_mx : matrix -> bool.

(* For convenience, we assume that the check also checks matrix dimensions *)
axiom check_valid A : check_mx A => A \in dA.

(* Also for convenience we assume some (fixed) A0 passing the check        *)
op A0 : { matrix | check_mx A0 } as A0P.

(* upper bound on the mass of the matrices not passing check               *)
const delta_ : { real | 0%r <= delta_ }  as delta_gt0.
axiom check_mx_most : mu dA (predC check_mx) <= delta_.

(* upper bound on the expected probability mass 
   of the most likely commitment for a good key  *)
const eps_comm  : { real | 0%r < eps_comm } as eps_comm_gt0.

axiom check_mx_entropy : 
  E (dcond dA check_mx) (fun mA => 
    p_max (dmap dy (fun y => highBitsV (mA *^ y)))) <= eps_comm.

(* bound on the probability that he low-bis check in the Sim fails *)
const eps_low : { real | eps_low < 1%r } as eps_low_lt1.

axiom bound_low c (t : vector) (mA : matrix) :
  c \in dC tau => t \in dvector dRq k => check_mx mA =>
  mu dz (fun z => gamma2 - beta_ <= inf_normv (lowBitsV (mA *^ z - c ** t)) ) <= eps_low. 


(*************************************)
(**** The Security Proof      ********)
(*************************************)

(* Here we mostry instantiate the security proof for the simplified scheme. 
   The onyl part we prove here is that security of the scheme above reduces
   to security of the simplified scheme, where the public key is (A,t) and
   the private key is (A,s1,s2). *)

(* Instantiate the definitions for digital signature security in the ROM *)
clone import DigitalSignaturesRO as DSS with 
type DS.pk_t <- PK,
type DS.sk_t <- SK,
type DS.msg_t <- M,
type DS.sig_t <- Sig,
type PRO.in_t <= commit_t*M,
type PRO.out_t <= challenge_t, 
op   PRO.dout <= fun _ => dC tau,
op   EFCMA.q_efcma <= qS
proof* by smt(qS_ge0).
import DSS.DS.Stateless.

(* The digital signature definitions also provide the ROM *)
module H = DSS.PRO.RO.

(* Pnnstantiate security proof of the simplified scheme *)
clone SimplifiedScheme as SD with 
  theory DR <- DR,
  theory DV <- DV,
  type M <- M,

  theory Params <- Params,

  op check_mx <- check_mx,
  op eps_comm <- eps_comm,
  op eps_check <- delta_,
  op eps_low <- eps_low,
  axiom eps_comm_gt0 <- eps_comm_gt0,
  axiom eps_check_gt0 <- delta_gt0,
  axiom check_mx_entropy <- check_mx_entropy,
  axiom bound_low <- bound_low,
  axiom eps_low_lt1 <- eps_low_lt1,
  axiom check_mx_most <- check_mx_most,
  axiom check_valid <- check_valid,

  op A0 <- A0,
  axiom A0P <- A0P,

  op qS <- qS,
  op qH <- qH,
  axiom qS_ge0 <- qS_ge0,
  axiom qH_ge0 <- qH_ge0
proof* by smt(gt0_eta gt0_k gt0_l gamma2_bound gamma2_div gt0_beta beta_gamma1_lt 
              beta_gamma2_lt gt0_d tau_bound eta_tau_leq_b ub_d).

(* Key types of the simplified scheme *)
type SK' = matrix * vector * vector.
type PK' = matrix * vector.

(* reduction to simplified scheme: drop t0 *)
module (RedS (A : Adv_EFCMA_RO) : SD.FSaCR.DSS.Adv_EFCMA_RO)
       (H : Hash) (O : SOracle_CMA) = { 
 proc forge (pk: PK') = { 
    var r,mA,t,t1;
    (mA,t) <- pk;
    t1 <- base2highbitsV t;
    r <@ A(H,O).forge(mA,t1);
    return r;
  }
}.

(* The clone of the SimplifiedScheme theory above also instantiate the
   MLWE and SelfTargetMSIS games with the correct parameters and
   defines the reductions to MLWE and SelfTargetMSIS. Both are part of
   the final statement. Here we just introduce short names for
   them: *)

(* Left and Right Game of the MLWE assumption *)
module MLWE_L (A : SD.RqMLWE.Adversary) = SD.RqMLWE.GameL(A).
module MLWE_R (A : SD.RqMLWE.Adversary) = SD.RqMLWE.GameR(A).

(* The SelfTargetMSIS Game *)
module SelfTargetMSIS (A : SD.RqStMSIS.Adversary) = SD.RqStMSIS.Game(A).

(* Reduction to MLWE *)
module RedMLWE (A : Adv_EFCMA_RO) = 
  SD.RedMLWE(SD.RedCR(SD.CMAtoKOA.RedKOA(SD.CG.RedFSaG(RedS(A)), SD.HVZK_Sim_Inst)), 
  SD.FSaCR.DSS.PRO.RO).

(* Reduction to SelfTargetMSIS *)
module RedStMSIS (A : Adv_EFCMA_RO) = 
  SD.RedMSIS(SD.RedCR(SD.CMAtoKOA.RedKOA(SD.CG.RedFSaG(RedS(A)), SD.HVZK_Sim_Inst))).

section PROOF.

(* We assume some adversary A whose memory is disjoint from the random
oracle H, the signing oracle of che EUF_CMA game, and all the
auxiliary constructions used in the proof. *)

declare module A <: Adv_EFCMA_RO{
  -H, -O_CMA_Default,
  -SD.H, 
  -SD.G, 
  -SD.OpBasedSig, 
  -SD.CMAtoKOA.ORedKOA, 
  -SD.CMAtoKOA.CountS, 
  -SD.CMAtoKOA.CountH, 
  -SD.CountS, 
  -SD.CountH, 
  -SD.O_CMA_Default_G, 
  -SD.RO_G, 
  -SD.OpBasedSigG,
  -RedS,
  -SD.FSaCR.DSS.DS.Stateless.O_CMA_Default
}.

(* A's attemts at forging a signature terminate, 
  provided the oracles it is provided with are terminating *)
declare axiom A_ll (SO' <: SOracle_CMA{-A}) (H' <: Hash{-A} ) : 
  islossless SO'.sign => islossless H'.get => islossless A(H', SO').forge.

(* A makes no more than qH random oracle (i.e., hash) queries 
  and no more than qS many signing queries *)
(* NOTE: we can use the counting wrappers from SD, because the oracles
have the same signature. Only the key format is changed *)
declare axiom A_bound 
  (H' <: Hash{-SD.CountS, -SD.CountH, -A} )
  (SO' <: SOracle_CMA{-SD.CountS, -SD.CountH, -A} ) :
  hoare[ A(SD.CountH(H'), SD.CountS(SO')).forge :
      SD.CountH.qh = 0 /\ SD.CountS.qs = 0 ==>
      SD.CountH.qh <= qH /\ SD.CountS.qs <= qS].


(************************************************)
(*         M A I N       T H E R O E M          *)
(************************************************)

op p0 = (size (to_seq (support dz)))%r / (size (to_seq (support dy)))%r.
op p_rej : real = (p0 * eps_low) + (1.0 - p0).

lemma Dilithium_secure &m :
 Pr[EF_CMA_RO(Dilithium, A, H, O_CMA_Default).main() @ &m : res] <=
     `|Pr[MLWE_L(RedMLWE(A)).main() @ &m : res] -
       Pr[MLWE_R(RedMLWE(A)).main() @ &m : res]| +
     Pr[SelfTargetMSIS(RedStMSIS(A), SD.RqStMSIS.PRO.RO).main () @ &m : res] +
     (2%r * qS%r * (qH + qS + 1)%r * eps_comm / (1%r - p_rej) +
      qS%r * eps_comm * (qS%r + 1%r) / (2%r * (1%r - p_rej) ^ 2)) + delta_.
proof.
(* Instantiate the security proof for SimplifiedDilithium, this is 99% of the proof *)
have SD_security := SD.SimplifiedDilithium_secure (RedS (A)) _ _ &m.
- by move => H' O'; proc; call (A_bound H' O'); auto.
- by move => O' H' ? ?; islossless; exact (A_ll O' H').
apply: ler_trans SD_security. byequiv => //; proc. 
inline{1} 2; inline{2} 2.
inline{1} 2; inline{2} 2.
inline{2} 10.
(* suff to show that signature, RO state, and pk agree *)
seq 12 14 : (={m,sig} /\ PRO.RO.m{1} = SD.FSaCR.DSS.PRO.RO.m{2} /\ 
             O_CMA_Default.qs{1} = SD.FSaCR.DSS.DS.Stateless.O_CMA_Default.qs{2} /\
             pk{1} = (mA,base2highbitsV t){2} /\ pk{2} = (mA,t){2}); last first. 
- inline {1} 3; inline{2} 3. inline{1} 2; inline{2} 2. wp.
  inline {1} 1; inline{2} 1. wp. 
  call(: PRO.RO.m{1} = SD.FSaCR.DSS.PRO.RO.m{2}); 1: by auto.
  by auto => />.
(* Turn mA, s1, s2, and t into global variables *)
wp; swap{1} 1 4. swap{2} 1 4. 
seq 4 4 : (={glob A,mA,s1,s2,t} /\ (t = mA *^ s1 + s2){1}).
  by wp; sim : (={glob A,mA,s1,s2}).
exlim t{1} => t; exlim s1{1} => s1; exlim s2{1} => s2; exlim mA{1} => mA.
(* Soundness of the reduction *)
call (: t = mA *^ s1 + s2 /\
        PRO.RO.m{1} = SD.FSaCR.DSS.PRO.RO.m{2} /\ 
        O_CMA_Default.qs{1} = SD.FSaCR.DSS.DS.Stateless.O_CMA_Default.qs{2} /\
        O_CMA_Default.sk{1} = (mA,s1,s2, base2lowbitsV t) /\
        SD.FSaCR.DSS.DS.Stateless.O_CMA_Default.sk{2} = (mA,s1,s2)).
- proc; inline{1} 1; inline{2} 1; wp; conseq />. 
- while (={response,c,mA,s1,s2,t0,m0} /\ PRO.RO.m{1} = SD.FSaCR.DSS.PRO.RO.m{2}).
    by sim.
  by auto => />.
- by proc; auto.
by inline*; auto => />.
qed.

end section PROOF.

end AbstractDilithium.

abstract theory ConcreteDilithium.

(* We again assume some parameter set *)
clone import DParams as Params.

(* We instantiate the concrete ring ℤq[X]/(X^n + 1) 
   using q and n as given by the paramers *)
clone import ConcreteDRing as CDR with 
  op Round.q <= Params.q,
  op Round.n <= Params.n,
  axiom Round.prime_q <= Params.prime_q,
  axiom Round.gt0_n <= Params.gt0_n
(* proof* *)
(* TODO: proof* gives more than just the (unavoidable) subtype axioms *)

(* E: Not anymore. The fix I did was stranded on a different branch...
 * btw, the `to_poly` and `of_poly` stuff are just renamed subtype axioms. *)
.

clone import AbstractDilithium as ConcreteDilithium with 
  theory Params <- Params,
  theory DR <- CDR.DR.
(* The above is accepted by EC. This verifies that the concrete 
   DRing instance (CDR.DR) implements the abstract DRing (DR) assumed by 
   the AbstractDilithium theory. *)

end ConcreteDilithium.
