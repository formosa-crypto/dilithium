require import AllCore Distr List IntDiv StdOrder.
require import DistrExtras.
import RealOrder.

require DRing DVect MLWE SelfTargetMSIS.
require SimplifiedScheme.


(** Abstract Version using DRing *)

abstract theory AbstractDilithium.

(* abstract data structure for Rq                       *)
(* this defines an abstract type Rq and a constant q    *)
(* also includes highBits, norms, etc.                  *)
clone import DRing as DR.

(* Parameters: *)
(* Note: eta and beta are keywords in EC, so we use a trailing _ *)

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

(* Generate a theory of matrices/vectors over Rq           *)
clone import DVect as DV with 
  theory DR <= DR,
  op HL.alpha <- 2*gamma2,
  op HL.d     <- d
proof 
  HL.ge2_alpha, HL.alpha_halfq_le, HL.even_alpha, HL.alpha_almost_divides_q.
realize HL.ge2_alpha by smt(gamma2_bound).
realize HL.even_alpha by smt().
realize HL.alpha_halfq_le by smt(gamma2_bound).
realize HL.alpha_almost_divides_q by apply gamma2_div.

import DV.MatRq. (* Matrices and Vectors over Rq *)
import DV.HL.    (* highBitsV and lowBitsV with HL.alpha = 2 * gamma2 and HL.d = d *)
type M.
type SK = matrix * vector * vector * vector.
type PK = matrix * high2 list.
type commit_t = high list.
type challenge_t = Rq.
type response_t = vector * hint_t list.
type Sig = challenge_t * response_t.

module type Hash  = {
  proc get(x : high list * M) : challenge_t
}.

module Dilithium (H: Hash) = {
  proc keygen() : PK * SK = {
    var pk, sk;
    var mA, s1, s2,t, t1,t0;
    mA <$ dmatrix dRq k l;
    s1 <$ dvector (dRq_ eta_) l;
    s2 <$ dvector (dRq_ eta_) k;
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
    var c : R;
    var ctr : int;
    var y, w, w1;
    var mA, s1, s2;
    var t0;
    (* silences unused variable warning *)
    c <- witness;

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
    var result;
    (mA, t1) <- pk;

    (c, response) <- sig;
    (z, h) <- response;
    w1 <- useHintV h (mA *^ z - c ** base2shiftV t1);
    c' <@ H.get((w1, m));
    result <- size z = l /\ size h = k /\ inf_normv z < gamma1 - beta_ /\ c = c';

    return result;
  }
}.

(*************************************)
(**** Parameters of the proof ********)
(*************************************)

(* TOTHINK: can we make these section variables? *)
const qS : { int | 0 <= qS } as qS_ge0.
const qH : { int | 0 <= qH } as qH_ge0.


(** We require a check on the matrix component of public and secrect
key that ensures:

- sufficiently high commitment entropy
- sufficiently high probability that respond succeeds *)

op dA = dmatrix dRq k l.
op dy = dvector (dRq_ (gamma1 - 1)) l.
op dz = dvector (dRq_ (gamma1 - beta_ - 1)) l.

(* Check that ensures that the matrix is "entropy preserving" *)
(* (and has the right dimensions)                             *)
op check_mx : matrix -> bool.

axiom check_valid A : check_mx A => A \in dA.

(* upper bound on the mass of the most likely commitment for a good key *)
const eps_comm  : { real | 0%r < eps_comm } as eps_comm_gt0.

axiom check_mx_entropy (mA : matrix) : 
  check_mx mA => p_max (dmap dy (fun y => highBitsV (mA *^ y))) <= eps_comm.

op A0 : { matrix | check_mx A0 } as A0P.

(* upper bound on the mass of the keys not passing check *)
const eps_check : { real | 0%r <= eps_check }  as eps_check_gt0.

axiom check_mx_most : mu dA (predC check_mx) <= eps_check.

(* bound on the probability that he low-bis check in the Sim fails *)
const eps_low : { real | eps_low < 1%r } as eps_low_lt1.

axiom bound_low c (t : vector) (mA : matrix) :
  c \in dC tau => t \in dvector dRq k => check_mx mA =>
  mu dz (fun z => gamma2 - beta_ <= inf_normv (lowBitsV (mA *^ z - c ** t)) ) <= eps_low. 

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

(* Clone Simplified Dilithium Scheme *)

(* TOTHINK: It would be nice to make this a local clone. 
   However, it defines the reductions to MLWE and SelfTargetMSIS that are part of the final statement. 
   It also provides the instances themselves (including the parameters *)
clone SimplifiedScheme as SD with 
  theory DR <- DR,
  theory DV <- DV,
  type M <- M,

  op e <- eta_,
  op b <- beta_,
  op gamma1 <- gamma1,
  op gamma2 <- gamma2,
  op k <- k,
  op l <- l,
  op tau <- tau,
  op d <- d,
  axiom tau_bound <- tau_bound,

  op check_mx <- check_mx,
  op eps_comm <- eps_comm,
  op eps_check <- eps_check,
  op eps_low <- eps_low,
  axiom eps_comm_gt0 <- eps_comm_gt0,
  axiom eps_check_gt0 <- eps_check_gt0,
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

print SD.FSaCR.DSS.Adv_EFCMA_RO.

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

(* Reduction to MLWE *)
module RedMLWE (A : Adv_EFCMA_RO) = 
  SD.RedMLWE(SD.RedCR(SD.CMAtoKOA.RedKOA(SD.CG.RedFSaG(RedS(A)), SD.HVZK_Sim_Inst)), SD.FSaCR.DSS.PRO.RO).

(* Reduction to SelfTargetMSIS *)
module RedStMSIS (A : Adv_EFCMA_RO) = 
  SD.RedMSIS(SD.RedCR(SD.CMAtoKOA.RedKOA(SD.CG.RedFSaG(RedS(A)), SD.HVZK_Sim_Inst))).

lemma SimplifiedDilithium_secure &m :
 Pr[EF_CMA_RO(Dilithium, A, H, O_CMA_Default).main() @ &m : res] <=
     `|Pr[SD.RqMLWE.GameL(RedMLWE(A)).main() @ &m : res] -
       Pr[SD.RqMLWE.GameR(RedMLWE(A)).main() @ &m : res]| +
     Pr[SD.RqStMSIS.Game(RedStMSIS(A), SD.RqStMSIS.PRO.RO).main () @ &m : res] +
     (2%r * qS%r * (qH + qS + 1)%r * eps_comm / (1%r - SD.p_rej) +
      qS%r * eps_comm * (qS%r + 1%r) / (2%r * (1%r - SD.p_rej) ^ 2)) + 2%r * eps_check.
proof.
have SD_security := SD.SimplifiedDilithium_secure (RedS (A)) _ _ &m.
- by move => H' O'; proc; call (A_bound H' O'); auto.
- by move => O' H' ? ?; islossless; exact (A_ll O' H').
apply: ler_trans SD_security; byequiv => //; proc. 
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

require ConcreteDRing.

const q : { int | prime q } as prime_q.
const n : { int | 0 < n } as gt0_n.

(* clone import ConcreteDRing as CR proof*. *)

clone import ConcreteDRing as CDR with 
  op Round.q <= q,
  op Round.n <= n,
  axiom Round.prime_q <= prime_q,
  axiom Round.gt0_n <= gt0_n
(* proof* *)
(* TODO: proof* gives more than just the (unavoidable) subtype axioms *)
.

clone import AbstractDilithium as ConcreteDilithium with 
  theory DR <- CDR.DR.

end ConcreteDilithium.

(* TODO: this has more axioms than there should be *)
(* clone ConcreteDilithium as CD proof*. *)


