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


axiom gamma2_bound  : 2 <= gamma2 <= q %/ 4.
axiom gamma2_div : 2 * gamma2 %| (q - 1).

axiom beta_gamma1_lt : beta_ < gamma1.
axiom beta_round_gamma2_lt : beta_ < 2 * gamma2 %/ 2.

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
type SK = matrix * vector * vector.
type PK = matrix * vector.
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
    var mA, s1, s2,t;
    mA <$ dmatrix dRq k l;
    s1 <$ dvector (dRq_ eta_) l;
    s2 <$ dvector (dRq_ eta_) k;
    t  <- mA *^ s1 + s2;
    pk <- (mA, t);
    sk <- (mA, s1, s2);
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

    (mA, s1, s2) <- sk;
    t0 <- base2lowbitsV (mA *^ s1 + s2); (* compute t0 *)

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
    var mA, t, t1;
    var result;
    (mA, t) <- pk;
    t1 <- base2highbitsV t; (* t only used to compure t1 *)

    (c, response) <- sig;
    (z, h) <- response;
    w1 <- useHintV h (mA *^ z - c ** base2shiftV t1);
    c' <@ H.get((w1, m));
    result <- size z = l /\ size h = k /\ inf_normv z < gamma1 - beta_ /\ c = c';

    return result;
  }
}.


(* keygen as a mathematical distribution - for use in axioms *)
op dA = dmatrix dRq k l.
op ds1 = dvector (dRq_ eta_) l.
op ds2 = dvector (dRq_ eta_) k.
op keygen : (PK * SK) distr =
  dlet (dmatrix dRq k l) (fun mA =>
  dlet ds1 (fun s1 =>
  dmap ds2 (fun s2 =>
  let pk = (mA, mA *^ s1 + s2) in
  let sk = (mA, s1, s2) in
  (pk, sk)))).

(* commit as a mathematical distribution - for use in axioms *)
op dy = dvector (dRq_ (gamma1 - 1)) l.
type pstate_t = vector. 
op commit (sk : SK) : (commit_t * pstate_t) distr =
  let (mA, s1, s2) = sk in
  dmap dy (fun y =>
  let w1 = highBitsV (mA *^ y) in
  (w1, y)).

(* respond as a mathematical function - for use in axioms *)
op respond (sk : SK) (c : challenge_t) (y: pstate_t) : response_t option =
  let (mA, s1, s2) = sk in
  let t0 = base2lowbitsV (mA *^ s1 + s2) in
  let w = mA *^ y in
  let z = y + c ** s1 in
  if inf_normv z < gamma1 - beta_ /\
     inf_normv (lowBitsV (mA *^ y - c ** s2) ) < gamma2 - beta_ then
    let h = makeHintV (- c ** t0) (w - c ** s2 + c ** t0) in
    Some (z, h)
    else None.


(* Parameters of the proof *)
(* TOTHINK: can we make these section variables? *)
const qS : { int | 0 <= qS } as qS_ge0.
const qH : { int | 0 <= qH } as qH_ge0.


op valid_sk sk = exists pk, (pk,sk) \in keygen.
(* a check for "good" keys *)
op check (sk : SK) : bool.

(* upper bound on the mass of the most likely commitment for a good key *)
const eps_comm  : { real | 0%r < eps_comm }   as eps_comm_gt0.
(* upper bound on the mass of the keys not passing check *)
const eps_check : { real | 0%r <= eps_check }  as eps_good_gt0.
(* upper bound in on the rejection probability for good keys *)
const p_rej  : { real | 0%r <= p_rej < 1%r} as p_rej_bounded.

(* all secret keys passing the check have high commitment entropy *)
axiom check_entropy (sk : SK) : valid_sk sk => check sk =>
  p_max (dfst (commit sk)) <= eps_comm.

(* most honestly sampled secret keys pass the check *)
axiom check_most : mu (dsnd keygen) (predC check) <= eps_check.

(* probability that response fails on "good" keys is bounded by p_rej *)
axiom rej_bound (sk : SK) :
  sk \in dsnd (dcond keygen (check \o snd)) =>
  mu (commit sk `*` dC tau) 
     (fun (x : (commit_t * pstate_t) * challenge_t) => respond sk x.`2 x.`1.`2 = None) <= p_rej.

(* Some good key. Since keygen is lossless and check only rules out
small fraction, we could just use epsilon here. *)
const sk0 : { SK | (exists pk, (pk,sk0) \in keygen) /\ check sk0 } as sk0P.

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
  theory FSaCR.DSS <- DSS,

  op e <- eta_,
  op b <- beta_,
  op gamma1 <- gamma1,
  op gamma2 <- gamma2,
  op k <- k,
  op l <- l,
  op tau <- tau,
  op d <- d,
  axiom tau_bound <- tau_bound,

  op check <- check,
  op eps_comm <- eps_comm,
  op eps_check <- eps_check,
  op p_rej <- p_rej,
  axiom eps_comm_gt0 <- eps_comm_gt0,
  axiom eps_good_gt0 <- eps_good_gt0,
  axiom check_entropy <- check_entropy,

  op qS <- qS,
  op qH <- qH,
  axiom qS_ge0 <- qS_ge0,
  axiom qH_ge0 <- qH_ge0
proof* by admit. (* TODO *)




section PROOF.

(* We assume some adversary A whose memory is disjoint from the random
oracle H, the signing oracle of che EUF_CMA game, and all the
auxiliary constructions used in the proof. *)

declare module A <: DSS.Adv_EFCMA_RO{
  -H, -O_CMA_Default,
  -SD.H, -SD.G, 
  -SD.OpBasedSig, 
  -SD.CMAtoKOA.ORedKOA, 
  -SD.CMAtoKOA.CountS, 
  -SD.CMAtoKOA.CountH, 
  -SD.CountS, 
  -SD.CountH, 
  -SD.O_CMA_Default_G, 
  -SD.RO_G, 
  -SD.OpBasedSigG}.

(* A's attemts at forging a signature terminate, 
  provided the oracles it is provided with are terminating *)
declare axiom A_ll (SO' <: SOracle_CMA{-A}) (H' <: Hash{-A} ) : 
  islossless SO'.sign => islossless H'.get => islossless A(H', SO').forge.

(* A makes no more than qH random oracle (i.e., hash) queries 
  and no more than qS many signing queries *)
declare axiom A_bound 
  (H' <: Hash{-SD.CountS, -SD.CountH, -A} )
  (SO' <: SOracle_CMA{-SD.CountS, -SD.CountH, -A} ) :
  hoare[ A(SD.CountH(H'), SD.CountS(SO')).forge :
      SD.CountH.qh = 0 /\ SD.CountS.qs = 0 ==>
      SD.CountH.qh <= qH /\ SD.CountS.qs <= qS].

module RedMLWE (A : Adv_EFCMA_RO) = 
  SD.RedMLWE(SD.RedCR(SD.CMAtoKOA.RedKOA(SD.CG.RedFSaG(A), SD.HVZK_Sim_Inst)), PRO.RO).

module RedStMSIS (A : Adv_EFCMA_RO) = 
  SD.RedMSIS(SD.RedCR(SD.CMAtoKOA.RedKOA(SD.CG.RedFSaG(A), SD.HVZK_Sim_Inst))).

lemma SimplifiedDilithium_secure &m :
 Pr[EF_CMA_RO(Dilithium, A, H, O_CMA_Default).main() @ &m : res] <=
     `|Pr[SD.RqMLWE.GameL(RedMLWE(A)).main() @ &m : res] -
       Pr[SD.RqMLWE.GameR(RedMLWE(A)).main() @ &m : res]| +
     Pr[SD.RqStMSIS.Game(RedStMSIS(A), SD.RqStMSIS.PRO.RO).main () @ &m : res] +
     (2%r * qS%r * (qH + qS + 1)%r * eps_comm / (1%r - p_rej) +
      qS%r * eps_comm * (qS%r + 1%r) / (2%r * (1%r - p_rej) ^ 2)) + 2%r * eps_check.
proof.
apply: ler_trans (SD.SimplifiedDilithium_secure A A_bound A_ll &m).
byequiv (_ : ={glob A} ==> ={res}) => //. sim.
qed.

end section PROOF.

end AbstractDilithium.
