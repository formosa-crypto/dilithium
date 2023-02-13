require import AllCore Distr List DistrExtras.
require import Finite DBool.
import Biased.
require DigitalSignaturesRO.
require MatPlus.
require import RealSeries Supplementary Finite.
(* require import PolyReduce. *)
require import IntDiv.
(* require ZqRounding. *)
(* require ZModFieldExtras. *)
require import Nat.

require import IDSabort.
require FSabort.
require FSa_CMAtoKOA.
require FSa_CRtoGen.

require DRing DVect MLWE SelfTargetMSIS. 

require DParams.

clone import DParams as Params.

(* Parameters of the security games *)
const qS : int. (* allowed number of sig queries *)
const qH : int. (* allowed number of ro  queries *)
axiom qS_ge0 : 0 <= qS.
axiom qH_ge0 : 0 <= qH.

(* Dilithium-specific parameters *)

(* Abstract theory representing Rq = Zq[X]/(X^n + 1) and the high/lowBits operations *)
(* The constants [n] and [q] are defined by this theory *)
clone import DRing as DR with
  op q <= q,
  op n <= n
proof prime_q by exact prime_q
proof gt0_n by exact gt0_n.
import RqRing.

clone import DVect as DV with 
  theory DR <- DR,
  op HL.alpha <- 2*gamma2,
  op HL.d     <- d
proof HL.ge2_alpha, HL.alpha_halfq_le, HL.even_alpha, HL.alpha_almost_divides_q, HL.d_bound.
realize HL.ge2_alpha by smt(gamma2_bound).
realize HL.even_alpha by smt().
realize HL.alpha_halfq_le by smt(gamma2_bound).
realize HL.alpha_almost_divides_q by apply gamma2_div.
realize HL.d_bound.
  split; 1: smt(gt0_d). 
  apply (StdOrder.IntOrder.ler_lt_trans (tau * 2 ^ d)). 
    smt(gt0_d tau_bound StdOrder.IntOrder.expr_gt0).
  apply (StdOrder.IntOrder.ler_lt_trans (2 * gamma2) _ _ ub_d). 
  suff : `| 2 * gamma2 | <= `|Params.q -1| by smt(gamma2_bound prime_q gt1_prime). 
  by apply dvdz_le; smt(prime_q gt1_prime gamma2_div).
qed.

import DV.MatRq. (* Matrices and Vectors over Rq *)
import DV.HL.    (* highBitsV and lowBitsV with HL.alpha = 2 * gamma2 and HL.d = d *)

lemma cnorm_dC c tau : c \in dC tau => cnorm c <= 1 by smt(supp_dC).

type M.

type challenge_t = Rq.
type SK = matrix * vector * vector.
type PK = matrix * vector.
type commit_t = high list.
type response_t = vector * hint_t list.

(* Just storing `y` should be good here. *)
type pstate_t = vector. 

clone IDS as DID with 
  type PK <= PK,
  type SK <= SK,
  type W <= commit_t,
  type C <= challenge_t,
  type Z <= response_t,
  type Pstate <= pstate_t proof*.

clone import FSabort as FSa with 
  theory ID <= DID,
  type M <= M,
  op dC <= dC tau
proof* by smt(dC_ll dC_uni tau_bound).

(* no longer needed
clone import FSabort as OpFSA with
  type ID.PK <= PK,
  type ID.SK <= SK,
  type ID.W <= commit_t,
  type ID.C <= challenge_t,
  type ID.Z <= response_t,
  type ID.Pstate <= pstate_t,
  type M <= M,
  op dC <= dC tau
proof* by smt(dC_ll dC_uni tau_bound). *)

(* -- Procedure-based -- *)

op recover (pk : PK) (c : challenge_t) (resp : response_t) : commit_t =
  let (mA, t) = pk in
  let (z, h) = resp in
  useHintV h (mA *^ z - c ** base2shiftV (base2highbitsV t)).

clone FSa.CommRecov as FSaCR with
  op recover <= recover,
  op qS <= qS,
  op qH <= qH
proof* by smt(qS_ge0 qH_ge0).

import FSaCR.
import FSaCR.DSS.

(* This scheme corresponds to the scheme in KLS18 Figure 13, whith the
following minor differences:

- We (uniformly) sample the matrix A rather than a seed
- The public key is (A,t) rather than (A,t1,t0)
- The secret key is (A,s1,s2) rather than (A,s1,s2,t0) 
- sign (resp. verify) computes t0 (t1) from s1 and s2 (t).
- due to liberal typing, verify needs to check the size (length) of the signature

This avoids having to split/merge t (e.g., in the MLWE reduction). We
eliminate these differences using a separate reduction *)

module (SimplifiedDilithium : SchemeRO)(H: Hash) = {
  proc keygen() : PK * SK = {
    var pk, sk;
    var mA, s1, s2,t;
    mA <$ dmatrix dRq k l;
    s1 <$ dvector (dRq_ Params.eta_) l;
    s2 <$ dvector (dRq_ Params.eta_) k;
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

(** KOA to MLWE + SelfTargetMSIS *)

clone import MLWE as RqMLWE with 
  theory M <- MatRq,
  op dR <- dRq,
  op dS <- dRq_ Params.eta_,
  op k <- k,
  op l <- l
proof* by smt(gt0_k gt0_l).

clone import SelfTargetMSIS as RqStMSIS with
  theory M <- MatRq,
  type M <- M,
  op m <- k,
  op n <- l+1,
  op dR <- dRq,
  op dC <- dC tau,
  op inf_norm <- inf_normv,
  op gamma <- max (gamma1 - beta_) (tau * 2^(d-1) + (2*gamma2+1))
proof* by smt(gt0_k Params.gt0_l).

module H = DSS.PRO.RO.
module G = RqStMSIS.PRO.RO.

module RedMLWE (A : Adv_EFKOA_RO) (H : Hash_i) : RqMLWE.Adversary = { 
  proc distinguish (mA : matrix, t : vector) = { 
    var pk,m,sig,r;
    H.init();
    pk <- (mA,t);
    (m,sig) <@ A(H).forge(pk);
    r <@ SimplifiedDilithium(H).verify(pk,m,sig);
    return r;
  }
}.

module H' : Hash_i = { 
  proc init = G.init

  proc get(w1,mu) = {
    var r;
    r <@ G.get(shiftV w1,mu);
    return r;
  }
}.

module RedMSIS (A : Adv_EFKOA_RO) (H : RqStMSIS.PRO.RO) = { 
  proc guess(mB : matrix) : vector * M = { 
    var mA,tbar,t,mu,sig,c,zh,z,h;
    var t1,r,u1,u2,y;
    mA <- subm mB 0 k 0 l;
    tbar <- col mB l;
    t <- -tbar;
    (mu,sig) <@ A(H').forge(mA,t); (* discard H, use H' *)
    y <- witness;
    (c,zh) <- sig;
    (z,h) <- zh;
    t1 <- base2highbitsV t;
    r <- mA *^z - c ** base2shiftV t1;
    u1 <- r - shiftV (useHintV h r);
    u2 <- c ** base2lowbitsV t;
    y <- (u2 - u1) || z || vectc 1 c;

    return (y,mu);
  }
}.


section PROOF.

declare module A <: Adv_EFKOA_RO{-H,-G}.

local module S1 (H : Hash) = { 
  proc keygen() : PK * SK = {
    var pk, mA, t;
    mA <$ dmatrix dRq k l;
    t  <$ dvector dRq k;
    pk <- (mA, t);
    return (pk,witness);
  }
  
  proc sign(sk: SK, m: M) : Sig = { return witness; }

  proc verify = SimplifiedDilithium(H).verify
}.

(* Hop 1 : replace keygen with (completely) random public key *)
local lemma hop1 &m : 
  Pr [EF_KOA_RO(SimplifiedDilithium,A,H).main() @ &m : res ] <=
  Pr [EF_KOA_RO(S1,A,H).main() @ &m : res] + 
  `| Pr[ GameL(RedMLWE(A,H)).main() @ &m : res ] - Pr [ GameR(RedMLWE(A,H)).main() @ &m : res ] |.
proof.
have -> : Pr [EF_KOA_RO(SimplifiedDilithium,A,H).main() @ &m : res ] = 
          Pr[ GameL(RedMLWE(A,H)).main() @ &m : res ].
- byequiv (_: ={glob A,glob H} ==> ={res}) => //; proc. 
  inline{1} 2; inline{1} 2; inline{2} 4. swap{2} 6 -5.
  by sim; wp; sim. (* why is the "wp" necessary - is sim this stupid? *)   
suff -> : Pr [EF_KOA_RO(S1,A,H).main() @ &m : res ] = 
          Pr[ GameR(RedMLWE(A,H)).main() @ &m : res ] by smt().
- byequiv (_: ={glob A,glob H} ==> ={res}) => //; proc. 
  inline{1} 2; inline{1} 2; inline{2} 3. swap{2} 5 -4. 
  by sim; wp; sim. 
qed.

import SmtMap.

(* Hop2 : replace H with H' (wrapped RO from SelfTargetMSIS *)
local lemma hop2 &m : 
  Pr [EF_KOA_RO(S1,A,H).main() @ &m : res] = Pr [EF_KOA_RO(S1,A,H').main() @ &m : res].
proof.
byequiv (_ : ={glob A} ==> ={res}) => //; proc. 
inline{1} 2; inline{2} 2. 
seq 3 3 : (={m,sig,pk} /\ 
           forall (w : commit_t) (mu : M), 
             H.m.[(w,mu)]{1} = G.m.[(shiftV w,mu)]{2}). 
- call (:forall (w : commit_t) (mu : M), 
         H.m.[(w,mu)]{1} = G.m.[(shiftV w,mu)]{2}).
  + proc; inline*; sp. 
    seq 1 1 : (#pre /\ r{1} = r0{2}); first by auto.
    if; 1,3: by auto => /> /#.
    auto => />. smt(get_setE set_set_sameE shiftV_inj).
  by inline*; auto => />; smt(emptyE).
inline*; auto => />; smt(get_set_sameE).
qed.

import StdOrder.RealOrder.

(* move to EC lib? *)
lemma maxr_lerP (i j k : int) : i <= max j k <=> i <= j \/ i <= k by smt().

local lemma hop3 &m : 
  Pr[EF_KOA_RO(S1, A, H').main() @ &m : res] <= Pr[Game(RedMSIS(A), G).main() @ &m : res].
proof.
byequiv (_ : ={glob A} ==> res{1} => res{2}) => //; proc. 
inline{1} 2; inline{1} 1. inline{1} 2; inline{2} 3. 
seq 6 7 : (={sig,PRO.RO.m} /\ (forall x, x \in PRO.RO.m => oget PRO.RO.m.[x] \in dC tau){1}
           /\ m{1} = mu0{2} /\ pk{1} = (mA0,t){2} /\ 
           (mA = (mA0 || - colmx t) /\ size mA0 = (k,l) /\ size t = k){2}).
- (* merge [dmatrix/dvector] sampling on LHS *)
  seq 3 2 : (={glob A,PRO.RO.m} /\ (forall x, x \in PRO.RO.m => oget PRO.RO.m.[x] \in dC tau){1}
            /\ size mA{1} = (k,l) /\ size t{1} = k /\
            (mA || - colmx t){1} = mA{2}). 
  + inline*; sp 1 1. 
    conseq (:_ ==> size mA{1} = (k,l) /\ size t{1} = k /\ (mA || - colmx t){1} = mA{2}).
    * smt(emptyE).
    rnd (fun mAt : matrix * vector => (mAt.`1 || -colmx mAt.`2))  
        (fun mAt : matrix => (subm mAt 0 k 0 l,- col mAt l)) : *0 *0.
    skip => /= &1 &2 _. split => [A|?]; last split => [A|?].
    * rewrite dmap_id => /size_dmatrix /(_ _ _) /=; 1,2: smt(gt0_k Params.gt0_l).
      rewrite colmxN oppvK => -[<-] ?. rewrite subm_colmx; smt(gt0_k Params.gt0_l).
    * rewrite -(dmap_dprodE _ _ (fun x => x)) !dmap_id.
      rewrite dprod1E (@dvector_rnd_funi _ _ (col A l)) ?dRq_funi // -dprod1E.
      move/size_dmatrix => /(_ _ _); 1,2: smt(gt0_k Params.gt0_l).
      apply dmatrixRSr1E; 1,2: smt(gt0_k Params.gt0_l).
    case => A t /=; rewrite -(dmap_dprodE _ _ (fun x => x)) !dmap_id supp_dprod /=.
    case => supp_A supp_t. 
    move: (supp_A) => /size_dmatrix /(_ _ _) /=; 1,2: smt(gt0_k Params.gt0_l).
    move: (supp_t) => /size_dvector. rewrite lez_maxr; 1:smt(gt0_k). move => s_t [r_A c_A].
    (* case => /supp_dmatrix_Rqkl /= [[r_A c_A] Rq_A] /supp_dvector_Rqk [s_t Rq_t]. *)
    rewrite r_A c_A s_t /= -{2}r_A -{2}c_A subm_catmrCl /=.
    rewrite col_catmrR /= ?r_A ?c_A ?s_t // subrr. 
    rewrite colN oppmK colK /=; apply supp_dmatrix_catmr => //;1,2: smt(gt0_k Params.gt0_l).
    rewrite supp_dmatrix_full ?dRq_fu //; smt(gt0_k Params.gt0_l). 
  call (: ={PRO.RO.m} /\ (forall x, x \in PRO.RO.m => oget PRO.RO.m.[x] \in dC tau){1}).
    proc; inline*; auto => />; smt(get_setE get_set_sameE).
  auto => /> &1 &2 RO_dC r_mA c_mA s_t. split => [|E1 E2]. 
  + rewrite -r_mA -c_mA subm_catmrCl /=.
    rewrite col_catmrR //= 1:/#. 
    by rewrite colN oppmK colK. 
  move => _ _.     
  by rewrite -E1 -E2 /= rows_catmr //=; smt(gt0_k Params.gt0_l).
(* If A forges successfully the reduction succeeds in the SelfTargetMSIS game *)
inline S1(H').verify  H'.get. wp. sp.
(* need [size z{1} = l /\ size h{1} = l] to prove equality of the RO argument *)
case (size z{1} = l /\ size h{1} = k);
  last by conseq (:_ ==> true); [ smt() | inline*; auto].
call(: ={arg,glob G} /\ (forall x, x \in PRO.RO.m => oget PRO.RO.m.[x] \in dC tau){1} 
       ==> ={res} /\ res{1} \in dC tau).
- by proc; inline*; auto => />; smt(get_set_sameE).
auto => /> &1 _.
move: (mA0{1}) (t{1}) (z{1}) (c0{1}) (h{1}) => mA t z c h {&1 &m}.
move => r_mA c_mA size_t size_z size_h.
(* Recover the definitions from the reduction *)
pose t0 := base2lowbitsV t.
pose t1 := base2highbitsV t.
pose r  := mA *^ z - c ** base2shiftV t1.
pose r' := shiftV (useHintV h r).
pose u1 := r - r'; pose u2 := c ** t0.
have size_Az : size (mA *^ z) = k by rewrite size_mulmxv.
have [size_r size_r'] : size r = k /\ size r' = k.
  rewrite /r' /r. rewrite !size_addv size_shiftV size_useHintV size_addv.
  rewrite size_Az size_oppv size_scalarv size_base2shiftV.
  rewrite size_base2highbitsV /#.
have size_u : size (u2 - u1) = k. 
  rewrite size_addv size_scalarv size_oppv size_addv size_oppv size_base2lowbitsV /#.
split => [|_ c_dC normv_z]; last split. 
- (* StMSIS Oracle is called on the same arguments *)
  rewrite mulmxv_cat; 1: smt(size_addv size_oppv gt0_k).
  rewrite mulmxv_cat 1:/#. 
  rewrite colmxN mul_colmxc -size_u mulmx1v scalarvN.
  suff : u2 - r + (mA *^ z - c ** t) = zerov k by smt(addvA addvC addv0 oppvD oppvK).
  suff : (mA *^ z - mA *^ z) + (c ** base2shiftV t1 + c ** t0 - c** t) = zerov k.
     smt(addvA addvC oppvD oppvK).
  rewrite addvN lin_add0v. 
  + rewrite ?size_Az ?size_addv ?size_oppv ?size_scalarv ?size_base2shiftV.
    rewrite size_base2highbitsV size_base2lowbitsV /#.
  by rewrite -scalarvDr b2high_lowPv addvN size_scalarv size_t.
- (* The StMSIS solution is "short" *)  
  rewrite 2!inf_normv_cat !StdOrder.IntOrder.ler_maxrP !maxr_lerP.
  rewrite [inf_normv z <= _]StdOrder.IntOrder.ltrW 1:normv_z /= 1!inf_normv_vectc //.
  have ? : 0 <= tau * (2 ^ (d - 1)). 
    smt(StdOrder.IntOrder.mulr_ge0 tau_bound StdOrder.IntOrder.expr_ge0).
  suff: inf_normv (u2 - u1) <= 2 * gamma2 + 1 + tau * 2 ^ (d - 1)
    by smt(cnorm_dC gamma2_bound).
  rewrite /u1 /u2 oppvD oppvK [_ + r']addvC addrC. 
  have X := ler_inf_normv (c ** t0) (r' - r).
  apply (StdOrder.IntOrder.ler_trans _ _ _ X) => {X}.
  apply (StdOrder.IntOrder.ler_add); last first.
  + by rewrite -inf_normvN oppvD addvC oppvK /r' hint_error /#.
  apply l1_inf_norm_product_ub; 
    1,2,3: smt(tau_bound StdOrder.IntOrder.expr_gt0 gt0_d supp_dC).
  exact b2low_bound.
- rewrite catvA get_catv_r ?size_catv 1:/#. 
  have -> : k + (l + 1) - 1 - (size (u2-u1) + size z) = 0 by smt().
  by rewrite get_vectc.
qed.

lemma KOA_bound &m : 
     Pr [EF_KOA_RO(SimplifiedDilithium,A,H).main() @ &m : res ] 
  <= `| Pr[ GameL(RedMLWE(A,H)).main() @ &m : res ] - Pr [ GameR(RedMLWE(A,H)).main() @ &m : res ] |
   + Pr [ Game(RedMSIS(A),G).main() @ &m : res]. 
proof.
apply (ler_trans _ _ _ (hop1 &m)); rewrite RField.addrC ler_add2l.
by rewrite hop2 hop3.
qed.

end section PROOF.

(* -- Operator-based -- *)

op dA = dmatrix dRq k l.
op ds1 = dvector (dRq_ Params.eta_) l.
op ds2 = dvector (dRq_ Params.eta_) k.

op keygen : (PK * SK) distr =
  dlet (dmatrix dRq k l) (fun mA =>
  dlet ds1 (fun s1 =>
  dmap ds2 (fun s2 =>
  let pk = (mA, mA *^ s1 + s2) in
  let sk = (mA, s1, s2) in
  (pk, sk)))).

op dy = dvector (dRq_ (gamma1 - 1)) l.

op commit (sk : SK) : (commit_t * pstate_t) distr =
  let (mA, s1, s2) = sk in
  dmap dy (fun y =>
  let w1 = highBitsV (mA *^ y) in
  (w1, y)).

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

op verify (pk : PK) (w1 : commit_t) (c : challenge_t) (resp : response_t) : bool =
  let (mA, t) = pk in
  let t1 = base2highbitsV t in
  let (z, h) = resp in
  size z = l /\ 
  size h = k /\
  inf_normv z < gamma1 - beta_ /\
  w1 = useHintV h (mA *^ z - c ** base2shiftV t1).

lemma keygen_ll : is_lossless keygen. 
proof. 
apply dlet_ll => [|/= mA ?]; 1: by apply dmatrix_ll; apply dRq_ll.
apply dlet_ll => [|/= s1 ?]; 1: by apply dvector_ll; apply dRq__ll.
by apply dmap_ll; apply dvector_ll; apply dRq__ll.
qed.

lemma commit_ll sk : is_lossless (commit sk).
proof.
case: sk => mA s1 s2 @/commit /=.
by apply dmap_ll; apply dvector_ll; apply dRq__ll. 
qed.

clone import OpBased with
  op keygen <= keygen,
  op commit <= commit,
  op response <= respond,
  op verify <= verify
proof* by smt(keygen_ll commit_ll).

lemma size_t pk sk : (pk,sk) \in keygen => size pk.`2 = k.
proof. 
case/supp_dlet => mA /= [s_mA]. 
case/supp_dlet => s1 /= [s_s1]. 
case/supp_dlet => s2 /= [s_s2].
rewrite /(\o) supp_dunit => -[-> _]. 
rewrite [Vectors.size]lock /= -lock.
rewrite size_addv size_mulmxv;
smt(size_dmatrix size_dvector gt0_k Params.gt0_l).
qed.

module OpBasedSig = FSaCR.IDS_Sig(OpBased.P, OpBased.V).

section OpBasedCorrectness.

declare module H <: Hash {-OpBased.P}.

equiv keygen_opbased_correct :
  OpBasedSig(H).keygen ~ SimplifiedDilithium(H).keygen :
  true ==> ={res}.
proof. 
proc; inline *.
rnd: *0 *0; skip => />; split => [kp ?|_ [pk sk]].
- by rewrite dmap_id /keygen &(mu_eq). 
by rewrite /keygen dmap_id.
qed.

equiv sign_opbased_correct :
  OpBasedSig(H).sign ~ SimplifiedDilithium(H).sign :
  ={arg,glob H} ==> ={res,glob H}.
proof.
proc; inline *; sp. 
while (oz{1} = response{2} /\ ={c,sk,glob H,m} /\
       t0{2} = base2lowbitsV (mA{2} *^ s1{2} + s2{2}) /\
       (sk = (mA,s1,s2)){2}); 
  last by auto => /> /#.
conseq (: _ ==> ={c, sk, glob H, m} /\ (sk = (mA,s1,s2)){2} 
                 /\ oz{1} = response{2}); 1: smt().
seq 4 4 : (#pre /\ w{1} = w1{2} /\ P.pstate{1} = y{2} /\ (w = mA *^ y){2} (* /\ y{2} \in dy *)).
- call(: true); conseq />; sp; wp.
  rnd (fun (wy : DID.W * vector) => wy.`2) (fun y => (highBitsV (mA{2} *^ y), y)).
  skip => /> &m.
  split => [y ? | ? [w y] HR /=].
  - rewrite /commit /= /dy /=. 
    rewrite [mu1 _ (_,_)]dmap1E &(mu_eq) => y'. 
    by rewrite /pred1 /(\o) /=; smt().
  (* fixme: the rewrite below should not be necessary *)
  by move: HR; rewrite /commit /=; case/supp_dmap => /#.
conseq />. auto => /> &m. split => [|pass_chk]. 
+ rewrite /respond /= => -> -> //=.
+ by rewrite /respond /= ifF.
qed.

equiv verify_opbased_correct :
  OpBasedSig(H).verify ~ SimplifiedDilithium(H).verify :
  ={arg,glob H} ==> ={res,glob H}.
proof.
proc; inline *.
wp; call (: true).
auto => /> /#.
qed.

end section OpBasedCorrectness.

(* -- OpBased is commitment recoverable -- *)
(* Necessary for the simulator definition below to make sense *)

lemma pk_decomp mA' t' mA s1 s2 :
  ((mA', t'), (mA, s1, s2)) \in keygen =>
  mA' = mA /\ t' = mA *^ s1 + s2.
proof.
move => /supp_dlet H.
case H => x [? /supp_dlet H].
by case H => y [? /supp_dmap H] /#.
qed.

lemma sk_size mA s1 s2 :
  (exists pk, (pk, (mA, s1, s2)) \in keygen) => size mA = (k, l) /\ size s1 = l /\ size s2 = k.
proof.
move => [pk /supp_dlet valid_keys].
case valid_keys => [mA' [mA_supp /supp_dlet valid_keys]].
case valid_keys => [s1' [s1_supp /supp_dmap valid_keys]].
case valid_keys => [s2' [s2_supp [#]]] *; subst.
smt(size_dmatrix size_dvector gt0_k Params.gt0_l).
qed.

lemma keygen_supp_decomp pk mA s1 s2 :
  (pk, (mA, s1, s2)) \in keygen =>
  s1 \in ds1 /\
  s2 \in ds2.
  (* There's a lot more that can be said if necessary *)
proof.
move => /supp_dlet H.
case H => a [a_supp /supp_dlet H].
case H => v1 [v1_supp /supp_dmap H].
by case H => /= v2 [v2_supp [#]] *; subst.
qed.

hoare recover_correct (pk_i : PK) (sk_i : SK) :
  DID.Honest_Execution(OpBased.P, OpBased.V).get_trans :
  ((pk_i, sk_i) \in keygen /\ arg = (pk_i, sk_i)) ==>
  (res <> None => let (w, c, z) = oget res in w = recover pk_i c z).
proof.
case pk_i sk_i => [mA' t'] [mA s1 s2].
proc; inline *; auto => /> valid_keys.
have sk_sizes: size mA = (k, l) /\ size s1 = l /\ size s2 = k.
- by apply sk_size; exists (mA', t').
have rg_s2: s2 \in ds2 by smt(keygen_supp_decomp).
case /pk_decomp valid_keys => [??]; subst.
move => [w0 y0] @/commit /= /supp_dmap [y [y_supp [??]]] c c_supp H w c' z; subst.
have {H} H /=: (respond (mA, s1, s2) c y <> None) by smt().
rewrite H /respond /= => [#] *; subst c' w z.
rewrite ifT 1:/# /recover /=.
(* recover some definitions *)
pose t := mA *^ s1 + s2.
pose t1 := base2highbitsV t.
pose t0 := base2lowbitsV t.
pose w := mA *^ y.
pose z := y + c ** s1.
rewrite mulmxvDr mulmx_scalarv -/w. 
have W : w - c ** s2 = mA *^ z - c ** t0 - c ** base2shiftV t1.
  rewrite /w /z mulmxvDr -!addvA; congr.
  rewrite mulmx_scalarv -!scalarvN -2!scalarvDr. congr. 
  rewrite -oppvD [t0+_]addvC b2high_lowPv /t. 
  by rewrite oppvD addvA addvN size_mulmxv /= lin_add0v /#.
have W' : w - c ** s2 + c ** t0 =  mA *^ z - c ** base2shiftV t1.
  rewrite W -!addvA; congr; rewrite [_ + c**t0]addvC addvA [_ + c**t0]addvC addvN.
  rewrite lin_add0v // size_oppv.
  by rewrite !size_scalarv size_base2lowbitsV size_base2shiftV size_base2highbitsV.
rewrite W'.
have -> : w + c ** (mA *^ s1) = mA *^ z by rewrite /w /z mulmxvDr mulmx_scalarv.
rewrite usehint_correctV.
- rewrite size_addv !size_oppv !size_scalarv size_base2shiftV size_mulmxv.
  have ->: size t0 = size t by smt(size_base2lowbitsV).
  have ->: size t1 = size t by smt(size_base2highbitsV).
  suff: size t = rows mA by smt().
  by rewrite size_addv size_mulmxv /#.
- have ->: 2 * gamma2 %/ 2 = gamma2 by smt().
  rewrite inf_normvN.
  apply (StdOrder.IntOrder.ler_trans (tau * (2 ^ d %/ 2))).
  apply l1_inf_norm_product_ub.
  + smt(tau_bound).
  + suff: 2 <= (2 ^ d) by smt().
    apply StdOrder.IntOrder.ler_eexpr => //.
    exact gt0_d.
  + smt(supp_dC).
  + suff: 2 ^ (d - 1) = 2 ^ d %/ 2 by smt(b2low_bound).
    suff: 2 * 2 ^ (d - 1) = 2 ^ d by smt(Ring.IntID.expr_pred).
    smt(Ring.IntID.exprS gt0_d).
  + smt(tau_bound ub_d gt0_d).
rewrite -addvA [(_ - _)%Vectors]addvC addvA -W.
have {1}-> : w = w - c**s2 + c**s2. 
  rewrite -addvA [_+ c**s2]addvC addvN size_scalarv. 
  rewrite addvC lin_add0v //; smt(size_mulmxv size_dvector).
have [C1 C2] {H} : inf_normv z < gamma1 - beta_ /\ 
                   inf_normv (lowBitsV (mA *^ y - c ** s2)) < gamma2 - beta_ by smt(). 
apply (hide_lowV _ _ beta_); 
  1,2,3,5: smt(size_oppv size_scalarv size_mulmxv size_dvector size_addv
               gt0_beta beta_gamma2_lt).
apply: StdOrder.IntOrder.ler_trans eta_tau_leq_b; rewrite mulrC.
apply l1_inf_norm_product_ub; 1..3: smt(tau_bound gt0_eta supp_dC).
(* Lemma *)
apply inf_normv_ler =>[|i rg_i]; first by smt(gt0_eta).
rewrite supp_dvector in rg_s2; first by smt(gt0_k).
by rewrite -supp_dRq; smt(gt0_eta). 
qed.

(* -- OpBased is indeed zero-knowledge -- *)

(* Ditstribution of "good" (i.e., small inf norm) vectors *)
op dsimz = dvector (dRq_open (gamma1 - beta_)) l.

(* fraction of "good" z compared to the domain of y *)
op line12_magic_number = (size (to_seq (support dsimz)))%r / (size (to_seq (support dy)))%r.

(* Dicectly sample oz (either a some good z or None) *)
op dsimoz : vector option distr = 
   dlet (dbiased line12_magic_number) 
        (fun b => if b then dmap dsimz Some else dunit None).

module HVZK_Sim_Inst : DID.HVZK_Sim = {
  proc get_trans(pk : PK) = {
    var mA, w', z, t,t0, resp,sample_z;
    var c <- witness;
    (mA, t) <- pk;
    t0 <- base2lowbitsV t;    
    sample_z <$ dbiased line12_magic_number;  
    if(sample_z) {
      c <$ FSa.dC;
      z <$ dsimz;
      w' <- mA *^ z - c ** t;
      resp <- if inf_normv (lowBitsV w') < gamma2 - beta_ then
        let h = makeHintV (- c ** t0) (w' + c ** t0) in Some (z, h)
      else None;
    } else {
      resp <- None;
    }
    return omap (fun z => (recover pk c z, c, z)) resp;
  }
}.

section OpBasedHVZK.

local lemma dsimz_uni :is_uniform dsimz.
proof. smt(dRq_open_uni dvector_uni). qed.

local lemma dsimz_ll : is_lossless dsimz.
proof. smt(dRq_open_ll dvector_ll). qed.

local lemma dsimz1E z : z \in dsimz => 
  mu1 dsimz z = inv (size (to_seq (support dsimz)))%r.
proof. by rewrite mu1_uni_ll ?dsimz_uni ?dsimz_ll /#. qed.

lemma supp_ds1 s1 : s1 \in ds1 <=> size s1 = l /\ inf_normv s1 <= Params.eta_.
proof. rewrite supp_dRq_vect; smt(Params.gt0_l gt0_k gt0_eta). qed.

lemma supp_ds2 s2 : s2 \in ds2 <=> size s2 = k /\ inf_normv s2 <= Params.eta_.
proof. rewrite supp_dRq_vect; smt(Params.gt0_l gt0_k gt0_eta). qed.

lemma supp_dsimz z : z \in dsimz <=> size z = l /\ inf_normv z < gamma1 - beta_.
proof. rewrite supp_dRq_vect; smt(Params.gt0_l beta_gamma1_lt). qed.

local lemma masking_range c s1 z:
  c \in FSa.dC => s1 \in ds1 => z \in dsimz =>
  (z - c ** s1) \in dy.
proof.
rewrite supp_dC supp_ds1 supp_dsimz supp_dRq_vect; 
  1,2: smt(Params.gt0_l beta_gamma1_lt gt0_beta).
move => |> cnorm_c l1_c size_s1 norm_s1 size_z norm_z. 
rewrite size_addv size_oppv size_scalarv size_z size_s1 maxrr /=.
apply (StdOrder.IntOrder.ler_trans _ _ _ (ler_inf_normv _ _)).
rewrite inf_normvN. 
suff: inf_normv (c ** s1) <= tau * Params.eta_ by smt(eta_tau_leq_b).
by apply l1_inf_norm_product_ub; smt(tau_bound gt0_eta).
qed.

local lemma is_finite_dy : is_finite (support dy).
proof. apply finite_dRq_vect; smt(Params.gt0_l beta_gamma1_lt gt0_beta). qed.

local lemma is_finite_dsimz : is_finite (support dsimz).
proof. apply finite_dRq_vect; smt(Params.gt0_l beta_gamma1_lt gt0_beta). qed.

lemma mask_size :
  size (to_seq (support dsimz)) <= size (to_seq (support dy)).
proof.
apply leq_size_to_seq => [v|]; last exact is_finite_dy.
rewrite !supp_dRq_vect; smt(Params.gt0_l gt0_beta beta_gamma1_lt).
qed.

lemma mask_nonzero :
  0 < size (to_seq (support dsimz)).
proof.
suff: zerov l \in (to_seq (support dsimz)) by smt(size_eq0 List.size_ge0).
by rewrite mem_to_seq ?is_finite_dsimz dRq_zerov; 
  smt(Params.gt0_l gt0_beta beta_gamma1_lt).
qed.

lemma clamp_magic : clamp line12_magic_number = line12_magic_number.
proof. by rewrite clamp_id; smt(clamp_id mask_size mask_nonzero). qed.

local lemma dy_ll :
  is_lossless dy.
proof. smt(dvector_ll dRq__ll). qed.

local lemma dy_uni :
  is_uniform dy.
proof. smt(dvector_uni dRq__uni). qed.

local op transz (c : Rq) s1 =
  dmap dy (fun y =>
    let z' = y + c ** s1 in
    if z' \in dsimz then Some z' else None).

local lemma line12_magic_some :
  forall c s1 z0, c \in FSa.dC => s1 \in ds1 => z0 \in dsimz =>
    mu1 (transz c s1) (Some z0) = 1%r / (size (to_seq (support dy)))%r.
proof.
move => c s1 z0 c_valid s1_valid z0_valid.
rewrite /transz dmap1E /pred1 /(\o) /=.
rewrite (mu_eq _ _ (fun y => y + c ** s1 = z0)) => [y /#|].
rewrite (mu_eq_support _ _ (pred1 (z0 - c ** s1))) => [y supp_y /=|].
- rewrite /pred1 eq_iff; split.
  + move => <-.
    rewrite -addvA addvN size_scalarv.
    by rewrite addvC lin_add0v; smt(size_dvector).
  + move => ->.
    rewrite -addvA [_ + c ** _]addvC addvN size_scalarv addvC lin_add0v //.
    smt(size_dvector).
by rewrite mu1_uni_ll ?dy_uni ?dy_ll; smt(masking_range).
qed.

local lemma line12_outofbound :
  forall c s1 z0, c \in FSa.dC => s1 \in ds1 => z0 \notin dsimz =>
    (Some z0) \notin (transz c s1).
proof.
move => c s1 z0 c_valid s1_valid z0_invalid.
by rewrite supp_dmap => /#.
qed.

local lemma line12_magic_none :
  forall c s1, c \in FSa.dC => s1 \in ds1 =>
    mu1 (transz c s1) None = 1%r - (size (to_seq (support dsimz)))%r / (size (to_seq (support dy)))%r.
proof.
move => c s1 c_valid s1_valid.
have sumz : (sum (fun z => mu1 (transz c s1) z) = 1%r).
- by rewrite - weightE; apply dmap_ll; apply dy_ll.
rewrite sumD1_None /= in sumz.
- by apply summable_mu1.
suff: sum (fun (y : vector) => mu1 (transz c s1) (Some y)) = 
  (size (to_seq (support dsimz)))%r / (size (to_seq (support dy)))%r by smt().
(* bug: Doesn't let me do `suff {sumz}: ...` *)
clear sumz.
have -> :
  (fun z => mu1 (transz c s1) (Some z)) =
  (fun z => if z \in dsimz then 1%r / (size (to_seq (support dy)))%r else 0%r).
- apply fun_ext.
  smt(line12_magic_some supportPn line12_outofbound).
by rewrite sum_characteristic // is_finite_dsimz.
qed.

local lemma line12_magic c s1 :
  c \in FSa.dC => s1 \in ds1 =>
  transz c s1 = dsimoz.
proof.
move => c_valid s1_valid.
apply eq_distr => z; case z.
- rewrite line12_magic_none //.
  rewrite eq_sym dlet1E sum_over_bool /=.
  rewrite dmap1E /pred1 /(\o) mu0 /=.
  by rewrite dunit1E dbiased1E clamp_magic.
- move => z.
  case (z \in dsimz).
  + move => z_valid.
    rewrite line12_magic_some // dlet1E sum_over_bool /=.
    rewrite dunit1E /= dmap1E /pred1 /(\o) /=.
    rewrite dsimz1E //= dbiased1E /=. 
    rewrite clamp_magic; smt(mask_nonzero mask_size).
  + move => z_invalid.
    have -> : mu1 (transz c s1) (Some z) = 0%r by rewrite -supportPn line12_outofbound.
    rewrite eq_sym -supportPn supp_dlet.
    smt(supp_dmap supp_dunit).
qed.

local module HVZK_Hops = {
  (* Drop commitment *)
  proc game1(pk: PK, sk: SK) : (challenge_t * response_t) option = {
    var w, st, c, oz, r;
    (w, st) <$ commit sk;
    c <$ FSa.dC;
    oz <- respond sk c st;
    r <- omap (fun z => (c, z)) oz;
    return r;
  }

  (* unfold everything *)
  proc game2(pk: PK, sk: SK) : (challenge_t * response_t) option = {
    var mA, s1, s2, w', y, c, z, t, resp;
    var t0;

    (mA, s1, s2) <- sk;
    t <- mA *^ s1 + s2;
      t0 <- base2lowbitsV t;
    c <$ FSa.dC;
    y <$ dy;
    z <- y + c ** s1;
    if(z \in dsimz) {
      w' <- mA *^ y - c ** s2;
      resp <- if inf_normv (lowBitsV w') < gamma2 - beta_ then
        let h = makeHintV (- c ** t0) (mA *^ y - c ** s2 + c ** t0) in Some (z, h)
      else None;
    } else {
      resp <- None;
    }
    return omap (fun z => (c, z)) resp;
  }

  (* Compute w' using only public information *)
  proc game3(pk: PK, sk: SK) : (challenge_t * response_t) option = {
    var mA, s1, s2, w', y, c, z, t, resp;
    var t0;

    (mA, s1, s2) <- sk;
    t <- mA *^ s1 + s2;
    t0 <- base2lowbitsV t;
    c <$ FSa.dC;
    y <$ dy;
    z <- y + c ** s1;
    if(z \in dsimz) {
      w' <- mA *^ z - c ** t;
      resp <- if inf_normv (lowBitsV w') < gamma2 - beta_ then
        let h = makeHintV (- c ** t0) (w' + c ** t0) in Some (z, h)
      else None;
    } else {
      resp <- None;
    }
    return omap (fun z => (c, z)) resp;
  }

  (* Change conditional on `oz` *)
  proc game4(pk: PK, sk: SK) : (challenge_t * response_t) option = {
    var mA, s1, s2, w', y, c, z, t, resp;
    var oz, t0;

    (mA, s1, s2) <- sk;
    t <- mA *^ s1 + s2;
    t0 <- base2lowbitsV t;
    c <$ FSa.dC;
    y <$ dy;
    z <- y + c ** s1;
    oz <- if z \in dsimz then Some z else None;
    if(oz <> None) {
      z <- oget oz;
      w' <- mA *^ z - c ** t;
      resp <- if inf_normv (lowBitsV w') < gamma2 - beta_ then
        let h = makeHintV (- c ** t0) (w' + c ** t0) in Some (z, h)
      else None;
    } else {
      resp <- None;
    }
    return omap (fun z => (c, z)) resp;
  }

  (* Rewrite relevant parts of above as operator *)
  proc game5(pk: PK, sk: SK) : (challenge_t * response_t) option = {
    var mA, s1, s2, w', c, z, t, resp;
    var oz, t0;

    (mA, s1, s2) <- sk;
    t <- mA *^ s1 + s2;
    t0 <- base2lowbitsV t;
    c <$ FSa.dC;
    oz <$ transz c s1;
    if(oz <> None) {
      z <- oget oz;
      w' <- mA *^ z - c ** t;
      resp <- if inf_normv (lowBitsV w') < gamma2 - beta_ then
        let h = makeHintV (- c ** t0) (w' + c ** t0) in Some (z, h)
      else None;
    } else {
      resp <- None;
    }
    return omap (fun z => (c, z)) resp;
  }

  (* Get (a, t) from public key *)
  proc game6(pk: PK, sk: SK) : (challenge_t * response_t) option = {
    var mA, mA', s1, s2, w', c, z, t, resp;
    var oz, t0;

    (mA', s1, s2) <- sk;
    (mA, t) <- pk;
    t0 <- base2lowbitsV t;
    c <$ FSa.dC;
    oz <$ transz c s1;
    if(oz <> None) {
      z <- oget oz;
      w' <- mA *^ z - c ** t;
      resp <- if inf_normv (lowBitsV w') < gamma2 - beta_ then
        let h = makeHintV (- c ** t0) (w' + c ** t0) in Some (z, h)
      else None;
    } else {
      resp <- None;
    }
    return omap (fun z => (c, z)) resp;
  }

  (* simulator: dropping secret key *)
  proc game7(pk: PK) : (challenge_t * response_t) option = {
    var mA, w', c, z, t, resp;
    var oz, t0;

    (mA, t) <- pk;
    t0 <- base2lowbitsV t;
    c <$ FSa.dC;
    oz <$ dsimoz;
    if(oz <> None) {
      z <- oget oz;
      w' <- mA *^ z - c ** t;
      resp <- if inf_normv (lowBitsV w') < gamma2 - beta_ then
        let h = makeHintV (- c ** t0) (w' + c ** t0) in Some (z, h)
      else None;
    } else {
      resp <- None;
    }
    return omap (fun z => (c, z)) resp;
  }

  proc game8(pk: PK) : (challenge_t * response_t) option = {
    var mA, w', z, t, t0, resp, sample_z;
    var oz; (* only used for the proof *)
    var c <- witness;

    (mA, t) <- pk;
    t0 <- base2lowbitsV t;
    c <$ FSa.dC;
    sample_z <$ dbiased line12_magic_number;  
    z <$ dsimz;
    oz <- if sample_z then Some z else None;
    if(oz <> None) {
      z <- oget oz;
      w' <- mA *^ z - c ** t;
      resp <- if inf_normv (lowBitsV w') < gamma2 - beta_ then
        let h = makeHintV (- c ** t0) (w' + c ** t0) in Some (z, h)
      else None;
    } else {
      resp <- None;
    }
    return omap (fun z => (c, z)) resp;
  }

  proc game9(pk: PK) : (challenge_t * response_t) option = {
    var mA, w', z, t, t0, resp, sample_z;
    var c <- witness;

    (mA, t) <- pk;
    t0 <- base2lowbitsV t;
    sample_z <$ dbiased line12_magic_number;  
    if(sample_z) {
      c <$ FSa.dC;
      z <$ dsimz;
      w' <- mA *^ z - c ** t;
      resp <- if inf_normv (lowBitsV w') < gamma2 - beta_ then
        let h = makeHintV (- c ** t0) (w' + c ** t0) in Some (z, h)
      else None;
    } else {
      resp <- None;
    }
    return omap (fun z => (c, z)) resp;
  }
}.

local equiv hop2_correct pk_i sk_i :
  HVZK_Hops.game1 ~ HVZK_Hops.game2 :
  (pk_i, sk_i) \in keygen /\ arg{1} = (pk_i, sk_i) /\ arg{2} = (pk_i, sk_i) ==>
  ={res}.
proof.
case sk_i => mA' s1' s2'.
proc; inline*.
swap{1} 1 1.
swap{2} [1..3] 1.
seq 1 1: (#pre /\ ={c}); first by auto.
sp.
(* Sample `y` and discard unused `w` *)
seq 1 1: (#pre /\ st{1} = y{2} /\ size y{2} = l).
- rnd (fun wst => let (w, st) = wst in st) (fun y => (highBitsV (mA' *^ y), y)).
  auto => /> _.
  split.
  + move => y supp_y.
    rewrite /commit /= (dmap1E dy) /(\o).
    by apply mu_eq => ? /#.
  move => _ [w st] @/commit /= /supp_dmap [y [supp_y [??]]]; subst.
  smt(size_dvector Params.gt0_l).
(* suff: equality of oz *)
seq 1 2: (#pre /\ oz{1} = resp{2}); last by auto => /#. 
conseq />. 
auto => />; smt(sk_size size_addv size_scalarv supp_dsimz).
qed.

local equiv hop3_correct :
  HVZK_Hops.game2 ~ HVZK_Hops.game3 :
  ={arg} /\ arg{1} \in keygen ==> ={res}.
proof.
proc.
seq 6 6 : (#pre /\ ={mA, s1, s2, t, c, y, z, t0} /\
          mA{1} *^ y{1} - c{1} ** s2{1} = mA{2} *^ z{2} - c{2} ** t{2}); 
  last by auto => /#.
auto => /> &2 valid_key c c_valid y y_valid.
have: size (sk{2}.`1) = (k, l) /\ size (sk{2}.`2) = l /\ size (sk{2}.`3) = k.
- apply (sk_size (sk{2}.`1) (sk{2}.`2) (sk{2}.`3)).
  by exists pk{2} => /#.
(* Annoying proof of some simple vector calculations below... *)
case (sk{2}) => mA s1 s2 /= /> *.
rewrite mulmxvDr -addvA; congr.
rewrite mulmx_scalarv scalarvDr oppvD addvA addvN.
by rewrite lin_add0v // size_oppv !size_scalarv size_mulmxv /#.
qed.

local equiv hop4_correct :
  HVZK_Hops.game3 ~ HVZK_Hops.game4 :
  ={arg} ==> ={res}.
proof. proc; by auto => /#. qed.

local equiv hop5_correct pk_i sk_i :
  HVZK_Hops.game4 ~ HVZK_Hops.game5 :
  ={arg} /\ arg{1} = (pk_i, sk_i) /\ (pk_i, sk_i) \in keygen ==> ={res}.
proof.
proc.
seq 4 4: (#pre /\ ={mA, s1, s2, t, t0, c} /\ (mA{1}, s1{1}, s2{1}) = sk_i).
- by auto => /#.
seq 3 1: (#pre /\ ={oz}); last by sim.
rnd: *0 *0.
auto => /> &2.
case pk_i sk_i => [mA'' t'] [mA' s1' s2'] valid_keys.
have ?: size mA{2} = (k, l) /\ size s1{2} = l /\ size s2{2} = k.
- by apply sk_size; exists (mA'', t').
have [??]: mA'' = mA{2} /\ t' = mA{2} *^ s1{2} + s2{2}.
- by apply pk_decomp => //.
subst.
split => [oz oz_valid | _ oz oz_valid].
- by rewrite dmap_id /transz /#.
case /supp_dmap oz_valid => y [#] y_valid ? /=; subst.
by rewrite dmap_id supp_dmap /=; exists y.
qed.

local equiv hop6_correct pk_i sk_i :
  HVZK_Hops.game5 ~ HVZK_Hops.game6 :
  ={arg} /\ arg{1} = (pk_i, sk_i) /\ (pk_i, sk_i) \in keygen ==> ={res}.
proof.
proc.
seq 2 2: (#pre /\ ={mA, s1, s2, t} /\ mA{2} = mA'{2}); last by sim.
by auto => />; smt(pk_decomp).
qed.

local equiv hop7_correct pk_i sk_i :
  HVZK_Hops.game6 ~ HVZK_Hops.game7 :
  arg{1} = (pk_i, sk_i) /\ arg{2} = pk_i /\ (pk_i, sk_i) \in keygen ==> ={res}.
proof.
proc.
seq 2 1 : (#pre /\ ={mA, t} /\ mA{1} = mA'{1} /\ sk{1} = (mA'{1}, s1{1}, s2{1}) /\ pk{1} = (mA{1}, t{1})).
- by auto; smt(pk_decomp).
sp.
seq 1 1 : (#pre /\ ={c} /\ c{1} \in FSa.dC); first by auto.
seq 1 1 : (#pre /\ ={oz}); last by sim.
rnd; auto => //= &1 &2.
move => [#] ????? valid_keys ?????? c_valid ; subst.
rewrite line12_magic //.
by case /keygen_supp_decomp valid_keys.
qed.

local equiv hop8_correct pk_i sk_i :
  HVZK_Hops.game7 ~ HVZK_Hops.game8 :
  arg{1} = pk_i /\ arg{2} = pk_i /\ (pk_i, sk_i) \in keygen ==> ={res}.
proof.
proc.
seq 4 7 : (={mA,c,t,t0,oz}); last by sim.
sp; conseq />.
swap{1} 1 1; swap{2} 1 3; rnd.
conseq (: true ==> ={oz}); 1: smt().
rnd : *0 *0;skip. 
suff -> : dlet (dbiased line12_magic_number) 
               (fun b => dmap dsimz (fun z => if b then Some z else None)) = dsimoz.
- move => _ _ _; rewrite !andaE; do ! split => ?; by rewrite dmap_id. 
by apply in_eq_dlet => -[] //= _; apply/dmap_cst/dsimz_ll.
qed.

local equiv hop9_correct pk_i sk_i :
  HVZK_Hops.game8 ~ HVZK_Hops.game9 :
  arg{1} = pk_i /\ arg{2} = pk_i /\ (pk_i, sk_i) \in keygen ==> ={res}.
proof.
proc. 
swap{1} 4 1.
seq 4 4 : (={mA,t,t0,sample_z}); 1: by auto.
if{2}; first by rcondt{1} ^if; by auto => />.
rcondf{1} ^if; auto => />; smt(dsimz_ll).
qed.

local equiv KLS_HVZK pk sk :
  HVZK_Hops.game1 ~ HVZK_Hops.game9 :
  (pk, sk) \in keygen /\ arg{1} = (pk, sk) /\ arg{2} = pk ==>
  ={res}.
proof.
transitivity HVZK_Hops.game2
  ((pk, sk) \in Self.keygen /\ arg{1} = (pk, sk) /\ arg{2} = (pk, sk) ==> ={res})
  ((pk, sk) \in Self.keygen /\ arg{1} = (pk, sk) /\ arg{2} = pk ==> ={res}); 1, 2: smt().
- by conseq (hop2_correct pk sk) => /#.
transitivity HVZK_Hops.game3
  ((pk, sk) \in Self.keygen /\ arg{1} = (pk, sk) /\ arg{2} = (pk, sk) ==> ={res})
  ((pk, sk) \in Self.keygen /\ arg{1} = (pk, sk) /\ arg{2} = pk ==> ={res}); 1, 2: smt().
- by conseq hop3_correct => /#.
transitivity HVZK_Hops.game4
  ((pk, sk) \in Self.keygen /\ arg{1} = (pk, sk) /\ arg{2} = (pk, sk) ==> ={res})
  ((pk, sk) \in Self.keygen /\ arg{1} = (pk, sk) /\ arg{2} = pk ==> ={res}); 1, 2: smt().
- by conseq hop4_correct => /#.
transitivity HVZK_Hops.game5
  ((pk, sk) \in Self.keygen /\ arg{1} = (pk, sk) /\ arg{2} = (pk, sk) ==> ={res})
  ((pk, sk) \in Self.keygen /\ arg{1} = (pk, sk) /\ arg{2} = pk ==> ={res}); 1, 2: smt().
- by conseq (hop5_correct pk sk) => /#.
transitivity HVZK_Hops.game6
  ((pk, sk) \in Self.keygen /\ arg{1} = (pk, sk) /\ arg{2} = (pk, sk) ==> ={res})
  ((pk, sk) \in Self.keygen /\ arg{1} = (pk, sk) /\ arg{2} = pk ==> ={res}); 1, 2: smt().
- by conseq (hop6_correct pk sk) => /#.
transitivity HVZK_Hops.game7
  ((pk, sk) \in Self.keygen /\ arg{1} = (pk, sk) /\ arg{2} = pk ==> ={res})
  ((pk, sk) \in Self.keygen /\ arg{1} = pk /\ arg{2} = pk ==> ={res}); 1, 2: smt().
- by conseq (hop7_correct pk sk) => /#.
transitivity HVZK_Hops.game8
  ((pk, sk) \in Self.keygen /\ arg{1} = pk /\ arg{2} = pk ==> ={res})
  ((pk, sk) \in Self.keygen /\ arg{1} = pk /\ arg{2} = pk ==> ={res}); 1, 2: smt().
- by conseq (hop8_correct pk sk) => /#.
by conseq (hop9_correct pk sk) => /#.
qed.

equiv HVZK_Sim_correct k :
  DID.Honest_Execution(OpBased.P, OpBased.V).get_trans ~ HVZK_Sim_Inst.get_trans :
  k \in keygen /\ arg{1} = k /\ arg{2} = k.`1 ==> ={res}.
proof.
case k => pk_i sk_i.
pose drop_commitment (wcz : commit_t * challenge_t * response_t) := (wcz.`2, wcz.`3).
(* Commitment recoverable - can drop the commitment *)
conseq 
  (_: (pk_i, sk_i) \in keygen /\ arg{1} = (pk_i, sk_i) /\ arg{2} = pk_i ==>
      omap drop_commitment res{1} = omap drop_commitment res{2})
  (_: arg = (pk_i, sk_i) /\ (pk, sk) \in keygen ==>
      res <> None => let (w, c, z) = oget res in w = (recover pk_i c z))
  (_: arg = pk_i ==>
      res <> None => let (w, c, z) = oget res in w = (recover pk_i c z)); 1, 2: smt().
- by conseq (recover_correct pk_i sk_i).
- proc; conseq (_ : _ ==> pk = pk_i); [ by auto => /> /# | by conseq /> ]. 
(* left hand side equiv to KLS HVZK first game *)
transitivity HVZK_Hops.game1
 ((pk_i, sk_i) \in keygen /\ arg{1} = (pk_i, sk_i) /\ arg{2} = (pk_i, sk_i) ==>
   omap drop_commitment res{1} = res{2})
 ((pk_i, sk_i) \in keygen /\ arg{1} = (pk_i, sk_i) /\ arg{2} = pk_i ==>
   res{1} = omap drop_commitment res{2}); 1, 2: smt().
 - by proc; inline *; auto => /#.
(* right hand side equiv to KLS HVZK final game *)
transitivity HVZK_Hops.game9
  ((pk_i, sk_i) \in keygen /\ arg{1} = (pk_i, sk_i) /\ arg{2} = pk_i ==> ={res})
  ((pk_i, sk_i) \in keygen /\ arg{1} = pk_i /\ arg{2} = pk_i ==>
   res{1} = omap drop_commitment res{2}); 1, 2: smt().
- by conseq (KLS_HVZK pk_i sk_i).
proc.
sim : (={pk, c, resp}); smt().
qed.

lemma pr_HonestExecution_Sim &m p pk sk : (pk,sk) \in keygen =>
  Pr[DID.Honest_Execution(P, V).get_trans(pk, sk) @ &m : p res] = 
  Pr[HVZK_Sim_Inst.get_trans(pk) @ &m : p res].
proof.
move => pk_sk; byequiv => //. 
by conseq (HVZK_Sim_correct (pk,sk)) => />.
qed.

local module HE = { 
  proc sample(sk) = { 
    var x;
    x <$ (commit sk `*` dC tau);
    return respond sk x.`2 x.`1.`2;
  } 
}. 


lemma pr_HonestExecution_op pk sk &m :
  (pk,sk) \in keygen =>  
  Pr[DID.Honest_Execution(P, V).get_trans(pk,sk) @ &m : res = None] = 
  mu (commit sk `*` dC tau) 
     (fun (x : (ID.W * ID.Pstate) * ID.C) => respond sk x.`2 x.`1.`2 = None).
proof.
move => Hpk. 
have -> : Pr[DID.Honest_Execution(P, V).get_trans(pk, sk) @ &m : res = None] = 
          Pr[HVZK_Hops.game1(pk,sk) @ &m : res = None]. 
- byequiv (: ={arg} /\ arg{1} \in keygen ==> res{1} = None <=> res{2} = None) => //.
  proc; inline*; auto => /> /#.
have <- : Pr[HE.sample(sk) @ &m : res = None] = 
          mu (commit sk `*` dC tau)
             (fun (x : (ID.W * ID.Pstate) * ID.C) => respond sk x.`2 x.`1.`2 = None).
- byphoare (: arg = sk ==> _) => //; proc; rnd; skip => &hr />. 
byequiv (_: arg.`2{1} = arg{2} ==> res{1} = None <=> res{2} = None) => //.
proc; wp. 
conseq (: _ ==> ((w,st),c){1} = x{2}); 1: smt().
rnd (fun wsc : high list * pstate_t * challenge_t => ((wsc.`1,wsc.`2),wsc.`3))
    (fun wsc : (high list * pstate_t) * challenge_t => (wsc.`1.`1,wsc.`1.`2,wsc.`2)) : *0 *0.
skip => &1 &2; rewrite !andaE => *; do ! split. 
- smt().
- case => -[] /= w1 y c ?. rewrite dprod_dlet dmap_dlet /=. 
  rewrite !dlet1E; congr; apply/fun_ext => -[w1' y'] /=; congr; 1: smt().
  rewrite !dmapE /(\o) /=. by apply mu_eq => /> /#.
- case => w1 y c /=.
  case/supp_dlet => -[w1' y'] [? /supp_dmap [c']] /> ?. 
  apply/supp_dmap; exists ((w1',y'),c'); smt(supp_dprod).
qed.

end section OpBasedHVZK.


op ll_dflt (d : 'a distr) : 'a = choiceb (support d) witness.
lemma ll_dfltP (d : 'a distr) : is_lossless d => ll_dflt d \in d.
proof. 
move => d_ll; apply: (choicebP (fun x => x \in d) witness) => /=.
move: d_ll. rewrite /is_lossless weightE_support.
apply absurd => /= ?; rewrite mu0_false /#.
qed.


(******************************************************)
(****  Instantiation of the CMA to NMA reduction ******)
(******************************************************)

(** We require a check on the matrix component of public and secrect
key that ensures:

- sufficiently high commitment entropy
- sufficiently high probability that respond succeeds *)

(* Check that ensures that the matrix is "entropy preserving" *)
(* (and has the right dimensions)                             *)
op check_mx : matrix -> bool.

axiom check_valid A : check_mx A => A \in dA.

(* upper bound on the mass of the most likely commitment for a good key *)
const eps_comm  : { real | 0%r < eps_comm } as eps_comm_gt0.

op A0 : { matrix | check_mx A0 } as A0P.

axiom check_mx_entropy : 
  E (dcond dA check_mx) (fun mA => 
    p_max (dmap dy (fun y => highBitsV (mA *^ y)))) <= eps_comm.


(* upper bound on the mass of the keys not passing check *)
const eps_check : { real | 0%r <= eps_check }  as eps_check_gt0.

axiom check_mx_most : mu dA (predC check_mx) <= eps_check.


(* bound on the probability that he low-bis check in the Sim fails *)

op dz = dvector (dRq_ (gamma1 - beta_ - 1)) l.
const eps_low : { real | eps_low < 1%r } as eps_low_lt1.

axiom bound_low c (t : vector) (mA : matrix) :
  c \in dC tau => t \in dvector dRq k => check_mx mA =>
  mu dz (fun z => gamma2 - beta_ <= inf_normv (lowBitsV (mA *^ z - c ** t)) ) <= eps_low. 


(* From the assumptions above, we can derive the assumptions of the
CMA to NMA reduction: *)

op p_rej = line12_magic_number * eps_low + (1%r - line12_magic_number).

lemma gt0_magic_number : 0%r < line12_magic_number.
proof.
suff: 0 < size (to_seq (support dsimz)) /\ 0 < size (to_seq (support dy)) by smt().
rewrite !gt0_dRq_vect; smt(Params.gt0_l gt0_beta beta_gamma1_lt).
qed.

lemma p_rej_bounded : 0%r <= p_rej < 1%r.
have ? : 0%r < line12_magic_number <= 1%r.
- rewrite gt0_magic_number /= /line12_magic_number.
  suff: 0 < size (to_seq (support dy)) by smt(mask_size size_ge0).
  apply gt0_dRq_vect; smt(Params.gt0_l beta_gamma1_lt gt0_beta).
suff: 0%r <= eps_low < 1%r by smt().
rewrite eps_low_lt1 /=.
pose c0 := ll_dflt (dC tau).
pose t0 := ll_dflt (dvector dRq k).
suff: mu dz (fun z => gamma2 - beta_ <= inf_normv (lowBitsV (A0 *^ z - c0 ** t0))) <= eps_low.
- smt(ge0_mu).
apply bound_low.
- by rewrite ll_dfltP dC_ll.
- by rewrite ll_dfltP dvector_ll dRq_ll.
- exact A0P.
qed.

(* op valid_sk sk = exists pk, (pk,sk) \in keygen. *)

(* a check for "good" secret keys (i.e, well-formed and high entropy) *)
op check (sk : SK) : bool = check_mx (sk.`1) /\ sk.`2 \in ds1 /\ sk.`3 \in ds2.

import StdBigop.Bigreal.BRA.
import StdOrder.RealOrder.

lemma dmap_keygen : dmap keygen (fun (k : PK * SK) => k.`2.`1) = dA.
proof.
have ds1_ll : is_lossless ds1 by apply/dvector_ll/dRq__ll.
have ds2_ll : is_lossless ds2 by apply/dvector_ll/dRq__ll.
apply eq_distr => mA. rewrite dmap1E. 
rewrite /keygen -/dA -dmapE dmap_dlet /= dletEunit // => {mA} mA.
rewrite dmap_dlet; apply dletEconst => //= s1.
by rewrite dmap_comp /dmap; apply dletEconst.
qed.

(* The expected entropy, conditioned on the SK passing the check, is high *)
lemma check_entropy: E (dcond keygen (fun k : (PK * SK) => check k.`2))
                          (fun (k : PK * SK) =>
                             p_max (dfst ((commit k.`2)))) <= eps_comm.
proof.
apply: StdOrder.RealOrder.ler_trans check_mx_entropy.
pose g (mA : matrix) := p_max (dmap dy (fun (y : vector) => highBitsV (mA *^ y))).
pose f (k : PK * SK) := k.`2.`1.
have -> : (fun (k : PK * SK) => p_max (dfst ((commit k.`2)))) = g \o f. 
  apply/fun_ext => -[pk [A s1 s2]] @/(\o) @/f @/g @/commit /=.
  by rewrite dmap_comp.
rewrite -exp_dmap. 
- pose d := dmap _ _; rewrite /hasE. 
  rewrite (eq_summable _ (fun x => mu1 d x * g x)) 1:/#. 
  apply/summable_mu1_wght; smt(ge0_pmax le1_pmax).
apply lerr_eq; congr; apply/eq_distr => mA. 
rewrite (eq_dcond _ _ (check_mx \o f)); 1: smt(keygen_supp_decomp).
by rewrite dmap_dcond dmap_keygen.
qed.

(* most honestly sampled secret keys pass the check *)
lemma check_most : mu keygen (fun k : PK * SK => !check k.`2) <= eps_check.
proof.
apply: StdOrder.RealOrder.ler_trans check_mx_most.
rewrite (mu_eq_support _ _ ((predC check_mx) \o (fun k : PK*SK => k.`2.`1))). 
  smt(keygen_supp_decomp).
by rewrite -dmapE (mu_eq_l dA) // dmap_keygen.
qed.

lemma get_pk (sk : SK) : check sk => exists pk, (pk,sk) \in keygen.
proof.
case: sk => mA s1 s2 [|> chk_mA s1_d s2_d]; exists (mA,mA *^ s1 + s2).
rewrite supp_dlet; exists mA; rewrite check_valid //=.
rewrite supp_dlet; exists s1; rewrite s1_d //=.
by rewrite supp_dmap; exists s2; rewrite s2_d.
qed.

(* probability that response fails on "good" keys is bounded by p_rej *)
lemma rej_bound (sk : SK) :
  check sk =>
  mu (commit sk `*` dC tau) 
     (fun (x : (ID.W * ID.Pstate) * ID.C) => respond sk x.`2 x.`1.`2 = None) <= p_rej.
proof.
move => chk_sk; have [pk pk_sk] := get_pk _ chk_sk.
(* TODO: use [pose &m] once this has been merged *)
have [&m _] : exists &m, true by smt(). 
have /= <- := pr_HonestExecution_op pk sk &m pk_sk. 
have -> := pr_HonestExecution_Sim &m (pred1 None) pk sk pk_sk.
have [A' t' [def_pk chk_A]] : exists A t, pk = (A,t) /\ check_mx A; 2: subst.
  case: pk pk_sk => A t pk_sk; exists A t => /=. smt(pk_decomp).  
byphoare (: arg = (A',t') ==> _) => //; proc.
conseq (: _ ==> resp = None); 1: smt().
seq 4 : (sample_z) line12_magic_number eps_low (1%r - line12_magic_number) 1%r 
        (mA = A' /\ t = t'). 
- by auto.
- rnd. auto => _ _. by rewrite dbiasedE /= clamp_magic.
- rcondt ^if; 1: by auto. 
  wp; conseq (: _ ==> gamma2 - beta_ <= inf_normv (lowBitsV (mA *^ z - c ** t))); 1: smt().
  rnd. auto => /> &1 _ c c_dC. apply bound_low => //. 
  rewrite supp_dvector ?ltzW ?gt0_k; move/size_t : pk_sk; smt(dRq_fu).
- rnd; auto => _ _. by rewrite dbiasedE /= clamp_magic.
- by auto.
- done.
qed.

lemma keygen_finite : is_finite (support keygen).
proof.
apply finite_dlet => [|mA ? /=]; first exact/uniform_finite/dmatrix_uni/dRq_uni.
apply finite_dlet => [|s1 ? /=]; first exact/uniform_finite/dvector_uni/dRq__uni.
apply finite_dlet; first exact/uniform_finite/dvector_uni/dRq__uni.
by move => s2 ? @/(\o); exact finite_dunit.
qed.

import FSaCR.DSS.
import FSaCR.DSS.PRO.
import FSaCR.DSS.DS.Stateless.
import FSaCR.DSS.EFCMA.

(* Distinguisher for (RO) signature schemes *)
module type SigDist (S : Scheme) (H : Hash_i) = { 
  proc distinguish() : bool
}.


equiv eqv_code_op (D <: SigDist{-OpBasedSig}) (H <: Hash_i{-OpBased.P,-D}) : 
  D(SimplifiedDilithium(H),H).distinguish ~ D(OpBasedSig(H),H).distinguish : 
  ={glob D,glob H} ==> ={glob D,glob H,res}.
proof.
proc*; call (: ={glob H}); last done.
- proc true; auto.
- proc true; auto.
- by symmetry; conseq (keygen_opbased_correct H) => //.
- by symmetry; conseq (sign_opbased_correct H) => /#.
- by symmetry; conseq (verify_opbased_correct H) => /#.
qed.

clone Generic as FSaG with
  op qS <= qS,
  op qH <= qH + Self.qS
proof* by smt(qS_ge0 qH_ge0). 

(* Generic FS+abort transform of the OpBased ID scheme *)
module OpBasedSigG     = FSaG.IDS_Sig(OpBased.P,OpBased.V).
module O_CMA_Default_G = FSaG.DSS.DS.Stateless.O_CMA_Default.
module RO_G            = FSaG.DSS.PRO.RO.

module EF_CMA_RO_G = FSaG.DSS.EF_CMA_RO.
module EF_KOA_RO_G = FSaG.DSS.EF_KOA_RO.

clone FSa_CRtoGen as CG with
  theory FSa <- FSa,
  theory FSaCR <- FSaCR,
  theory FSaG <- FSaG. 

clone import FSa_CMAtoKOA as CMAtoKOA with
  theory FSa <- FSa,
  theory FSaG <- FSaG,
  theory OP <- OpBased,
  op p_rej <- p_rej,
  op check_entropy <- check,
  op alpha <- eps_comm,
  op gamma <- eps_check
proof *. 
realize alpha_gt0 by apply eps_comm_gt0.
realize gamma_gt0 by apply eps_check_gt0.
realize check_entropy_correct by apply check_entropy.
realize most_keys_high_entropy by apply check_most.
realize p_rej_bounded by smt(p_rej_bounded).
realize rej_bound by apply rej_bound.
realize keygen_finite by apply keygen_finite.

module (RedCR (A : Self.FSaG.DSS.Adv_EFKOA_RO) : Adv_EFKOA_RO) (H : Hash) = { 
  proc forge (pk : PK) : M*Sig = { 
    var m,sig,w,z,c;
    (m,sig) <@ A(H).forge(pk);
    (w,z) <- sig;
    c <@ H.get(w,m);
    return (m,(c,z));
  }
}.

module RedNMA(A : Adv_EFCMA_RO) = RedCR(RedKOA(CG.RedFSaG(A),HVZK_Sim_Inst)).

require import SmtMap.


module CountS (O : SOracle_CMA) = { 
  var qs : int
  proc init() = { qs <- 0; }

  proc sign (m : M) = { 
    var s;
    qs <- qs + 1;
    s <@ O.sign(m);
    return s;
  } 
}.

module CountH (H : Hash) = { 
  var qh : int
  proc init() = { qh <- 0; }

  proc get (w,m) = { 
    var c;
    qh <- qh + 1;
    c <@ H.get(w,m);
    return c;
  } 
}.


(*************************)
(****  Main Theorem ******)
(*************************)


section PROOF.

declare module A <: Adv_EFCMA_RO{
  -O_CMA_Default,-H,-OpBasedSig,
  -O_CMA_Default_G, -RO_G, -OpBasedSigG,
  -ORedKOA,-CMAtoKOA.CountS,-CMAtoKOA.CountH,
  -CountS,-CountH,
  -G
}.

(* A makes at most qS queries to [sign] and at most qH queries to [H.get] *)
declare axiom A_bound
 (H' <: Hash{-A,-CountH,-CountS}) 
 (SO' <: SOracle_CMA{-A,-CountH, -CountS})
 :
 hoare[ A(CountH(H'),CountS(SO')).forge :
        CountH.qh = 0 /\ CountS.qs = 0 ==>
        CountH.qh <= qH /\ CountS.qs <= qS].

(* The adversary will output a forgery attempt, procided all oracle calls terminate *)
declare axiom A_ll
 (SO <: SOracle_CMA{-A})
 (H <: Hash{-A}) :
 islossless SO.sign => islossless H.get => islossless A(H,SO).forge.

(*** Step 1 : Replace the code-based scheme with an operator-based one ***)

(* EF_CMA game seen as a distinshuisher for signature schemes *) 
local module (SD : SigDist) (S : Scheme) (H : Hash_i) = { 
  proc distinguish() = {
    var r;
    H.init();
    r <@ EF_CMA(S,A(H),O_CMA_Default).main();
    return r;
  }
}.

local lemma pr_code_op &m : 
  Pr [ EF_CMA_RO(SimplifiedDilithium, A, RO,O_CMA_Default).main() @ &m : res ] = 
  Pr [ EF_CMA_RO(OpBasedSig, A, RO,O_CMA_Default).main() @ &m : res ].
proof.
byequiv (_: ={glob A,glob RO,glob O_CMA_Default} ==> ={res}) => //; proc*.
transitivity*{1} { r <@ SD(SimplifiedDilithium(RO),RO).distinguish();}; 1,2:smt();
  first by sim.
transitivity*{2} { r <@ SD(OpBasedSig(RO),RO).distinguish();}; 1,2: smt(); 
  last by sim.
by call (eqv_code_op SD RO).
qed.


(*** Step 2 : Reduce to the case for general (i.e., not commitment recoverable schemes) ***)

local lemma pr_cr_gen &m : 
  Pr [ EF_CMA_RO  (OpBasedSig , A            , RO, O_CMA_Default).main() @ &m : res ] <=
  Pr [ EF_CMA_RO_G(OpBasedSigG, CG.RedFSaG(A), RO_G, O_CMA_Default_G).main() @ &m : res ].
proof.
have H := CG.FSa_CommRecov_Generic OpBased.P OpBased.V _ A &m; 1: by islossless.
exact (StdOrder.RealOrder.ler_trans _ _ _ H).
qed.

(*** Step 3 : Instantiate the CMA to KOA reduction *)

(* Counting wrapper for adversaries*)

local module Wrap(A : Adv_EFCMA_RO,H : Hash,O : SOracle_CMA) = { 
  proc forge(pk) = { 
    var r; 
    CountH.qh <- 0;
    CountS.qs <- 0;
    r <@ A(CountH(H),CountS(O)).forge(pk);
    return r;
  }
}.

(* NOTE: We would like to prove A(H,O).forge ~ Wrap(A,H,O).forge for
any A, H, and O that does not access the counters. However, expressing
the distinguishing contexts naively leads to a higher-order module
type.

  local module type AdvDist (A : Adv_EFCMA_RO) = {
    proc distinguish () : bool 
  }.

However, the rules for (abstract) higher-oder functors do not allow
the provided functor (i.e., A) to call its argument modules. So this
is useless. Unfortunately, even the first-order version does not work: 

  local equiv count_A (H' <: Hash{-A,-CountH,-CountS}) 
                      (O' <: SOracle_CMA{-A,-CountH, -CountS}) : 
    A(H',O').forge ~ Wrap(A,H',O').forge : 
    ={arg, glob A,glob H',glob O'} ==> ={glob A,glob H',glob O',res}.

The problem is that the call rule for abstract A requires the abstract
arguments H' and O' to have disjoint memories. This is not the case
for the instances we are interested in. However, we can prove a
variant where H' and O' are projections of a single module and use
this to prove the instances we need. *)

local module type HO = { 
  include Hash
  include SOracle_CMA
}.

local module H_ (HO:HO) : Hash = { proc get = HO.get }.
local module SOracle_ (HO:HO) : SOracle_CMA = { proc sign = HO.sign }.

local module HO(H:Hash,O:SOracle_CMA) : HO = { 
  proc get = H.get 
  proc sign = O.sign
}.
  
local equiv Wrap_A_HO (HO <: HO{-A,-CountH,-CountS}) : 
  A(H_(HO),SOracle_(HO)).forge ~ Wrap(A,H_(HO),SOracle_(HO)).forge : 
  ={arg,glob A,glob HO} ==> ={glob A,glob HO,res}.
proof.
proc*; inline*; wp; sp. call (: ={glob HO}). 
- by proc*; inline*; wp; call (: true); auto.
- by proc*; inline*; wp; call (: true); auto.
by auto => />.
qed.

(* This is still not provable, but maybe it should be
local equiv Wrap_A (H' <: Hash{-A,-CountH,-CountS}) 
                   (O' <: SOracle_CMA{-A,-CountH, -CountS}) : 
  A(H',O').forge ~ Wrap(A,H',O').forge : 
  ={arg, glob A,glob H',glob O'} ==> ={glob A,glob H',glob O',res}.
proof.
have X /= := Wrap_A_HO (<: HO(H',O')). 
(* transitivity A(H_(HO(H', O')), SOracle_(HO(H', O'))).forge *)
(*   (={glob A, glob H', glob O'} ==> ={glob A, glob H', glob O', res}) *)
(*   (={glob A, glob H', glob O'} ==> ={glob A, glob H', glob O', res}). *)
abort. 
*)

local module B = RedKOA(CG.RedFSaG(A),HVZK_Sim_Inst).

section.
import Self.FSaG.
import Self.FSaG.DSS.
import Self.FSaG.DSS.PRO.
import Self.FSaG.DSS.DS.Stateless.

(* Instances of the wrap lemma *)
local equiv wrap1 : 
  A      (RO, CG.OCR(RO, O_CMA_Default(IDS_Sig(P, V, RO)))).forge ~
  Wrap(A, RO, CG.OCR(RO, O_CMA_Default(IDS_Sig(P, V, RO)))).forge :
  ={arg, glob A, glob RO, glob CG.OCR(RO, O_CMA_Default(IDS_Sig(P, V, RO)))} ==>
  ={glob A, glob RO, glob CG.OCR(RO, O_CMA_Default(IDS_Sig(P, V, RO))), res}.
proof.
have X := Wrap_A_HO (<: HO(RO,CG.OCR(RO, O_CMA_Default(IDS_Sig(P, V, RO))))).
proc*.
transitivity*{1} { 
  r <@ A(H_(HO(RO, CG.OCR(RO, O_CMA_Default(IDS_Sig(P, V, RO))))), 
   SOracle_(HO(RO, CG.OCR(RO, O_CMA_Default(IDS_Sig(P, V, RO)))))).forge(pk); }; 
  1,2: smt();1: sim. 
transitivity*{2} { 
  r <@ Wrap(A, H_(HO(RO, CG.OCR(RO, O_CMA_Default(IDS_Sig(P, V, RO))))), 
         SOracle_(HO(RO, CG.OCR(RO, O_CMA_Default(IDS_Sig(P, V, RO)))))).forge(pk); }; 
  1,2:smt(); 2: sim.
call X; auto => />.
qed.

local equiv wrap2 : 
        A(RedKOA_H'(RO), CG.OCR(RedKOA_H'(RO), ORedKOA(HVZK_Sim_Inst))).forge ~
  Wrap(A, RedKOA_H'(RO), CG.OCR(RedKOA_H'(RO), ORedKOA(HVZK_Sim_Inst))).forge :
  ={arg, glob A, glob RedKOA_H'(RO), glob CG.OCR(RedKOA_H'(RO), ORedKOA(HVZK_Sim_Inst))} ==>
  ={glob A, glob RedKOA_H'(RO), glob CG.OCR(RedKOA_H'(RO), ORedKOA(HVZK_Sim_Inst)), res}.
proof.
have X := Wrap_A_HO (<: HO(RedKOA_H'(RO), CG.OCR(RedKOA_H'(RO), ORedKOA(HVZK_Sim_Inst)))).
proc*.
transitivity*{1} { 
  r <@ A(H_(HO(RedKOA_H'(RO), CG.OCR(RedKOA_H'(RO), ORedKOA(HVZK_Sim_Inst)))), 
   SOracle_(HO(RedKOA_H'(RO), CG.OCR(RedKOA_H'(RO), ORedKOA(HVZK_Sim_Inst))))).forge(pk); }; 
  1,2: smt();1: sim. 
transitivity*{2} { 
  r <@ Wrap(A, H_(HO(RedKOA_H'(RO), CG.OCR(RedKOA_H'(RO), ORedKOA(HVZK_Sim_Inst)))), 
         SOracle_(HO(RedKOA_H'(RO), CG.OCR(RedKOA_H'(RO), ORedKOA(HVZK_Sim_Inst))))).forge(pk); }; 
1,2:smt(); 2: sim.
call X; auto => />.
qed.

  
lemma pr_cma_koa &m : 
  Pr [ EF_CMA_RO_G(OpBasedSigG, CG.RedFSaG(A), RO_G, O_CMA_Default_G).main() @ &m : res ] <= 
  Pr [ EF_KOA_RO_G(OpBasedSigG, RedKOA(CG.RedFSaG(A),HVZK_Sim_Inst),RO_G).main() @ &m : res ] + 
  reprog_bound + eps_check.
proof.
have H := CMAtoKOA.FSabort_bound (CG.RedFSaG(Wrap(A))) _ _ HVZK_Sim_Inst _ &m; first last.
- move => Hx Ox ? ?. islossless. 
  apply (A_ll (<:CountS(CG.OCR(Hx, Ox))) (CountH(Hx))); islossless.
- exact HVZK_Sim_correct.
- (* This is the same up to [Wrap] which introduces a counter that's never checked *)
  have -> : Pr[EF_CMA_RO_G(OpBasedSigG, CG.RedFSaG(A), RO_G, O_CMA_Default_G).main() @ &m : res ]= 
            Pr[EF_CMA_RO_G(OpBasedSigG, CG.RedFSaG(Wrap(A)), RO_G, O_CMA_Default_G).main() @ &m : res ].
  + byequiv (_: ={glob A,glob RO_G, glob O_CMA_Default_G, glob P} ==> ={res}) => //.
    proc. inline{1}2; inline{2} 2. 
    seq 4 4 : (={pk,m,sig,RO.m,O_CMA_Default.qs}); last by sim.
    inline{1}4; inline{2}4. wp. 
    by call wrap1; inline*; auto => />.
  apply (StdOrder.RealOrder.ler_trans _ _ _ H); rewrite !StdOrder.RealOrder.ler_add2r.
  byequiv (_: ={glob A,glob RO_G, glob P} ==> ={res}) => //. symmetry.
  proc. inline{1}2; inline{2} 2. 
  seq 3 3 : (={pk,m,sig,RO.m}); last by sim.
  inline{1}3; inline{2}3.  inline{1}5; inline{2}5. wp.
  by call wrap2; inline*; auto => />.
(* Query bound for RedFSaG *)
move => Ox Hx; proc; wp. 
(* go back to procedure judgment *)
inline *; sp; wp.
conseq (_: CountH.qh + CountS.qs = CMAtoKOA.CountH.qh /\ CountS.qs = CMAtoKOA.CountS.qs)
       (_: CountH.qh = 0 /\ CountS.qs = 0 ==> CountH.qh <= qH /\ CountS.qs <= qS); 1,2: smt().
  by call (A_bound (<: CMAtoKOA.CountH(Hx)) (<: CG.OCR(CMAtoKOA.CountH(Hx), CMAtoKOA.CountS(Ox)))).
call (: CountH.qh + CountS.qs = CMAtoKOA.CountH.qh /\ CountS.qs = CMAtoKOA.CountS.qs).
- proc. inline*. wp. call(: true). wp. call(: true). auto => /> /#.
- proc. inline*; wp; call(: true); auto => /> /#.
- by auto.
qed.

end section.

(*** Step 4 : Go back to the KOA propblem for the CR transform *)

local lemma verify_recover pk w c z : 
  verify pk w c z => recover pk c z = w.
proof. rewrite /verify /recover. smt(). qed.

local lemma pr_koa_cr &m (B <: Self.FSaG.DSS.Adv_EFKOA_RO{-RO.m, -Self.FSaG.DSS.PRO.RO}) : 
  Pr [ EF_KOA_RO_G(OpBasedSigG, B,RO_G).main() @ &m : res ] <= 
  Pr [ EF_KOA_RO(OpBasedSig,RedCR(B),RO).main() @ &m : res].
proof.
byequiv => //; proc. 
inline{1}2; inline{2}2. inline{2}3.
seq 3 4 : (={pk} /\ m{1} = m0{2} /\ sig{1} = sig0{2} /\ Self.FSaG.DSS.PRO.RO.m{1} = RO.m{2}). 
- inline*. 
  call(: Self.FSaG.DSS.PRO.RO.m{1} = RO.m{2}); [by proc;inline*; auto| by auto].
wp.
inline{1} 1. inline{2} 4. wp. sp. 
seq 1 1 : (#pre /\ ={c} /\ (RO.m.[w,m0] = Some c){2}).
- inline*; conseq />; auto => />; smt(get_setE).
inline V.verify. sp.
inline RO.get. 
case (result{1}); last by conseq (:_ ==> true); [smt()|islossless].
rcondf{2} ^if; 1: by move => &h; auto => &h' />; smt(verify_recover).
rcondt{2} ^if; 1: by move => &h; auto => &h' />; smt(verify_recover).
auto => />; smt(verify_recover).
qed.

(* Step 5 : Go back to the Code-Based Scheme used for the NMA proof *)

local module (SD' : SigDist) (S : Scheme) (H : Hash_i) = { 
  proc distinguish() = {
    var r;
    H.init();
    r <@ EF_KOA(S,RedCR(B,H)).main();
    return r;
  }
}.

local lemma pr_code_op' &m : 
  Pr [ EF_KOA_RO(SimplifiedDilithium,RedCR(B),RO).main() @ &m : res ] = 
  Pr [ EF_KOA_RO(OpBasedSig, RedCR(B),RO).main() @ &m : res ].
proof.
byequiv (_: ={glob A,glob RO,glob ORedKOA} ==> ={res}) => //; proc*.
transitivity*{1} { r <@ SD'(SimplifiedDilithium(RO),RO).distinguish();}; 1,2:smt();
  first by sim.
transitivity*{2} { r <@ SD'(OpBasedSig(RO),RO).distinguish();}; 1,2: smt(); 
  last by sim.
by call (eqv_code_op SD' RO). 
qed.

lemma SimplifiedDilithium_secure &m : 
  Pr [EF_CMA_RO(SimplifiedDilithium, A, RO,O_CMA_Default).main() @ &m : res ] <= 
    `|Pr[GameL(RedMLWE(RedNMA(A), RO)).main() @ &m : res] -
      Pr[GameR(RedMLWE(RedNMA(A), RO)).main() @ &m : res]|
  + Pr[Game(RedMSIS(RedNMA(A)), G).main() @ &m : res] 
  + (2%r * qS%r * (qH + qS + 1)%r * eps_comm / (1%r - p_rej) +
     qS%r * eps_comm * (qS%r + 1%r) / (2%r * (1%r - p_rej) ^ 2))
  + eps_check.
proof.
rewrite pr_code_op.
apply (StdOrder.RealOrder.ler_trans _ _ _ (pr_cr_gen &m)).
apply (StdOrder.RealOrder.ler_trans _ _ _ (pr_cma_koa &m)).
rewrite !StdOrder.RealOrder.ler_add2r.
apply (StdOrder.RealOrder.ler_trans _ _ _ (pr_koa_cr &m B)).
rewrite -pr_code_op'.
exact (StdOrder.RealOrder.ler_trans _ _ _ (KOA_bound (RedCR(B)) &m)). 
qed.

end section PROOF.
