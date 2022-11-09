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

(* Parameters of the security games *)
const qS : int. (* allowed number of sig queries *)
const qH : int. (* allowed number of ro  queries *)
axiom qS_ge0 : 0 <= qS.
axiom qH_ge0 : 0 <= qH.

(* Dilithium-specific parameters *)

(* secret key range.
 * Typically "eta" but that's a reserved keyword in EC. *)
op e : {int | 0 < e} as gt0_eta.

(* upper bound on number of itertions. *)
(* op kappa : { int | 0 < kappa } as gt0_kappa. *)

(* matrix dimensions *)
op k : {int | 0 < k} as gt0_k.
op l : {int | 0 < l} as gt0_l.

(* Abstract theory representing Rq = Zq[X]/(X^n + 1) and the high/lowBits operations *)
(* The constants [n] and [q] are defined by this theory *)
clone import DRing as DR. 
import RqRing.

(* Parameters for "Rounding" (e.g., highBits, lowBits, and shift)  *)
op gamma1 : int.
op gamma2 : { int | 2 <= gamma2 <= q %/ 4 } as gamma2_bound.
axiom gamma2_div : 2 * gamma2 %| (q - 1).

(* beta in spec.
 * beta is again a reserved keyword in EC.
 *
 * Maybe bound should be gt0_beta anyways?
 *)
op b : {int | 0 < b} as gt0_b.

(* more beta bounds and properties... *)
axiom b_gamma1_lt : b < gamma1.
axiom b_round_gamma2_lt : b < 2 * gamma2 %/ 2.

clone import DVect as DV with 
  theory DR <- DR,
  op HL.alpha <- 2*gamma2 
proof HL.ge2_alpha, HL.alpha_halfq_le, HL.even_alpha, HL.alpha_almost_divides_q.
realize HL.ge2_alpha by smt(gamma2_bound).
realize HL.even_alpha by smt().
realize HL.alpha_halfq_le by smt(gamma2_bound).
realize HL.alpha_almost_divides_q by apply gamma2_div.

import DV.MatRq. (* Matrices and Vectors over Rq *)
import DV.HL.    (* highBitsV and lowBitsV with alpha = 2 * gamma2 *)

(* challenge weight *)
op tau : { int | 1 <= tau <= n } as tau_bound.

axiom eta_tau_leq_b : e * tau <= b.

lemma cnorm_dC c tau : c \in dC tau => cnorm c <= 1 by smt(supp_dC).

type M.

type challenge_t = Rq.
type SK = matrix * vector * vector.
type PK = matrix * vector.
type commit_t = high list.
type response_t = vector. 

(* op dC : challenge_t distr = dC tau.  *)

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

op recover (pk : PK) (c : challenge_t) (z : response_t) : commit_t =
  let (mA, t) = pk in
  highBitsV (mA *^ z - c ** t).

clone FSa.CommRecov as FSaCR with
  op recover <= recover,
  op qS <= qS,
  op qH <= qH
proof* by smt(qS_ge0 qH_ge0).

section.
import FSaCR.
import FSaCR.DSS.

module (SimplifiedDilithium : SchemeRO)(H: Hash) = {
  proc keygen() : PK * SK = {
    var pk, sk;
    var mA, s1, s2;
    mA <$ dmatrix dRq k l;
    s1 <$ dvector (dRq_ e) l;
    s2 <$ dvector (dRq_ e) k;
    pk <- (mA, mA *^ s1 + s2);
    sk <- (mA, s1, s2);
    return (pk, sk);
  }

  proc sign(sk: SK, m: M) : Sig = {
    var z : vector option;
    var c : R;
    var ctr : int;
    var y, w, w1;
    var mA, s1, s2;
    (* silences unused variable warning *)
    c <- witness;

    (mA, s1, s2) <- sk;
    z <- None;
    while(z = None) {
      y <$ dvector (dRq_ (gamma1 - 1)) l;
      w <- mA *^ y;
      w1 <- highBitsV w;
      c <@ H.get((w1, m));
      z <- Some (y + c ** s1);
      if(gamma1 - b <= inf_normv (oget z) \/
         gamma2 - b <= inf_normv (lowBitsV (mA *^ y - c ** s2))) {
        z <- None;
      }
    }
    return (c, oget z);
  }

  proc verify(pk: PK, m : M, sig : Sig) = {
    var w, c, z, c';
    var mA, t1;
    var result;
    (mA, t1) <- pk;

    (c, z) <- sig;
    w <- highBitsV (mA *^ z - c ** t1);
    c' <@ H.get((w, m));
    result <- size z = l /\ inf_normv z < gamma1 - b /\ c = c';

    return result;
  }
}.

(** KOA to MLWE + SelfTargetMSIS *)

clone import MLWE as RqMLWE with 
  theory M <- MatRq,
  op dR <- dRq,
  op dS <- dRq_ e,
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
  op gamma <- max (gamma1 - b) (gamma2+1)
proof* by smt(Top.gt0_k Top.gt0_l). 
(* Where do dout_ll and enum_spec come from? Why are they not picked up by proof* *)

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
    var mA,tbar,t,mu,sig,c,z,w,e,y;
    mA <- subm mB 0 k 0 l;
    tbar <- col mB l;
    t <- -tbar;
    (mu,sig) <@ A(H').forge(mA,t); (* discard H, use H' *)
    y <- witness;

    (c,z) <- sig;
    w <- (mA *^ z - c ** t);
    e <- -lowBitsV w;
    y <- e || z || vectc 1 c;

    return (y,mu);
  }
}.

op locked (x : 'a) = x axiomatized by unlock.
lemma lock (x : 'a) : x = locked x by rewrite unlock.

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
(* Ethan: Not sure if good way to patch things *)
inline*; auto => />; smt(get_set_sameE).
qed.

import StdOrder.RealOrder.

(* move to EC lib? *)
lemma max_ltrP (i j k : int) : i < max j k <=> i < j \/ i < k by smt().

(* Ethan: This proof was broken; I tried fixing it. *)
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
    * rewrite dmap_id => /size_dmatrix /(_ _ _) /=; 1,2: smt(Top.gt0_k Top.gt0_l).
      rewrite colmxN oppvK => -[<-] ?. rewrite subm_colmx; smt(Top.gt0_k Top.gt0_l).
    * rewrite -(dmap_dprodE _ _ (fun x => x)) !dmap_id.
      rewrite dprod1E (@dvector_rnd_funi _ _ (col A l)) ?dRq_funi // -dprod1E.
      move/size_dmatrix => /(_ _ _); 1,2: smt(Top.gt0_k Top.gt0_l).
      apply dmatrixRSr1E; 1,2: smt(Top.gt0_k Top.gt0_l).
    case => A t /=; rewrite -(dmap_dprodE _ _ (fun x => x)) !dmap_id supp_dprod /=.
    case => supp_A supp_t. 
    move: (supp_A) => /size_dmatrix /(_ _ _) /=; 1,2: smt(Top.gt0_k Top.gt0_l).
    move: (supp_t) => /size_dvector. rewrite lez_maxr; 1:smt(Top.gt0_k). move => s_t [r_A c_A].
    (* case => /supp_dmatrix_Rqkl /= [[r_A c_A] Rq_A] /supp_dvector_Rqk [s_t Rq_t]. *)
    rewrite r_A c_A s_t /= -{2}r_A -{2}c_A subm_catmrCl /= 1:/#.
    rewrite col_catmrR /= ?r_A ?c_A ?s_t // subrr. 
    rewrite colN oppmK colK /=; apply supp_dmatrix_catmr => //;1,2: smt(Top.gt0_k Top.gt0_l).
    rewrite supp_dmatrix_full ?dRq_fu //; smt(Top.gt0_k Top.gt0_l). 
  call (: ={PRO.RO.m} /\ (forall x, x \in PRO.RO.m => oget PRO.RO.m.[x] \in dC tau){1}).
    proc; inline*; auto => />; smt(get_setE get_set_sameE).
  auto => /> &1 &2 RO_dC r_mA c_mA s_t. split => [|E1 E2]. 
  + rewrite -r_mA -c_mA subm_catmrCl /= 1:/#. 
    rewrite col_catmrR //= 1:/#. 
    by rewrite colN oppmK colK. 
  move => _ _.     
  by rewrite -E1 -E2 /= rows_catmr //=; smt(Top.gt0_k Top.gt0_l).
inline S1(H').verify  H'.get. wp. sp.

(* need [size z{1} = l] to prove equality of the RO argument *)
case (size z{1} = l /\ inf_normv z{1} < gamma1 - b);
  last by conseq (:_ ==> true); [ smt() | inline*; auto].
call(: ={arg,glob G} /\ (forall x, x \in PRO.RO.m => oget PRO.RO.m.[x] \in dC tau){1} 
       ==> ={res} /\ res{1} \in dC tau).
  proc; inline*; auto => />. smt(get_set_sameE).

auto => /> &1 ? r_mA c_mA size_t size_z normv_z.

pose w := (_ - Vectors.(**) _ _). (* FIXME: why is XInt.(**) in scope? *)
pose w1 := highBitsV _. 
pose e := - lowBitsV _.

have size_w : size w{1} = k.
- by rewrite size_addv /= size_scalarv size_mulmxv /#. 
have size_e : size e = k.
- by rewrite size_oppv size_lowBitsV.
split => [|? c_dC]; last split.
- rewrite mulmxv_cat.
  + smt(gt0_k). 
  + rewrite cols_catmr /= 1:/# size_catv /=. smt().
  + rewrite rows_catmr /=; smt(). 
  rewrite -size_e mulmx1v mulmxv_cat;  1..3: smt().
  rewrite colmxN colmxc scalarvN.  
  rewrite addvC -sub_eqv 2://; 1: by rewrite size_shiftV size_highBitsV /#.
  by rewrite /w1 /e oppvK high_lowPv. 
- rewrite 2!inf_normv_cat !StdOrder.IntOrder.ltr_maxrP !max_ltrP.
  rewrite normv_z /= 1!inf_normv_vectc //.
  have -> /= : cnorm c0{1} < gamma2+1 by smt(cnorm_dC gamma2_bound).
  right. rewrite /e inf_normvN. smt(inf_normv_low gamma2_bound).
- rewrite catvA get_catv_r ?size_catv 1:/#. 
  have -> : k + (l + 1) - 1 - (size e + size z{1}) = 0 by smt().
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
op ds1 = dvector (dRq_ e) l.
op ds2 = dvector (dRq_ e) k.

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
  let z = y + c ** s1 in
  if gamma1 - b <= inf_normv z \/
     gamma2 - b <= inf_normv (lowBitsV (mA *^ y - c ** s2) ) then
    None else
    Some z.

op verify (pk : PK) (w1 : commit_t) (c : challenge_t) (z : response_t) : bool =
  let (mA, t) = pk in
  size z = l /\ 
  inf_normv z < gamma1 - b /\
  w1 = highBitsV (mA *^ z - c ** t).

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

(* Sanity check for matrix/vector dimensions *)
lemma size_t pk sk : (pk,sk) \in keygen => size pk.`2 = k.
proof. 
case/supp_dlet => mA /= [s_mA]. 
case/supp_dlet => s1 /= [s_s1]. 
case/supp_dlet => s2 /= [s_s2].
rewrite /(\o) supp_dunit => -[-> _]. 
rewrite [Vectors.size]lock /= -lock.
rewrite size_addv size_mulmxv;
smt(size_dmatrix size_dvector Top.gt0_k Top.gt0_l).
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
proc; inline *. 
while (oz{1} = z{2} /\ ={c,sk,glob H,m} /\ (sk = (mA,s1,s2)){2}); 
  last by auto => /> /#.
conseq (: _ ==> ={c, sk, glob H, m} /\ (sk = (mA,s1,s2)){2} 
                 /\ oz{1} = z{2}); 1: smt().
seq 4 4 : (#pre /\ w{1} = w1{2} /\ P.pstate{1} = y{2}).
- call(: true). conseq />. 
  rnd: *0 *0.
  skip => /> &m.
  split => [[y w1] ?|_]. 
  + apply/eq_sym. congr. (* symmetry as hack for RHS pattern selection *)
    by rewrite /commit /= dmap_comp /(\o) /=. 
  move => ?. by rewrite /commit /= dmap_comp /(\o).
conseq />. auto => /> &m. split => [|pass_chk]. 
+ by rewrite /respond /= => ->.
+ by rewrite /respond /= ifF.
qed.

equiv verify_opbased_correct :
  OpBasedSig(H).verify ~ SimplifiedDilithium(H).verify :
  ={arg,glob H} ==> ={res,glob H}.
proof.
proc; inline *.
sp.
seq 1 1: (#pre /\ ={c, z, w, c'} /\
          w{1} = recover pk{1} c{1} z{1}).
- by sp; call (: true).
if{1}; by auto => />.
qed.

end section OpBasedCorrectness.

(* -- OpBased is commitment recoverable -- *)
(* Necessary for the simulator definition below to make sense *)

local lemma pk_decomp mA' t' mA s1 s2 :
  ((mA', t'), (mA, s1, s2)) \in keygen =>
  mA' = mA /\ t' = mA *^ s1 + s2.
proof.
rewrite /keygen.
move => /supp_dlet /= H.
case H => x [? /supp_dlet /= H].
by case H => y [? /supp_dmap /= H] /#.
qed.

local lemma sk_size mA s1 s2 :
  (exists pk, (pk, (mA, s1, s2)) \in keygen) => size mA = (k, l) /\ size s1 = l /\ size s2 = k.
proof.
move => [pk /supp_dlet valid_keys].
case valid_keys => [mA' [mA_supp /supp_dlet /= valid_keys]].
case valid_keys => [s1' [s1_supp /supp_dmap /= valid_keys]].
case valid_keys => [s2' [s2_supp [#]]] *; subst.
smt(size_dmatrix size_dvector Top.gt0_l Top.gt0_k).
qed.

local lemma keygen_supp_decomp pk mA s1 s2 :
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
case pk_i => mA' t'.
case sk_i => mA s1 s2.
proc; inline *; auto => />.
(* introduce and unfold hypothesis *)
move => valid_keys.
have sk_sizes: size mA = (k, l) /\ size s1 = l /\ size s2 = k.
- by apply sk_size; exists (mA', t').
have rg_s2: s2 \in ds2 by smt(keygen_supp_decomp).
case /pk_decomp valid_keys => [??]; subst.
rewrite /commit /= => [[w0 y] /supp_dmap [y' [y'_supp [??]]]] c c_supp H w c' z; subst.
have ? {H}: (respond (mA, s1, s2) c y' <> None) by smt().
have -> /=: (respond (mA, s1, s2) c y' = None) = false by smt().
move => [#] *; subst.
(* Now, deal with the goal... *)
rewrite /respond /=.
have -> /= : (gamma1 - b <= inf_normv (y' + c' ** s1) \/
              gamma2 - b <= inf_normv (lowBitsV (mA *^ y' - c' ** s2))) = false by smt().
rewrite /recover /=.
(* From here, highbits Ay is close to highbits (Az - ct).
 * First expand out Az-ct.
 *)
have ->: mA *^ (y' + c' ** s1) - c' ** (mA *^ s1 + s2) = mA *^ y' - c' ** s2.
- rewrite mulmxvDr.
  + have ->: size y' = l by smt(size_dvector).
    by rewrite size_scalarv /#.
  rewrite scalarvDr.
  + by rewrite size_mulmxv => /#.
  have ->: mA *^ (c' ** s1) = c' ** (mA *^ s1).
  + by rewrite mulmsv /#.
  rewrite oppvD addvA.
  suff: c' ** (mA *^ s1) - c' ** (mA *^ s1) - c' ** s2 = - c' ** s2 by smt(addvA).
  rewrite addvN.
  have ->: size (c' ** (mA *^ s1)) = size (-c' ** s2).
  + by rewrite size_oppv !size_scalarv size_mulmxv => /#.
  by rewrite add0v //.
(* Now line things up for `hide_lowV` *)
have ->: highBitsV (mA *^ y') = highBitsV (mA *^ y' - c' ** s2 + c' ** s2).
- congr; suff: - c' ** s2 + c' ** s2 = zerov (size (mA *^ y')).
  + move => H; by rewrite -addvA H addv0.
  rewrite addvC addvN; congr.
  by rewrite size_scalarv size_mulmxv; smt(size_dvector).
apply (hide_lowV _ _ b); 5: smt().
- rewrite size_addv size_oppv size_scalarv.
  suff: size (mA *^ y') = size s2 by smt().
  by rewrite size_mulmxv; smt(size_dvector).
- smt(gt0_b).
- smt(b_round_gamma2_lt).
(* Finally, need to prove inf_norm cs2 upper-bound.
 * It's sufficient to bound inf-norm of (1-norm poly * inf-norm poly). *)
apply (StdOrder.IntOrder.ler_trans (tau * e)); last by smt(eta_tau_leq_b).
apply l1_inf_norm_product_ub.
- smt(tau_bound).
- exact gt0_eta.
- (* l1_norm of c' *)
  rewrite supp_dC /# in c_supp.
- apply inf_normv_ler => [|i rg_i]; first by smt(gt0_eta).
  rewrite supp_dvector in rg_s2; first by smt(Top.gt0_k).
  rewrite -supp_dRq; smt(gt0_eta).
qed.

(* -- OpBased is indeed zero-knowledge -- *)

op check_znorm (v : vector) = (size v = l) /\ (inf_normv v < gamma1 - b).
op dsimz = dvector (dRq_open (gamma1 - b)) l.

op line12_magic_number = (size (to_seq check_znorm))%r / (size (to_seq (support dy)))%r.
op dsimoz : response_t option distr = dlet (dbiased line12_magic_number) (fun b => if b then dmap dsimz Some else dunit None).

module HVZK_Sim_Inst : DID.HVZK_Sim = {
  proc get_trans(pk : PK) = {
    var mA, t, w', c, oz, z;
    var resp;
    (mA, t) <- pk;
    c <$ FSa.dC;
    oz <$ dsimoz;
    if(oz <> None) {
      z <- oget oz;
      w' <- mA *^ z - c ** t;
      resp <- if gamma2 - b <= inf_normv (lowBitsV w') then None else Some z;
    } else {
      resp <- None;
    }
    return if resp = None then None else Some (recover pk c (oget resp), c, oget resp);
  }
}.

section OpBasedHVZK.

local lemma dsimz_uni :
  is_uniform dsimz.
proof.
apply dvector_uni.
exact dRq_open_uni.
qed.

local lemma dsimz_ll :
  is_lossless dsimz.
proof.
apply dvector_ll.
exact dRq_open_ll.
qed.

local lemma dsimz_supp : support dsimz = check_znorm.
proof.
apply fun_ext => z.
rewrite /dsimz /check_znorm.
rewrite supp_dvector; first smt(Top.gt0_l).
rewrite inf_normv_ltr; first smt(b_gamma1_lt).
case (size z = l) => /= [size_z|]; last by auto.
smt(supp_dRq_open b_gamma1_lt).
qed.

local lemma dsimz1E z :
  check_znorm z =>
  mu1 dsimz z = inv (size (to_seq check_znorm))%r.
proof.
  move => ?.
  rewrite mu1_uni_ll ?dsimz_uni ?dsimz_ll; smt(dsimz_supp).
qed.

local lemma masking_range c s1 z:
  c \in FSa.dC => s1 \in ds1 => check_znorm z =>
  (z - c ** s1) \in dy.
proof.
move => c_supp s1_supp z_supp.
apply supp_dvector; first smt(Top.gt0_l).
split => [|i rg_i].
- (* size *)
  rewrite size_addv size_oppv size_scalarv.
  smt(size_dvector).
rewrite supp_dRq; first smt(b_gamma1_lt gt0_b).
rewrite get_addv.
- (* size *)
  smt(size_addv size_oppv size_scalarv size_dvector).
apply (StdOrder.IntOrder.ler_trans (cnorm z.[i] + cnorm (- c ** s1).[i])).
- exact cnorm_triangle.
suff: cnorm z.[i] < gamma1 - b /\ cnorm (- c ** s1).[i] <= tau * e by smt(eta_tau_leq_b).
split.
- (* bound cnorm z.[i] *)
  rewrite /check_znorm in z_supp.
  case z_supp => [size_z norm_z_ub].
  by rewrite inf_normv_ltr in norm_z_ub; smt(b_gamma1_lt).
- (* bound cnorm cs1 *)
  rewrite getvN cnormN get_scalarv.
  apply l1_cnorm_product_ub.
  - smt(tau_bound).
  - smt(gt0_eta).
  - by rewrite supp_dC /# in c_supp.
  - rewrite supp_dvector in s1_supp.
    + smt(Top.gt0_l).
    by rewrite -supp_dRq; smt(gt0_eta).
qed.

local lemma is_finite_check_znorm :
  is_finite check_znorm.
proof.
have ->: check_znorm = (fun (v : vector) => size v = l /\
    forall i, 0 <= i < l => (fun r => cnorm r < gamma1 - b) v.[i]).
- apply fun_ext => v.
  rewrite eq_iff.
  split.
  + move => [sz_v znorm_v].
    split => [/#|i rg_i] /=.
    by rewrite inf_normv_ltr in znorm_v; smt(b_gamma1_lt).
  + move => [sz_v cnorm_vi].
    split => [/#|].
    rewrite inf_normv_ltr; smt(b_gamma1_lt).
apply is_finite_vector.
apply (finite_leq predT) => /=; first smt().
exact is_finite_Rq.
qed.

local lemma is_finite_dy :
  is_finite (support dy).
proof.
have ->: support dy =
         (fun (y : vector) => size y = l /\
          forall i, 0 <= i < l => (fun r => r \in dRq_ (gamma1 - 1)) y.[i]).
- rewrite fun_ext => y /=.
  apply eq_iff.
  by rewrite supp_dvector //; smt(Top.gt0_l).
apply is_finite_vector.
apply (finite_leq predT) => /=; first smt().
exact is_finite_Rq.
qed.

local lemma mask_size :
  size (to_seq check_znorm) <= size (to_seq (support dy)).
proof.
apply uniq_leq_size.
- apply uniq_to_seq.
  exact is_finite_check_znorm.
move => v.
rewrite mem_to_seq.
- exact is_finite_check_znorm.
rewrite mem_to_seq.
- apply is_finite_dy.
rewrite supp_dvector; first smt(Top.gt0_l).
rewrite /check_znorm.
rewrite inf_normv_ltr; first smt(b_gamma1_lt).
suff: (forall x, (cnorm x < gamma1 - b => x \in dRq_ (gamma1 - 1))) by smt().
move => x H.
by rewrite supp_dRq; smt(gt0_b b_gamma1_lt).
qed.

local lemma mask_nonzero :
  0 < size (to_seq check_znorm).
proof.
suff: zerov l \in (to_seq check_znorm) by smt(size_eq0 List.size_ge0).
rewrite mem_to_seq; first exact is_finite_check_znorm.
split; first smt(size_zerov Top.gt0_l).
rewrite inf_normv_zero.
smt(b_gamma1_lt).
qed.

local lemma dy_ll :
  is_lossless dy.
proof.
apply dvector_ll.
exact dRq__ll.
qed.

local lemma dy_uni :
  is_uniform dy.
proof.
apply dvector_uni.
exact dRq__uni.
qed.

local op transz (c : Rq) s1 =
  dmap dy (fun y =>
    let z' = y + c ** s1 in
    if check_znorm z' then Some z' else None).

local lemma line12_magic_some :
  forall c s1 z0, c \in FSa.dC => s1 \in ds1 => check_znorm z0 =>
    mu1 (transz c s1) (Some z0) = 1%r / (size (to_seq (support dy)))%r.
proof.
move => c s1 z0 c_valid s1_valid z0_valid.
rewrite /transz dmap1E /pred1 /(\o) => /=.
rewrite (mu_eq _ _ (fun y => y + c ** s1 = z0)).
- move => y /#.
rewrite (mu_eq_support _ _ (pred1 (z0 - c ** s1))).
- move => /= y supp_y.
  rewrite /pred1 eq_iff.
  split.
  + move => H; rewrite eq_sym in H; subst.
    rewrite -addvA addvN.
    rewrite size_scalarv.
    have ->: size s1 = l by smt(size_dvector).
    have ->: l = size y by smt(size_dvector).
    by rewrite addv0.
  + move => H; subst.
    rewrite -addvA.
    have ->: (- c ** s1) + c ** s1 = c ** s1 + (- c ** s1) by apply addvC.
    rewrite addvN size_scalarv.
    have ->: size s1 = l by smt(size_dvector).
    have ->: l = size z0 by smt().
    by rewrite addv0.
rewrite mu1_uni_ll ?dy_uni ?dy_ll.
suff -> : (z0 - c ** s1) \in dy by trivial.
exact masking_range.
qed.

local lemma line12_outofbound :
  forall c s1 z0, c \in FSa.dC => s1 \in ds1 => ! (check_znorm z0) =>
    (Some z0) \notin (transz c s1).
proof.
move => c s1 z0 c_valid s1_valid z0_invalid.
rewrite /transz /pred1 /(\o) => /=.
rewrite supp_dmap => /#.
qed.

local lemma line12_magic_none :
  forall c s1, c \in FSa.dC => s1 \in ds1 =>
    mu1 (transz c s1) None = 1%r - (size (to_seq check_znorm))%r / (size (to_seq (support dy)))%r.
proof.
move => c s1 c_valid s1_valid.
have sumz : (sum (fun z => mu1 (transz c s1) z) = 1%r).
  by rewrite - weightE; apply dmap_ll; apply dy_ll.
rewrite sumD1_None /= in sumz.
  by apply summable_mu1.
suff: sum (fun (y : vector) => mu1 (transz c s1) (Some y)) = 
  (size (to_seq check_znorm))%r / (size (to_seq (support dy)))%r by smt().
clear sumz.
have -> :
  (fun z => mu1 (transz c s1) (Some z)) =
  (fun z => if check_znorm z then 1%r / (size (to_seq (support dy)))%r else 0%r).
  apply fun_ext => z; case (check_znorm z).
  + move => z_good.
    rewrite line12_magic_some => /#.
  + move => z_out.
    apply supportPn.
    apply line12_outofbound => //.
apply sum_characteristic.
exact is_finite_check_znorm.
qed.

local lemma line12_magic c s1 :
  c \in FSa.dC => s1 \in ds1 =>
  transz c s1 = dsimoz.
proof.
move => c_valid s1_valid.
apply eq_distr => z.
case z.
- rewrite line12_magic_none //.
  apply eq_sym; rewrite dlet1E sum_over_bool /=.
  rewrite dmap1E /pred1 /(\o) mu0 /=.
  rewrite dunit1E dbiased1E /line12_magicnumber /=.
  rewrite clamp_id; smt(mask_nonzero mask_size).
- move => z.
  case (check_znorm z).
  + move => z_valid.
    rewrite line12_magic_some //.
    rewrite eq_sym /line12_magicnumber dlet1E sum_over_bool /=.
    rewrite dunit1E /=.
    rewrite dmap1E /pred1 /(\o) /=.
    rewrite dsimz1E //=.
    rewrite dbiased1E /=.
    rewrite clamp_id; smt(mask_nonzero mask_size).
  + move => z_invalid.
    have -> : mu1 (transz c s1) (Some z) = 0%r.
      apply supportPn; apply line12_outofbound; by assumption.
    apply eq_sym; apply supportPn.
    rewrite supp_dlet.
    (* abuse of smt? *)
    smt(supp_dmap supp_dunit dsimz_supp).
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

    (mA, s1, s2) <- sk;
    t <- mA *^ s1 + s2;
    c <$ FSa.dC;
    y <$ dy;
    z <- y + c ** s1;
    if(check_znorm z) {
      w' <- mA *^ y - c ** s2;
      resp <- if gamma2 - b <= inf_normv (lowBitsV w') then None else Some z;
    } else {
      resp <- None;
    }
    return omap (fun z => (c, z)) resp;
  }

  (* Compute w' using only public information *)
  proc game3(pk: PK, sk: SK) : (challenge_t * response_t) option = {
    var mA, s1, s2, w', y, c, z, t, resp;

    (mA, s1, s2) <- sk;
    t <- mA *^ s1 + s2;
    c <$ FSa.dC;
    y <$ dy;
    z <- y + c ** s1;
    if(check_znorm z) {
      w' <- mA *^ z - c ** t;
      resp <- if gamma2 - b <= inf_normv (lowBitsV w') then None else Some z;
    } else {
      resp <- None;
    }
    return omap (fun z => (c, z)) resp;
  }

  (* Change conditional on `oz` *)
  proc game4(pk: PK, sk: SK) : (challenge_t * response_t) option = {
    var mA, s1, s2, w', y, c, z, t, resp;
    var oz;

    (mA, s1, s2) <- sk;
    t <- mA *^ s1 + s2;
    c <$ FSa.dC;
    y <$ dy;
    z <- y + c ** s1;
    oz <- if check_znorm z then Some z else None;
    if(oz <> None) {
      z <- oget oz;
      w' <- mA *^ z - c ** t;
      resp <- if gamma2 - b <= inf_normv (lowBitsV w') then None else Some z;
    } else {
      resp <- None;
    }
    return omap (fun z => (c, z)) resp;
  }

  (* Rewrite relevant parts of above as operator *)
  proc game5(pk: PK, sk: SK) : (challenge_t * response_t) option = {
    var mA, s1, s2, w', c, z, t, resp;
    var oz;

    (mA, s1, s2) <- sk;
    t <- mA *^ s1 + s2;
    c <$ FSa.dC;
    oz <$ transz c s1;
    if(oz <> None) {
      z <- oget oz;
      w' <- mA *^ z - c ** t;
      resp <- if gamma2 - b <= inf_normv (lowBitsV w') then None else Some z;
    } else {
      resp <- None;
    }
    return omap (fun z => (c, z)) resp;
  }

  (* Get (a, t) from public key *)
  proc game6(pk: PK, sk: SK) : (challenge_t * response_t) option = {
    var mA, mA', s1, s2, w', c, z, t, resp;
    var oz;

    (mA', s1, s2) <- sk;
    (mA, t) <- pk;
    c <$ FSa.dC;
    oz <$ transz c s1;
    if(oz <> None) {
      z <- oget oz;
      w' <- mA *^ z - c ** t;
      resp <- if gamma2 - b <= inf_normv (lowBitsV w') then None else Some z;
    } else {
      resp <- None;
    }
    return omap (fun z => (c, z)) resp;
  }

  (* simulator *)
  proc game7(pk: PK) : (challenge_t * response_t) option = {
    var mA, w', c, z, t, resp;
    var oz;

    (mA, t) <- pk;
    c <$ FSa.dC;
    oz <$ dsimoz;
    if(oz <> None) {
      z <- oget oz;
      w' <- mA *^ z - c ** t;
      resp <- if gamma2 - b <= inf_normv (lowBitsV w') then None else Some z;
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
swap{2} [1..2] 1.
seq 1 1: (#pre /\ ={c}); first by auto.
sp.
(* Sample `y` and discard unused `w` *)
seq 1 1: (#pre /\ st{1} = y{2} /\ size y{2} = l).
- rnd (fun wst => let (w, st) = wst in st) (fun y => (highBitsV (mA' *^ y), y)).
  auto => /> _.
  split.
  + move => y supp_y.
    rewrite /commit /=.
    rewrite (dmap1E (dvector (dRq_ (gamma1 - 1)) l)) /(\o).
    suff: (fun x => pred1 (highBitsV (mA' *^ y), y) (highBitsV (mA' *^ x), x)) = pred1 y by smt().
    by apply fun_ext => x /#.
  move => _ wst; case wst => w st /=.
  move => wst_supp.
  rewrite /commit /= in wst_supp.
  rewrite supp_dmap /= in wst_supp.
  case wst_supp => y [supp_y [??]]; subst.
  split => [|_] ; first smt().
  smt(size_dvector Top.gt0_l).
(* suff: equality of oz *)
seq 1 2: (#pre /\ oz{1} = resp{2}); last by auto => /#.
auto => />; smt(sk_size size_addv size_scalarv).
qed.

local equiv hop3_correct :
  HVZK_Hops.game2 ~ HVZK_Hops.game3 :
  ={arg} /\ arg{1} \in keygen ==> ={res}.
proof.
proc.
seq 5 5: (#pre /\ ={mA, s1, s2, t, c, y, z} /\
          mA{1} *^ y{1} - c{1} ** s2{1} = mA{2} *^ z{2} - c{2} ** t{2}); 2: by auto => /#.
auto => />.
move => &2 valid_key c c_valid y y_valid.
have: size (sk{2}.`1) = (k, l) /\ size (sk{2}.`2) = l /\ size (sk{2}.`3) = k.
- apply (sk_size (sk{2}.`1) (sk{2}.`2) (sk{2}.`3)).
  by exists pk{2} => /#.
(* Annoying proof of some simple vector calculations below... *)
case (sk{2}) => mA s1 s2 /= /> *.
rewrite mulmxvDr.
- rewrite size_scalarv; smt(size_dvector).
rewrite -addvA; congr.
rewrite mulmsv => [/#|].
rewrite scalarvDr; first by rewrite size_mulmxv => /#.
rewrite oppvD addvA addvN.
have ->: size (c ** (mA *^ s1)) = size (- c ** s2).
- by rewrite size_oppv !size_scalarv size_mulmxv => /#.
by rewrite add0v //.
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
seq 3 3: (#pre /\ ={mA, s1, s2, t, c} /\ (mA{1}, s1{1}, s2{1}) = sk_i).
- by auto => /#.
seq 3 1: (#pre /\ ={oz}); last by auto => /#.
rnd: *0 *0.
auto => /> &2.
case sk_i => mA' s1' s2'.
case pk_i => mA'' t'.
move => valid_keys.
have ?: size mA{2} = (k, l) /\ size s1{2} = l /\ size s2{2} = k.
- apply sk_size.
  by exists (mA'', t') => //.
have [??]: mA'' = mA{2} /\ t' = mA{2} *^ s1{2} + s2{2}.
- by apply pk_decomp => //.
subst.
split => [oz oz_valid | _ oz oz_valid].
- by rewrite dmap_id /transz /#.
rewrite supp_dmap in oz_valid.
case oz_valid => y /= [#] y_valid ?; subst => /=.
rewrite dmap_id.
rewrite /transz.
rewrite supp_dmap /=.
by exists y => /#.
qed.

local equiv hop6_correct pk_i sk_i :
  HVZK_Hops.game5 ~ HVZK_Hops.game6 :
  ={arg} /\ arg{1} = (pk_i, sk_i) /\ (pk_i, sk_i) \in keygen ==> ={res}.
proof.
proc.
seq 2 2: (#pre /\ ={mA, s1, s2, t} /\ mA{2} = mA'{2}).
- by auto => />; smt(pk_decomp).
by sim.
qed.

local equiv hop7_correct pk_i sk_i :
  HVZK_Hops.game6 ~ HVZK_Hops.game7 :
  arg{1} = (pk_i, sk_i) /\ arg{2} = pk_i /\ (pk_i, sk_i) \in keygen ==> ={res}.
proof.
proc.
seq 3 2 : (#pre /\ ={mA, t, c} /\ mA{1} = mA'{1} /\ sk{1} = (mA'{1}, s1{1}, s2{1}) /\ pk{1} = (mA{1}, t{1}) /\ c{1} \in FSa.dC).
- by auto; smt(pk_decomp).
seq 1 1 : (#pre /\ ={oz}); last by auto => /#.
rnd; auto => //= &1 &2.
move => [#] ??? valid_keys ?????? c_valid ; subst.
rewrite line12_magic //.
apply keygen_supp_decomp in valid_keys.
by case valid_keys => [??] //.
qed.

local equiv KLS_HVZK pk sk :
  HVZK_Hops.game1 ~ HVZK_Hops.game7 :
  (pk, sk) \in keygen /\ arg{1} = (pk, sk) /\ arg{2} = pk ==>
  ={res}.
proof.
transitivity HVZK_Hops.game2
  ((pk, sk) \in Top.keygen /\ arg{1} = (pk, sk) /\ arg{2} = (pk, sk) ==> ={res})
  ((pk, sk) \in Top.keygen /\ arg{1} = (pk, sk) /\ arg{2} = pk ==> ={res}); 1, 2: smt().
- by conseq (hop2_correct pk sk) => /#.
transitivity HVZK_Hops.game3
  ((pk, sk) \in Top.keygen /\ arg{1} = (pk, sk) /\ arg{2} = (pk, sk) ==> ={res})
  ((pk, sk) \in Top.keygen /\ arg{1} = (pk, sk) /\ arg{2} = pk ==> ={res}); 1, 2: smt().
- by conseq hop3_correct => /#.
transitivity HVZK_Hops.game4
  ((pk, sk) \in Top.keygen /\ arg{1} = (pk, sk) /\ arg{2} = (pk, sk) ==> ={res})
  ((pk, sk) \in Top.keygen /\ arg{1} = (pk, sk) /\ arg{2} = pk ==> ={res}); 1, 2: smt().
- by conseq hop4_correct => /#.
transitivity HVZK_Hops.game5
  ((pk, sk) \in Top.keygen /\ arg{1} = (pk, sk) /\ arg{2} = (pk, sk) ==> ={res})
  ((pk, sk) \in Top.keygen /\ arg{1} = (pk, sk) /\ arg{2} = pk ==> ={res}); 1, 2: smt().
- by conseq (hop5_correct pk sk) => /#.
transitivity HVZK_Hops.game6
  ((pk, sk) \in Top.keygen /\ arg{1} = (pk, sk) /\ arg{2} = (pk, sk) ==> ={res})
  ((pk, sk) \in Top.keygen /\ arg{1} = (pk, sk) /\ arg{2} = pk ==> ={res}); 1, 2: smt().
- by conseq (hop6_correct pk sk) => /#.
by conseq (hop7_correct pk sk) => /#.
qed.

lemma HVZK_Sim_correct k :
  equiv[DID.Honest_Execution(OpBased.P, OpBased.V).get_trans ~ HVZK_Sim_Inst.get_trans :
        k \in keygen /\ arg{1} = k /\ arg{2} = k.`1 ==> ={res}].
proof.
case k => pk sk.
(* Commitment recoverable - can drop the commitment *)
conseq (_: (pk, sk) \in keygen /\ arg{1} = (pk, sk) /\ arg{2} = pk ==>
       (res{1} = None /\ res{2} = None) \/
       (res{1} <> None /\ res{2} <> None /\
         (oget res{1}).`2 = (oget res{2}).`2 /\ (oget res{1}).`3 = (oget res{2}).`3))
  (_: arg = (pk, sk) /\ (pk, sk) \in keygen ==>
      res <> None => let (w, c, z) = oget res in w = (recover pk c z))
  (_: arg = pk ==>
      res <> None => let (w, c, z) = oget res in w = (recover pk c z)); 1, 2: smt().
- by conseq (recover_correct pk sk).
- by proc; auto => /#.
(* left *)
transitivity HVZK_Hops.game1
 ((pk, sk) \in keygen /\ arg{1} = (pk, sk) /\ arg{2} = (pk, sk) ==>
   let resL = if res{1} = None then None else Some ((oget res{1}).`2, (oget res{1}).`3) in
   resL = res{2})
 ((pk, sk) \in keygen /\ arg{1} = (pk, sk) /\ arg{2} = pk ==>
   let resR = if res{2} = None then None else Some ((oget res{2}).`2, (oget res{2}).`3) in
   res{1} = resR); 1, 2: smt().
- by proc; inline *; auto => /#.
(* Doing the final hop first to get rid of misaligned tuple *)
transitivity HVZK_Hops.game7
  ((pk, sk) \in keygen /\ arg{1} = (pk, sk) /\ arg{2} = pk ==> ={res})
  ((pk, sk) \in keygen /\ arg{1} = pk /\ arg{2} = pk ==>
   let resR = if res{2} = None then None else Some ((oget res{2}).`2, (oget res{2}).`3) in
   res{1} = resR); 1, 2: smt().
- by conseq (KLS_HVZK pk sk).
by proc; auto => /#.
qed.

end section OpBasedHVZK.

(* Main Theorem *)

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

section PROOF.

declare module A <: Adv_EFCMA_RO{-O_CMA_Default,-RO,-OpBasedSig}.

op bound : real. (* TODO *)

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
byequiv (_: ={glob A,glob RO,glob O_CMA_Default} ==> ={res}) => //.
transitivity SD(SimplifiedDilithium(RO),RO).distinguish 
   (={glob A,glob RO,glob O_CMA_Default} ==> ={res}) 
   (={glob A,glob RO,glob O_CMA_Default} ==> ={res}); 
   [smt()| smt() | by sim |].
transitivity SD(OpBasedSig(RO),RO).distinguish 
   (={glob A,glob RO,glob O_CMA_Default} ==> ={res}) 
   (={glob A,glob RO,glob O_CMA_Default} ==> ={res}); 
   [smt()| smt() | | by sim].
by conseq (eqv_code_op SD RO).
qed.

(*** Step 2 : Reduce to the case for general (i.e., not commitment recoverable schemes) ***)

local clone Generic as FSaG with
  op qS <= qS,
  op qH <= qH + Top.qS 
proof* by smt(qS_ge0 qH_ge0).

(* Generic FS+abort transform of the OpBased ID scheme *)
local module OpBasedSigG = FSaG.IDS_Sig(OpBased.P,OpBased.V).

local module EF_CMA_RO_G = FSaG.DSS.EF_CMA_RO.

(* raises : module `FSa.ID.Imp_Game` is incompatible 
local clone import FSa_CRtoGen as CG with
  theory FSa <= FSa,
  theory FSaCR <= FSaCR,
  theory FSaG <= FSaG.
*)

(* Need the reduction from the cloned theory ... 
local lemma pr_cr_gen &m : 
  Pr [ EF_CMA_RO(OpBasedSig, A, RO,O_CMA_Default).main() @ &m : res ] = 
  Pr [ EF_CMA_RO_G(OpBasedSigG, A, RO,O_CMA_Default).main() @ &m : res ].
*)

lemma SimplifiedDilithium_secure &m : 
  Pr [ EF_CMA_RO(SimplifiedDilithium, A, RO,O_CMA_Default).main() @ &m : res ] <= bound.
proof.
(* Step 1 *)
rewrite pr_code_op.
admitted.

end section PROOF.
