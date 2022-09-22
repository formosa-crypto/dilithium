require import AllCore Distr List DistrExtras.
require DigitalSignaturesRO.
require Mat.
require import PolyReduce.
require import IntDiv.
require ZqRounding.
require ZModFieldExtras.
require import Nat.

require import IDSabort.
require FSabort.
require FSa_CMAtoKOA.
require FSa_CRtoGen.

require MLWE SelfTargetMSIS. 

abstract theory DRing.

(* Modulo *)
op q : {int | prime q} as prime_q. 

(* Poly degrees *)
op n : {int | 0 < n} as gt0_n.

(* Polynomial ring ℤq[X]/(X^n +1 ) *)
type Rq.

clone import Ring.ComRing as RqRing with type t <= Rq.

op cnorm : Rq -> int.             (* infinity norm (after centered reduction modulo) *)
op l1_norm : Rq -> int.           (* sum over absolute values                        *)

(* TOTHINK: If [high = Rq] is a problem, we either need to have a
ComRing structure on high or use lists rather than vectors to pass
[w1] around *)


type high = Rq.                   (* type of "rounded" elements *)

op lowBits  : Rq -> int -> Rq.    (* "low-order"  bits *)
op highBits : Rq -> int -> high.  (* "high-order" bits *)
op shift    : high -> int -> Rq.  (* adding zeros      *)

op [lossless uniform] dRq : Rq distr. (* TOTHINK: add full? *)

op [lossless uniform] dRq_ : int -> Rq distr.
axiom supp_dRq x a : x \in dRq_ a <=> cnorm x <= a.

op [lossless uniform] dC  : int -> Rq distr.
axiom supp_dC c a : c \in dC a <=> cnorm c <= 1 /\ l1_norm c = a.

axiom high_lowP x a : shift (highBits x a) a + lowBits x a = x.

axiom hide_low r s a b : 
  !odd a => cnorm s <= b => cnorm (lowBits s a) < a %/ 2 - b =>
  highBits (r + s) = highBits r.

axiom lowbit_small r a :
  cnorm (lowBits r a) <= a %/ 2. (* TOTHINK: +1 ? *)

end DRing.

clone import DRing as DR. 

clone import Mat as MatRq 
  with theory ZR <= DR.RqRing.

(* lifting functions to vectors *)
op mapv (f : Rq -> Rq) (v : vector) : vector = 
  offunv (fun i => f v.[i], size v).

op (**) (c : Rq) (v : vector) = mulvs v c.

lemma size_mapv f v : size (mapv f v) = size v by [].

op lowBitsV v a = mapv (fun x => lowBits x a) v.
op highBitsV v a = mapv (fun x => highBits x a) v.

clone import MatRq.NormV as INormV with 
  type a <- nat,
  op id <- zero,
  op (+) <- Nat.max,
  op norm <- ofint \o cnorm proof* by smt(maxrA maxrC max0r).

op inf_normv = ofnat \o INormV.normv.

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

(* matrix dimensions *)
op k : {int | 0 < k} as gt0_k.
op l : {int | 0 < l} as gt0_l.

type challenge_t = Rq.
type SK = matrix * vector * vector.
type PK = matrix * vector.
type commit_t = vector. 
type response_t = vector. 

op dC : challenge_t distr = dC tau. 

(* Just storing `y` should be good here. *)
type pstate_t = vector. 

clone IDS as DID with 
  type PK <= PK,
  type SK <= SK,
  type W <= commit_t,
  type C <= challenge_t,
  type Z <= response_t,
  type Pstate <= pstate_t proof*.

(* Raises "`ID.Imp_Game` is incompatible" error *)
(*
clone import FSabort as OpFSA with
  theory ID <= DID,
  type M <- M,
  op dC <- dC.
*)

(* Unsure if this is intended usage;
 * can't recall from the meeting the other day *)
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
  highBitsV (mA *^ z - c ** t) (2 * gamma2).

clone import CommRecov as FSaCR with
  op recover <= recover,
  op kappa <- kappa.
(* TODO instantiate a couple more things and prove axioms
 * TODO at least `recover` has to be defined for things to be provable *)
import DSS.

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
    ctr <- 0;
    z <- None;
    while(ctr < kappa /\ z = None) {
      y <$ dvector (dRq_ (gamma1 - 1)) l;
      w <- mA *^ y;
      w1 <- highBitsV w (2 * gamma2);
      c <@ H.get((w1, m));
      z <- Some (y + c ** s1);
      if(gamma1 - b <= inf_normv (oget z) \/
         gamma2 - b <= inf_normv (lowBitsV (mA *^ y - c ** s2) (2 * gamma2))) {
        z <- None;
      }
      ctr <- ctr + 1;
    }
    return if z = None then None else Some (c, oget z);
  }

  proc verify(pk: PK, m : M, sig : Sig) = {
    var w, c, z, c';
    var mA, t1;
    var result;
    (mA, t1) <- pk;
    result <- false;
    if(sig <> None) {
      (c, z) <- oget sig;
      w <- highBitsV (mA *^ z - c ** t1) (2 * gamma2);
      c' <@ H.get((w, m));
      result <- inf_normv z < gamma1 - b /\ c = c';
    }
    return result;
  }
}.

(** KOA to MLWE + SelfTargetMSIS *)

clone import MLWE as RqMLWE with 
  theory M <= MatRq, (* <- raises "Anomaly: removed" - issue #268 *)
  op dR <- dRq,
  op dS <- dRq_ e,
  op k <- k,
  op l <- l
proof* by smt(gt0_k gt0_l).

clone import SelfTargetMSIS as RqStMSIS with
  theory M <= MatRq,
  type M <- M,
  op m <- l+1,
  op n <- k,
  op dR <- dRq,
  op dC <- dC,
  op gamma <- max (gamma1 - b) gamma2.

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

section PROOF.

declare module H <: Hash_i.

declare module A <: Adv_EFKOA_RO{-H}.

local module S1 (H : Hash) = { 
  proc keygen() : PK * SK = {
    var pk, mA, t;
    mA <$ dmatrix dRq k l;
    t  <$ dvector dRq k;
    pk <- (mA, t);
    return (pk,witness);
  }
  
  proc sign(sk: SK, m: M) : Sig = { return None; }

  proc verify = SimplifiedDilithium(H).verify
}.

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

end section PROOF.


(* -- Operator-based -- *)

op keygen : (PK * SK) distr =
  dlet (dmatrix dRq k l) (fun mA =>
  dlet (dvector (dRq_ e) l) (fun s1 =>
  dmap (dvector (dRq_ e) k) (fun s2 =>
  let pk = (mA, mA *^ s1 + s2) in
  let sk = (mA, s1, s2) in
  (pk, sk)))).

op commit (sk : SK) : (commit_t * pstate_t) distr =
  let (mA, s1, s2) = sk in
  dmap (dvector (dRq_ (gamma1 - 1)) l) (fun y =>
  let w1 = highBitsV (mA *^ y) (2 * gamma2) in
  (w1, y)).

op respond (sk : SK) (c : challenge_t) (y: pstate_t) : response_t option =
  let (mA, s1, s2) = sk in
  let z = y + c ** s1 in
  if gamma1 - b <= inf_normv z \/
     gamma2 - b <= inf_normv (lowBitsV (mA *^ y - c ** s2) (2 * gamma2)) then
    None else
    Some z.

op verify (pk : PK) (w1 : commit_t) (c : challenge_t) (z : response_t) : bool =
  let (mA, t) = pk in
  inf_normv z < gamma1 - b /\
  w1 = highBitsV (mA *^ z - c ** t) (2 * gamma2).

clone import OpBased with
  op keygen <= keygen,
  op commit <= commit,
  op response <= respond,
  op verify <= verify.
(* TODO proof *. *)

op locked : 'a -> 'a.
axiom lock (x : 'a) : x = locked x.

(* Sanity check for matrix/vector dimensions *)
lemma size_t pk sk : (pk,sk) \in keygen => size pk.`2 = k.
proof. 
case/supp_dlet => mA /= [s_mA]. 
case/supp_dlet => s1 /= [s_s1]. 
case/supp_dlet => s2 /= [s_s2].
rewrite /(\o) supp_dunit => -[-> _]. 
rewrite [Vectors.size]lock /= -lock.
rewrite size_addv size_mulmxv;
smt(size_dmatrix size_dvector gt0_k gt0_l).
qed.

module OpBasedSig = IDS_Sig(OpBased.P, OpBased.V).

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
while (oz{1} = z{2} /\ ={c,sk,glob H,m} /\ k{1} = ctr{2} /\ (sk = (mA,s1,s2)){2}); 
  last by auto => /> /#.
conseq (: _ ==> ={c, sk, glob H, m} /\ (sk = (mA,s1,s2)){2} 
                 /\ oz{1} = z{2} /\ k{1} = ctr{2}); 1: smt().
seq 4 4 : (#pre /\ w{1} = w1{2} /\ P.pstate{1} = y{2}).
- call(: true). conseq />. 
  rnd: *0 *0. skip => /> &m ?. split => [[y w1] ?|_]. 
  + apply/eq_sym. congr. (* symmetry as hack for RHS pattern selection *)
    by rewrite /commit /= dmap_comp /(\o) /=. 
  move => ?. by rewrite /commit /= dmap_comp /(\o).
conseq />. auto => /> &m ?. split => [|pass_chk]. 
+ by rewrite /respond /= => ->.
+ by rewrite /respond /= ifF.
qed.

equiv verify_opbased_correct :
  OpBasedSig(H).verify ~ SimplifiedDilithium(H).verify :
  ={arg,glob H} ==> ={res,glob H}.
proof.
proc; inline *. 
sp; if; 1,3: by auto => />.
seq 3 3: (#pre /\ ={c, z, w, c'} /\
          w{1} = recover pk{1} c{1} z{1}).
- sp; call (: true); skip => /> ?? H H' ?.
  by rewrite -H in H'; case H' => ?? /#.
if{1}; by auto => />.
qed.

end section OpBasedCorrectness.



(* Main Theorem *)

import FSaCR.DSS.
import FSaCR.DSS.PRO.
import FSaCR.DSS.DS.Stateless.

(* Distinguisher for (RO) signature schemes *)
module type SigDist (S : Scheme) (H : Hash_i) = { 
  proc distinguish() : bool
}.

equiv eqv_code_op (D <: SigDist{-OpBasedSig}) (H <: Hash_i{-P,-D}) : 
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

(* TODO: this should be local, but for this all axioms need to be proved *)
clone Generic as FSaG with
  op kappa <- kappa,
  op qS <- qS,
  op qH <- qH + qS.

(* clone import FSa_CRtoGen as CG with  *)
(*   theory FSa <- OpFSA. *)
(*   theory FSaG <- FSaG. *)

lemma SimplifiedDilithium_secure &m : 
  Pr [ EF_CMA_RO(SimplifiedDilithium, A, RO,O_CMA_Default).main() @ &m : res ] <= bound.
proof.
(* Step 1 *)
rewrite pr_code_op.
admitted.

end section PROOF.
