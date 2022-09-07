(* ---------------------------------------------------------------------------------------------- 
   
   Verification of the proof of the Fiat-Shamir transform
   using lossy identification schemes by
   Eike Kiltz and Vadim Lyubashevsky and Christian Schaffner 
   in https://eprint.iacr.org/2017/916  
   
   ---------------------------------------------------------------------------------------------- *)
require import Int Real List FSet Distr RealExp SmtMap SDist StdOrder.
require import DistrExtras.
import RealOrder.

require FelTactic.

require DigitalSignaturesRO PROM ReprogOnce Collision.

require import IDSabort.
import IDS.
(* *********************************************************************** *)
(*                      IDS-based Signatures                               *)
(* *********************************************************************** *)


(* ********************* Cloning Signature Theory ************************ *) 

type M.               (* Messages *)
type Sig = W*Z.       (* Signatures *)

const qS : int. (* allowed number of sig queries *)
const qH : int. (* allowed number of ro  queries *)
axiom qS_ge0 : 0 <= qS.
axiom qH_ge0 : 0 <= qH.

(* maximal number of iterations allowed for signing *)
op kappa : { int | 0 < kappa } as kappa_gt0.

op [lossless uniform] dC : C distr.

(* clone RO signature theory, 
   setting oracle distribution to uniform challenges *)
clone import DigitalSignaturesRO as DSS with 
type DS.pk_t <- PK,
type DS.sk_t <- SK,
type DS.msg_t <- M,
type DS.sig_t <- Sig,
type PRO.in_t <= W*M,
type PRO.out_t <= C, 
op   PRO.dout <= fun _ => dC.

import DSS.PRO.
import DSS.DS.Stateless.

(* *** Defining the signature scheme (generic FS+abort signature) *********** *)
module (IDS_Sig (P: Prover, V:Verifier) : SchemeRO) (H: Hash) = {
  proc keygen() : PK*SK = {
    var sk, pk;
    (pk,sk) <@ P.keygen();
    return (pk,sk);
  }
  proc sign(sk:SK,m:M) : Sig = {
    var w  : W <- witness;
    var c  : C <- witness;
    var oz : Z option <- None;

    while (oz = None) { 
      w <@ P.commit(sk);
      c <@ H.get((w,m));
      oz <@ P.response(sk,c);
    }
    return (w,oget oz);
  }
  
  proc verify(pk:PK, m:M, s:Sig):bool = {
    var result,c,w,z;
    (w,z) <- s;
    c <@ H.get((w,m));
    result <@ V.verify(pk,w,c,z);
    return result; 
  }
}.

theory OpBased.

(* ********************* IDS based on operators ****************** *) 

(* This will simplify the proof here but may render it less
   generic. Will have to see if this is usable. *)

op [lossless] keygen : (PK * SK) distr.
op [lossless] commit : SK -> (W * Pstate) distr.
op response : SK -> C -> Pstate -> Z option. (* TODO: should be respond *)
op verify : PK -> W -> C -> Z -> bool.

(* -- Require most (valid?) keys to have high min-entropy -- *)

op check_entropy : SK -> bool.
op gamma, alpha : real.

axiom alpha_gt0 : 0%r < alpha.
axiom gamma_gt0 : 0%r < gamma.

op valid_sk sk =
  exists pk, (pk, sk) \in keygen.

axiom check_entropy_correct :
  forall sk, valid_sk sk => check_entropy sk => p_max (dfst (commit sk)) <= alpha.

axiom most_keys_high_entropy :
  mu keygen (fun keys => let (pk, sk) = keys in ! check_entropy sk) <= gamma.

(* Alternative keygen that only outputs key pairs with high commitment entropy *)
op keygen_good = 
  dcond keygen (fun k : PK * SK => check_entropy k.`2).

lemma keygen_good_sdist : 
  sdist keygen keygen_good <= gamma.
proof.
apply (ler_trans _ _ _ (sdist_dcond _ _ keygen_ll) _).
rewrite (mu_eq _ _ 
  (fun (keys : PK * SK) => let (_, sk) = keys in ! check_entropy sk)).
- by move => [pk sk] @/predC.
exact most_keys_high_entropy.
qed.

const sk0 : SK.
axiom sk0P : valid_sk sk0 /\ check_entropy sk0.

op commit_good (sk : SK) = 
  if valid_sk sk /\ check_entropy sk then commit sk else commit sk0.

lemma commit_good_ll sk : is_lossless (commit_good sk).
proof. smt(commit_ll). qed.

lemma commit_good_entropy sk : 
  p_max (dfst (commit_good sk)) <= alpha. 
proof. smt(check_entropy_correct sk0P). qed.

lemma commit_goodE sk : 
  sk \in dsnd keygen_good => commit_good sk = commit sk.
proof.
case/supp_dmap => -[pk sk'] /> /dcond_supp /#.
qed.

module V = { 
  proc challenge(w:W, pk:PK): C = { 
    var c;
    c <$ dC;
    return c;
  }

  proc verify(pk:PK, w:W, c:C, z:Z): bool = {
    return verify pk w c z;
  }
}.
module P = {
  var pstate : Pstate

  proc keygen(): PK*SK = { 
    var ks;
    ks <$ keygen;
    return ks;
  } 
  
  proc commit(sk:SK): W = { 
    var w;
    (w, pstate) <$ commit sk;
    return w;
  }
    
  proc response(sk:SK, c:C): Z option = {
    return response sk c pstate;
  }
}.

(* ----------------------------------------------------------------------*)
(*                           Start proof                                 *)
(* ----------------------------------------------------------------------*)

(* The following is the actual reduction that can break EF_KOA using 
   an EF_CMA adversary. The first module is the sign oracle the reduction 
   implements, and the second module is the reduction itself. *)

module ORedKOA (Sim : HVZK_Sim) : SOracle_CMA = {
  var pk : PK
  var qs : M list
  var overlay : (W*M,C) fmap

  proc init(pki: PK) : unit = {
    pk <- pki;
    qs <- [];
    overlay <- empty;
  }

  proc sign(m: M) : Sig = {
    var sig: Sig;
    var w,c,z;
    var ot <- None;
    var k;

    qs <- rcons qs m;
    k <- 0; 
    while (ot = None /\ k < kappa) {  
      ot <@ Sim.get_trans(pk);
      k <- k + 1;
    } 
    (w, c, z) <- oget ot;
    if (ot <> None) 
      overlay.[(w,m)] <- c;
    return if (ot <> None) then (w,z) else witness;
  }
}.

module (RedKOA (A : Adv_EFCMA_RO) (Sim : HVZK_Sim) : Adv_EFKOA_RO) (H : Hash) = { 
  import var ORedKOA

  module H' = { 
    proc get(x : W*M) : C = { 
      var oc : C option;
      var c : C;

      oc <- overlay.[x];
      if (oc = None) { 
        c <@ H.get(x);
        oc <- Some c;
      }
      return oget oc;
    }
  }

  proc forge (pk : PK) : M * Sig = { 
    var m,sig;
    
    ORedKOA(Sim).init(pk);
    (m,sig) <@ A(H',ORedKOA(Sim)).forge(pk);
    return (m,sig);
  } 
}.

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

(* Oracle with a bad event if the loop bound is reached. 
   This is out here, because we have no good way of bounding it *)

module (Oracle1b_CMA : Oracle_CMA) (S : Scheme)  = {
  include var O_CMA_Default(S) [-init,sign]
  var bad : bool

  proc init(ski: SK) : unit = {
    sk <- ski;
    qs <- [];
    bad <- false;
  }

  proc sign(m: M) : Sig = {
    var pstate;
    var sig: Sig;
    var k;
    var c <- witness;
    var w <- witness;
    var oz <- None;
    qs <- rcons qs m;

    k <- 0;
    while (oz = None /\ k < kappa) { 
      (w, pstate) <$ commit sk;
      c <@ RO.get((w,m));
      oz <- response sk c pstate;
      k <- k+1;
    } 
    bad <- bad \/ oz = None; 
    return if oz <> None then (w,oget oz) else witness;
  }
}.


section PROOF. 

(* We assume a CMA adversary A making at most [qH] [get] queries
to the random oracle and at most [qS] queries to the signing
oracle *)

declare module A <: Adv_EFCMA_RO{-RO,-P,-V,-O_CMA_Default,-ORedKOA,-CountS,-CountH,-Oracle1b_CMA}.

declare axiom A_query_bound (SO <: SOracle_CMA{-A,-CountH, -CountS}) (H <: Hash{-A,-CountH,-CountS}) : 
 hoare[ A(CountH(H),CountS(SO)).forge : 
        CountH.qh = 0 /\ CountS.qs = 0 ==> 
        CountH.qh <= qH /\ CountS.qs <= qS].

declare axiom A_ll : forall (R <: Hash{-A} ) (O <: SOracle_CMA{-A} ),
  islossless O.sign => islossless R.get => islossless A(R, O).forge.

(* We also assume a perfect HVZK simulator for the ID scheme *)

declare module Sim <: HVZK_Sim {-RO,-P,-V,-A,-ORedKOA,-CountS,-CountH}.

declare axiom Sim_perfect_HVZK k : 
  equiv [ Honest_Execution(P,V).get_trans ~ Sim.get_trans : 
          k \in keygen /\ arg{1} = k /\ arg{2} = k.`1 ==> ={res}].


module Game0 (A:Adv_EFCMA_RO,O:Oracle_CMA) = EF_CMA_RO(IDS_Sig(P,V),A,RO,O).


(* ----------------------------------------------------------------------*)
(*                            First game hop:                            *)
(* Simply replace the generic game by one that uses our scheme           *)
(* ----------------------------------------------------------------------*)

local module (Oracle1_CMA : Oracle_CMA) (S : Scheme)  = {
    include var O_CMA_Default(S) [-sign]

    proc sign(m: M) : Sig = {
      var pstate;
      var sig: Sig;
      var k;
      var c <- witness;
      var w <- witness;
      var oz <- None;
      qs <- rcons qs m;

      k <- 0;
      while (oz = None) { 
        (w, pstate) <$ commit sk;
        c <@ RO.get((w,m));
        oz <- response sk c pstate;
        k <- k + 1;
      } 
      return (w,oget oz);      
    }
  }.
 
(* This is basically just inlining and renaming  *)   
local lemma hop1 &m : 
  Pr [ Game0(A, O_CMA_Default).main() @ &m : res] = 
  Pr [ Game0(A, Oracle1_CMA).main() @ &m : res].
proof.
byequiv (_: ={glob A} ==> ={res}) => //. proc. inline{1} 2; inline {2} 2.
seq 4 4 : (={glob O_CMA_Default,RO.m, m, sig,pk,sk}); last by sim.
call (: ={RO.m,glob O_CMA_Default}); [|by sim|by inline*; auto].
proc; inline{1} 1; swap{1} 8 -2; wp.
while (={oz,w,m,glob O_CMA_Default, glob RO} 
       /\ sk{1} = O_CMA_Default.sk{2} 
       /\ m0{1} = m{2}); by inline*; auto => />. 
qed.

(* ----------------------------------------------------------------------*)
(*                            Second game hop:                           *)
(* Introduce an upper bound on the number of signing attempts            *)
(* ----------------------------------------------------------------------*)



(* TOTHINK: Proving termination actually requires us to prove 

forall sk, sk \in dsnd keygen => 
  exists w st, (w,st) \in commit sk /\ forall c, respond sk c st <> None

Otherwise, there is a miniscule chance that the (finately many) spaces
in the random oracle all get filled with c's that do not admit any
positive response, making it impossible to exit the loop. 

Maybe we should assume the loop to be bounded a priory? *)

local lemma hop1a &m : 
     Pr [Game0(A,Oracle1_CMA).main()  @ &m : res] 
  <=   Pr [Game0(A,Oracle1b_CMA).main() @ &m : res ] 
     + Pr [Game0(A,Oracle1b_CMA).main() @ &m : Oracle1b_CMA.bad ].
proof.
byequiv => //. proc. inline{1} 2; inline{2} 2. 
seq 4 4 : (!Oracle1b_CMA.bad{2} => ={glob O_CMA_Default,RO.m,pk,sk,m,sig}); last first.
- case (Oracle1b_CMA.bad{2}). 
  + conseq (:_ ==> true); [smt()| by inline*; auto]. 
  + conseq (: _ ==> ={r}); [smt() | sim => /#].
call (: Oracle1b_CMA.bad, ={RO.m, glob O_CMA_Default}).
- exact A_ll. 
- proc. wp. conseq />. smt().
  splitwhile{1} 6 : (k < kappa). 
  seq 5 5 : (={w,oz,glob O_CMA_Default,RO.m}); first by sim.
  admit. (* termination *)
- move => *. islossless.
  admit. (* termination *)
- admit. (* preservation of bad *)
- sim.
- move => *; islossless.
- move => *. conseq />. islossless. 
by inline*; auto => /> /#.
qed.


(* ----------------------------------------------------------------------*)
(*                           Second game hop:                            *)
(* Limit the game to use only keys with high committment entropy         *)
(* ----------------------------------------------------------------------*)


local module Game0k (A : Adv_EFCMA_RO) (O: Oracle_CMA) = {
  proc main() : bool = {
    var pk : PK;
    var sk : SK;
    var m : M;
    var sig : Sig;
    var nrqs : int;
    var is_valid : bool;
    var is_fresh : bool;
    
    RO.init();
    (pk, sk) <$ keygen_good;
    O(IDS_Sig(P,V,RO)).init(sk);
    (m, sig) <@ A(RO,O(IDS_Sig(P,V,RO))).forge(pk);
    is_valid <@ IDS_Sig(P,V,RO).verify(pk, m, sig);
    is_fresh <@ O(IDS_Sig(P,V,RO)).fresh(m);
    nrqs <@ O(IDS_Sig(P,V,RO)).nr_queries();
    
    return nrqs <= q_efcma /\ is_valid /\ is_fresh;
  }
}.

local clone Dist with
  type a <- PK * SK.

print Dist.GenDist.Distinguisher. 

local module (D (O : Oracle_CMA) : Dist.GenDist.Distinguisher) = { 
  proc guess (x : PK * SK) = {
    var pk : PK;
    var sk : SK;
    var m : M;
    var sig : Sig;
    var nrqs : int;
    var is_valid : bool;
    var is_fresh : bool;

    (pk, sk) <- x;
    RO.init();
    O(IDS_Sig(P,V,RO)).init(sk);
    (m, sig) <@ A(RO,O(IDS_Sig(P,V,RO))).forge(pk);
    is_valid <@ IDS_Sig(P,V,RO).verify(pk, m, sig);
    is_fresh <@ O(IDS_Sig(P,V,RO)).fresh(m);
    nrqs <@ O(IDS_Sig(P,V,RO)).nr_queries();
    
    return nrqs <= q_efcma /\ is_valid /\ is_fresh;
  }
}.

local lemma hop0 &m : 
     Pr [Game0(A,Oracle1b_CMA).main()  @ &m : res ] 
  <= Pr [Game0k(A,Oracle1b_CMA).main() @ &m : res ] + gamma.
proof.
suff : `| Pr[ Game0(A, Oracle1b_CMA).main() @ &m : res] - 
          Pr[ Game0k(A, Oracle1b_CMA).main() @ &m : res] | <= gamma; 1: smt().
have -> : Pr[ Game0(A, Oracle1b_CMA).main() @ &m : res] = 
          Pr[ Dist.Sample(D(Oracle1b_CMA)).main(keygen) @&m : res].
- byequiv (_ : ={glob A,glob Oracle1b_CMA,glob RO} /\ d{2} = keygen ==> _) => //. 
  proc; do ! inline{1} 2; inline{2} 2. 
  swap{1} [2..4] -1.
  seq 3 3 : (={glob A,glob Oracle1b_CMA,RO.m,pk,sk}); last by sim.
  by auto => /> /#. 
have -> : Pr[ Game0k(A, Oracle1b_CMA).main() @ &m : res] = 
          Pr[ Dist.Sample(D(Oracle1b_CMA)).main(keygen_good) @&m : res].
- byequiv (_ : ={glob A,glob Oracle1b_CMA,glob RO} /\ d{2} = keygen_good ==> _) => //. 
  proc. inline{2} 2. wp. swap{1} 2 -1.
  seq 1 3 : (={glob A,glob Oracle1b_CMA,RO.m,pk,sk}); last by sim.
  by auto => /> /#. 
apply: ler_trans keygen_good_sdist. 
exact (Dist.adv_sdist (D(Oracle1b_CMA))).
qed.



(* ----------------------------------------------------------------------*)
(*                           Second game hop:                            *)
(* First real modification of oracle: First sample c, then reprgram RO  *)
(*                                                                       *)
(* ----------------------------------------------------------------------*)

(* Second SIGN oracle: First samples challenge, then programs the QRO. This
   handles the reprogramming bound  *)
local module (Oracle2_CMA : Oracle_CMA) (S : Scheme)  = {
  include var O_CMA_Default(S) [-sign,init]
  var bad2 : bool

  proc init(ski: SK) : unit = {
    sk <- ski;
    qs <- [];
    bad2 <- false;
  }

    proc sign(m: M) : Sig = {
      var pstate;
      var sig: Sig;
      var k;
      var c <- witness;
      var w <- witness;
      var oz <- None;
      qs <- rcons qs m;

      k <- 0;
      while (oz = None /\ k < kappa) { 
        (w, pstate) <$ commit sk;
        bad2 <- bad2 \/ (w,m) \in RO.m;
        c <$ dC; 
        RO.set((w,m),c);
        oz <- response sk c pstate;
        k <- k+1;
      } 
      (* bad <- bad || oz = None;  *)
      return if oz <> None then (w,oget oz) else witness;
   }
}.

print Oracle2_CMA. 

(** Bounding the bad event **)

local clone Collision as C with
  type W <- W,
  type M <- M,
  type SK <- SK,
  type St <- Pstate,
  op d <- commit_good,
  axiom d_ll <- commit_good_ll.

print C.Oracle.

local module Oracle2C (PS : C.Oracle) = {
  import var O_CMA_Default

  proc init(ski: SK) : unit = {
    sk <- ski;
    qs <- [];
  }
  
  proc sign(m: M) : Sig = {
      var pstate;
      var sig: Sig;
      var k;
      var c <- witness;
      var w <- witness;
      var oz <- None;
      qs <- rcons qs m;

      k <- 0;
      while (oz = None /\ k < kappa) { 
        (w, pstate) <@ PS.sample(sk,m);
        c <$ dC; 
        RO.set((w,m),c);
        PS.put(w,m);
        oz <- response sk c pstate;
        k <- k+1;
      } 
      (* bad <- bad || oz = None;  *)
      return if oz <> None then (w,oget oz) else witness;
   }
}.

local module RedGuess (PS : C.Oracle) = {
  module H = { 
    proc get(x) = { 
      var r;
      PS.put(x);
      r <@ RO.get(x);
      return r;
    }
  }

  proc main() : unit = {
    var pk : PK;
    var sk : SK;
    var m : M;
    var sig : Sig;
    var nrqs : int;
    var is_valid : bool;
    var is_fresh : bool;
    
    RO.init();
    (pk, sk) <$ keygen_good;
    Oracle2C(PS).init(sk);
    CountH(H).init();
    CountS(Oracle2C(PS)).init();
    A(CountH(H),CountS(Oracle2C(PS))).forge(pk);
    (* we no longer care about the result *)
  }
}.

local lemma red_collision &m : 
  Pr [Game0k(A,Oracle2_CMA).main() @ &m : Oracle2_CMA.bad2] <=
  Pr [C.Game(RedGuess,C.M).main() @ &m : C.M.bad ].
proof.
byequiv => //; proc. 
seq 4 3 : (Oracle2_CMA.bad2{1} <=> C.M.bad{2}) ; last by conseq />; inline*; auto.
inline{2} 3.
call (: ={RO.m,glob O_CMA_Default}  
       /\ O_CMA_Default.sk{2} \in dsnd keygen_good
       /\ (fdom RO.m = C.M.s){2} /\ Oracle2_CMA.bad2{1} = C.M.bad{2}).
- proc. inline C.Count(C.M).sample Oracle2C(C.Count(C.M)).sign. wp.
  while (={k,w,oz,RO.m,glob O_CMA_Default} /\ m{1} = m0{2}
         /\ O_CMA_Default.sk{2} \in dsnd keygen_good
         /\ Oracle2_CMA.bad2{1} = C.M.bad{2} /\ (fdom RO.m = C.M.s){2}).
  inline*; auto => />. smt(fdom_set mem_fdom fsetP in_fsetU1 commit_goodE).
  auto => />. 
- proc. inline*; auto => /> &1 _. smt(fdom_set mem_fdom fsetP in_fsetU1).
inline*; auto => />. smt(fdom0 supp_dmap). 
qed.

local lemma bad2_bound &m : 
  Pr [Game0k(A,Oracle2_CMA).main() @ &m : Oracle2_CMA.bad2] <= 
  (qS * kappa)%r * (qS * kappa + qH)%r * alpha.
proof.
apply (ler_trans _ _ _ (red_collision &m)). 
have := C.put_sample_bound RedGuess (qH + kappa * qS) (kappa * qS) alpha _ _ _ _ &m; 
  1,2,5: smt(qH_ge0 kappa_gt0 qS_ge0).
- move => sk w. apply: ler_trans (commit_good_entropy sk). 
  exact: pmax_upper_bound. 
move => O. proc. 
conseq (:_ ==> C.Count.cp <= CountH.qh + kappa * CountS.qs /\ 
               C.Count.cs <= kappa * CountS.qs) 
       (: _ ==> CountH.qh <= qH /\ CountS.qs <= qS); 
  1,2: smt(qH_ge0 kappa_gt0 qS_ge0). 
- call (A_query_bound (<: Oracle2C(C.Count(O))) (<: RedGuess(C.Count(O)).H)).
  by inline*; auto => />.
call (:    C.Count.cs <= kappa * CountS.qs 
        /\ C.Count.cp <= CountH.qh + kappa * CountS.qs).
- proc; inline 2; swap 1 7; wp. 
  while (   C.Count.cs <= kappa * CountS.qs + k 
         /\ C.Count.cp <= CountH.qh + kappa * CountS.qs + k
         /\ k <= kappa).
  + by inline*; auto; call(: true); auto; call(: true); auto => /> /#.
  auto => />. smt(qH_ge0 kappa_gt0 qS_ge0).
- by proc; inline*; auto; call(: true); auto => /> /#.
by inline*; auto.
qed.

local lemma hop2 &m : 
  Pr [Game0k(A,Oracle1b_CMA).main() @ &m : res ] 
  <=   Pr [Game0k(A,Oracle2_CMA).main() @ &m : res ]
     + Pr [Game0k(A,Oracle2_CMA).main() @ &m : Oracle2_CMA.bad2].
proof.
byequiv => //; proc. 
seq 4 4 : (!Oracle2_CMA.bad2{2} => ={glob O_CMA_Default,RO.m,pk,sk,m,sig}); last first.
- case (Oracle2_CMA.bad2{2}). 
  + conseq (:_ ==> true); [smt() | by inline*; auto ].
  + conseq (: _ ==> ={nrqs,is_valid,is_fresh}); [smt() | sim => /#].
call (: Oracle2_CMA.bad2, ={RO.m, glob O_CMA_Default}); last 6 first.
- move => *. proc. islossless. 
  while true (kappa - k). move => z. wp. conseq (: _ ==> true). smt(). islossless. skip; smt(). 
- move => *. proc. 
  conseq (:_ ==> true) (:_ ==> Oracle2_CMA.bad2); 1,2: smt(). 
  + while Oracle2_CMA.bad2; inline*; auto => />. 
  while true (kappa - k). move => z. wp. conseq (: _ ==> true). smt(). islossless. islossless. smt(). 
- conseq />. by proc; inline*; auto.
- move => *; islossless.
- move => *. conseq />. islossless.
- by inline*; auto => /> /#.
- exact A_ll. 
proc. wp. conseq />.
seq 5 5 : (#[1:3]pre /\ ={w,oz,glob O_CMA_Default,k}); 1: by auto.
(* Make loop termination on LHS independent from bad event *)
transitivity*{1} { 
  while (k < kappa) {     
   if (oz = None) { 
     (w, pstate) <$ commit O_CMA_Default.sk;
     c <@ RO.get((w, m));
     oz <- response O_CMA_Default.sk c pstate;
   }
   k <- k + 1;
 }
}; 1,2: smt(). 
- splitwhile{2} 1 : (oz = None).
  seq 1 1 : (#post /\ !(k{2} < kappa /\ oz{2} = None)). 
  + while (#pre). 
    * rcondt{2} 1; first by auto => />. 
      conseq (: _ ==> ={O_CMA_Default.sk, O_CMA_Default.qs, RO.m, c, k, m, oz, pstate, w}). 
      smt(). sim. auto => />.
  + while{2} (#pre) (kappa - k{2}). 
    * move => &h z. by rcondf 1; auto => /> /#. 
  auto => />. smt().
(* Make loop termination on RHS independent from bad event - same as above *)
transitivity*{2} { 
  while (k < kappa) {     
   if (oz = None) { 
     (w, pstate) <$ commit O_CMA_Default.sk;
     Oracle2_CMA.bad2 <- Oracle2_CMA.bad2 \/ (w, m) \in RO.m;
     c <$ dC;
     RO.set((w, m), c);
     oz <- response O_CMA_Default.sk c pstate;
   }
   k <- k + 1;
 }
}; 1,2: smt(); last first.
- splitwhile{1} 1 : (oz = None).
  seq 1 1 : (#post /\ !(k{1} < kappa /\ oz{1} = None)). 
  + while (#pre). 
    * rcondt{1} 1; first by auto => />. 
      conseq (: _ ==> ={glob O_CMA_Default,Oracle2_CMA.bad2, RO.m, c, k, m, oz, pstate, w}). 
      smt(). sim. auto => />.
  + while{1} (#pre) (kappa - k{1}). 
    * move => &h z. by rcondf 1; auto => /> /#. 
  auto => />. smt().
(* main up-to-bad step *)
while (={k} /\ (!Oracle2_CMA.bad2{2} => ={RO.m,glob O_CMA_Default,w,oz,m}));
  last by auto => /> /#.
case (Oracle2_CMA.bad2{2}). 
- conseq (: ={k} ==> ={k}) _ (: Oracle2_CMA.bad2 ==> Oracle2_CMA.bad2); 1,2: smt(); 
    first by if; inline*; auto => />.
  wp. conseq />. 
  (* usual equitermination trick *)
  seq 1 0 : true. 
    conseq (:_ ==> _) (: _ ==> true : 1%r); islossless. 
  conseq (:_ ==> _) _ (: _ ==> true : 1%r); islossless.
if; 1,3: by auto => /> /#.
seq 1 1 : (!Oracle2_CMA.bad2{2} /\ ={RO.m, glob O_CMA_Default, m, k, oz, w, pstate}); 
  first by auto => /> /#.
case (((w,m) \in RO.m){2}).
- conseq (: ={k} ==> ={k}) _ (: ((w,m) \in RO.m) ==> Oracle2_CMA.bad2); 1,2: smt(). 
  + by inline*; auto => />. 
  + by wp; conseq />; inline*; auto.
inline*; rcondt{1} 3; first by auto => /> /#.
auto => />. smt(get_set_sameE).
qed.

local module (Oracle3_CMA : Oracle_CMA) (S : Scheme)  = {
    import var O_CMA_Default(S)
    include var Oracle1b_CMA(S) [-sign]
    var bad2 : bool

    proc sign(m: M) : Sig = {
      var pstate;
      var sig: Sig;
      var k;
      var c <- witness;
      var w <- witness;
      var oz <- None;
      qs <- rcons qs m;

      k <- 0;
      while (oz = None /\ k < kappa) { 
        (w, pstate) <$ commit sk;
        c <$ dC; 
        oz <- response sk c pstate;
        k <- k+1;
      } 
      if (oz <> None) RO.set((w,m),c);
      (* bad <- bad || oz = None;  *)
      return if oz <> None then (w,oget oz) else witness;
   }
}.


(* TODO: prove axioms and make this local *)
(* TOTHINK: How do we align the RO theories ? *)

local clone ReprogOnce as R1 with
  type PK <- PK,
  type SK <- SK,
  type ST <- Pstate,
  type Z <- Z,
  type M <- M,
  type W <- W,
  type C <- C,
  op dC <- dC,
  op qs <- qS,
  op qh <- qH + 1,
  op kappa <- kappa,
  op alpha <- alpha,
  op keygen <- keygen_good,
  op commit <- commit,
  op respond <- (fun sk c st => response sk st c),
  theory RO <= PRO
proof*. 
realize keygen_ll by admit. 
realize commit_ll by apply commit_ll.
realize dC_ll by apply dC_ll.
realize dC_uni by apply dC_uni.
realize all_sk_can_accept by admit.  
realize all_sk_can_reject by admit.
realize dX_pmax by admit. (* TODO: this should be phrased in terms of commit, respond, dcond ... *)
realize qs_gt0 by admit.
realize qh_gt0 by admit. 
realize kappa_gt0 by admit.

local module B (O : R1.Oracle) = { 
  module H = { 
    proc get = O.h
  }

  module SO = { 
    var qs : M list
    proc sign (m : M) = { 
      var ot;
      qs <- rcons qs m;
      ot <@ O.sign(m);
      return if ot <> None then ((oget ot).`1,(oget ot).`3) else witness;
    }
  }

  proc distinguish(pk:PK) = { 
    var m : M;
    var sig : Sig;
    var nrqs : int;
    var is_valid : bool;
    var is_fresh : bool;

    SO.qs <- [];
    CountH(H).init();
    CountS(SO).init();

    (m, sig) <@ A(CountH(H),CountS(SO)).forge(pk);
    is_valid <@ IDS_Sig(P,V,CountH(H)).verify(pk, m, sig);
    is_fresh <- !(m \in SO.qs);
    nrqs <- size SO.qs;    
    return nrqs <= q_efcma /\ is_valid /\ is_fresh;
  }
}.

local lemma hop3 &m : 
     Pr [Game0k(A,Oracle2_CMA).main() @ &m : res ] 
  <= Pr [Game0k(A,Oracle3_CMA).main() @ &m : res ] +  (qH + 1)%r * (kappa * qS)%r * alpha.
proof.
have -> : Pr[Game0k(A, Oracle2_CMA).main() @ &m : res] = 
          Pr[R1.Game(B,R1.OLeft).main() @ &m : res].
- byequiv => //. proc. inline{2} 4. 
  seq 4 8 : (={RO.m,m,sig} /\ pk{1} = pk0{2} 
             /\ O_CMA_Default.qs{1} = B.SO.qs{2}); 
     last by inline*; auto => />.
  call(: ={RO.m}  
          /\ O_CMA_Default.qs{1} = B.SO.qs{2}
          /\ O_CMA_Default.sk{1} = R1.OLeft.sk{2}); first last.
  + by proc; inline*; auto => /> /#.
  + by inline*; auto => />.
  proc. inline{2} 2. inline{2} 4. wp.
  while (={oz,w,RO.m} /\ k{1} = i{2} /\ m{1} = m1{2}
          /\ O_CMA_Default.qs{1} = B.SO.qs{2}
          /\ O_CMA_Default.sk{1} = R1.OLeft.sk{2}).
  + by inline*; auto.
  by auto => /> /#.
have -> : Pr[Game0k(A, Oracle3_CMA).main() @ &m : res] = 
          Pr[R1.Game(B,R1.ORight).main() @ &m : res].
- byequiv (_: ={glob A} ==> ={res}) => //. proc. inline{2} 4. 
  seq 4 8 : (={RO.m,m,sig} /\ pk{1} = pk0{2} 
             /\ O_CMA_Default.qs{1} = B.SO.qs{2}); 
     last by inline*; auto => />.
  call(: ={RO.m}  
          /\ O_CMA_Default.qs{1} = B.SO.qs{2}
          /\ O_CMA_Default.sk{1} = R1.OLeft.sk{2}); first last.
  + by proc; inline*; auto => /> /#.
  + inline*; auto => />.
  proc. inline{2} 2. inline{2} 4. inline RO.set. wp. 
  while (={oz,w,c,RO.m} /\ k{1} = i{2} /\ m{1} = m1{2}
          /\ O_CMA_Default.qs{1} = B.SO.qs{2}
          /\ O_CMA_Default.sk{1} = R1.OLeft.sk{2}).
  + by inline*; auto.
  by auto => />. 
suff : `| Pr[R1.Game(B, R1.OLeft).main() @ &m : res] - 
          Pr[R1.Game(B, R1.ORight).main() @ &m : res] | 
      <= (qH + 1)%r * (kappa * qS)%r * alpha by smt().
apply (R1.adv_bound B); last first.
- move => O ? ?; islossless. 
  by apply (A_ll (<: CountH(B(O).H)) (<: CountS(B(O).SO))) => //; islossless.
move => O; proc. 
seq 4 : (R1.Count.countS <= qS /\ R1.Count.countH <= qH); 
  last by inline*; auto; call(: true); auto => /> /#.
conseq (: _ ==> CountH.qh = R1.Count.countH /\ CountS.qs = R1.Count.countS)
       (: _ ==> CountH.qh <= qH /\ CountS.qs <= qS); 1,2 : smt().
- call (A_query_bound (<: B(R1.Count(O)).SO) (<: B(R1.Count(O)).H)). 
  by inline*; auto => />.
call (: CountH.qh = R1.Count.countH /\ CountS.qs = R1.Count.countS).
- proc; inline*; auto; call(: true); auto => />.
- proc; inline*; auto; call(: true); auto => />.
by inline*; auto => />.
qed.

(* This is no longer an Oracle_CMA, because init also takes the public key *)
local module OGame1  = {
  var sk : SK
  var pk : PK
  var qs : M list

  proc init(sk_i : SK, pk_i : PK) : unit = {
    sk <- sk_i;
    pk <- pk_i;
    qs <- [];
  }

  proc fresh(m : M) : bool = { return ! (m \in qs); }
  
  proc nr_queries() : int = { return size qs; }
  
  proc sign(m: M) : Sig = {
    var c,k,z;
    var w <- witness;
    var ot <- None;
    qs <- rcons qs m;

    k <- 0;
    while (ot = None /\ k < kappa) { 
      ot <@ Honest_Execution(P,V).get_trans(pk,sk);
      k <- k+1;
    } 
    (w,c,z) <- oget ot;
    if (ot <> None) RO.set((w,m),c);
    return if ot <> None then (w,z) else witness;      
   }
}.

local module Game1 (A : Adv_EFCMA_RO) = {
  proc main() : bool = {
    var pk : PK;
    var sk : SK;
    var m : M;
    var sig : Sig;
    var nrqs : int;
    var is_valid : bool;
    var is_fresh : bool;
    
    RO.init();
    (pk, sk) <$ keygen_good;
    OGame1.init(sk,pk);
    (m, sig) <@ A(RO,OGame1).forge(pk);
    is_valid <@ IDS_Sig(P,V,RO).verify(pk, m, sig);
    is_fresh <@ OGame1.fresh(m);
    nrqs <@ OGame1.nr_queries();
    
    return nrqs <= q_efcma /\ is_valid /\ is_fresh;
  }
}.

local lemma hop4 &m : 
  Pr [Game0k(A,Oracle3_CMA).main() @ &m : res ] = Pr [Game1(A).main() @ &m : res ].
proof.
byequiv (: ={glob A} ==> _) => //; proc.
seq 4 4 : (   ={m,sig,RO.m,pk,glob A} 
           /\ ={qs,sk}(O_CMA_Default,OGame1) 
           /\ pk{2} = OGame1.pk{2}); last first.
wp. conseq (: _ ==> ={nrqs,is_valid,is_fresh}). auto. sim => />.
  conseq />.
call (:  ={RO.m} /\ ={qs,sk}(O_CMA_Default,OGame1)).
- proc; inline*. conseq />. 
  wp. 
  while (={RO.m,k} /\ ={qs,sk}(O_CMA_Default,OGame1) 
         /\ (omap (fun z => (w,c,z)) oz){1} = ot{2}); 
  by auto => /> /#.
- by proc; inline*; auto.
by inline*; auto => />.
qed.

local module OGame2  = {
  var pk : PK
  var qs : M list

  proc init(pk_i : PK) : unit = {
    pk <- pk_i;
    qs <- [];
  }

  proc fresh(m : M) : bool = { return ! (m \in qs); }
  
  proc nr_queries() : int = { return size qs; }
  
  proc sign(m: M) : Sig = {
    var c,k,z;
    var w <- witness;
    var ot <- None;
    qs <- rcons qs m;

    k <- 0;
    while (ot = None /\ k < kappa) { 
      ot <@ Sim.get_trans(pk);
      k <- k+1;
    } 
    (w,c,z) <- oget ot;
    if (ot <> None) RO.set((w,m),c);
    return if ot <> None then (w,z) else witness;      
   }
}.

local module Game2 (A : Adv_EFCMA_RO) = {
  proc main() : bool = {
    var pk : PK;
    var sk : SK;
    var m : M;
    var sig : Sig;
    var nrqs : int;
    var is_valid : bool;
    var is_fresh : bool;
    
    RO.init();
    (pk, sk) <$ keygen_good;
    OGame2.init(pk);
    (m, sig) <@ A(RO,OGame2).forge(pk);
    is_valid <@ IDS_Sig(P,V,RO).verify(pk, m, sig);
    is_fresh <@ OGame2.fresh(m);
    nrqs <@ OGame2.nr_queries();
    
    return nrqs <= q_efcma /\ is_valid /\ is_fresh;
  }
}.

(* We only handle the case where the HVZK advantate is actually O *)
local lemma hop5 &m : 
  Pr [Game1(A).main() @ &m : res ] = Pr [Game2(A).main() @ &m : res ].
proof.
byequiv => //; proc. 
seq 4 4 : (={RO.m, m,pk, sig} /\ ={qs}(OGame1,OGame2)); last by sim.
inline*.
call (: =   {RO.m} /\ ={qs,pk}(OGame1,OGame2)
        /\ (OGame2.pk{2},OGame1.sk{1}) \in keygen_good); first last.
- by proc; inline*; auto.
- by auto => /> /#.
proc. 
inline RO.set. wp. 
while (={RO.m,k,ot} /\ ={qs,pk}(OGame1,OGame2) 
       /\ (OGame2.pk{2},OGame1.sk{1}) \in keygen_good); last by auto => />.
wp; conseq (: _ ==> ={ot}); 1: smt().
exlim (OGame2.pk{2}) => pk. 
exlim (OGame1.sk{1}) => sk.
call (Sim_perfect_HVZK (pk,sk)); auto => />. 
smt(dcond_supp).
qed.


local module Game2k (A : Adv_EFCMA_RO) = {
  proc main() : bool = {
    var pk : PK;
    var sk : SK;
    var m : M;
    var sig : Sig;
    var nrqs : int;
    var is_valid : bool;
    var is_fresh : bool;
    
    RO.init();
    (pk, sk) <$ keygen;
    OGame2.init(pk);
    (m, sig) <@ A(RO,OGame2).forge(pk);
    is_valid <@ IDS_Sig(P,V,RO).verify(pk, m, sig);
    is_fresh <@ OGame2.fresh(m);
    nrqs <@ OGame2.nr_queries();
    
    return nrqs <= q_efcma /\ is_valid /\ is_fresh;
  }
}.

local module D2 = {
  proc guess(x : PK*SK) : bool = {
    var pk : PK;
    var sk : SK;
    var m : M;
    var sig : Sig;
    var nrqs : int;
    var is_valid : bool;
    var is_fresh : bool;
    
    RO.init();
    (pk, sk) <- x;
    OGame2.init(pk);
    (m, sig) <@ A(RO,OGame2).forge(pk);
    is_valid <@ IDS_Sig(P,V,RO).verify(pk, m, sig);
    is_fresh <@ OGame2.fresh(m);
    nrqs <@ OGame2.nr_queries();
    
    return nrqs <= q_efcma /\ is_valid /\ is_fresh;
  }
}.

local lemma hop6 &m : 
     Pr [Game2(A).main()  @ &m : res ] 
  <= Pr [Game2k(A).main() @ &m : res ] + gamma.
proof.
suff : `| Pr[ Game2(A).main() @ &m : res] - 
          Pr[ Game2k(A).main() @ &m : res] | <= gamma; 1: smt().
have -> : Pr[ Game2(A).main() @ &m : res] = 
          Pr[ Dist.Sample(D2).main(keygen_good) @&m : res].
- byequiv (_ : ={glob A,glob Sim, glob RO} /\ d{2} = keygen_good ==> _) => //. 
  proc. inline D2.guess. wp.
  swap{1} 2 -1. swap{2} 4 -1. 
  seq 1 3 : (={glob A,glob Sim,RO.m,pk,sk}); last by sim.
  by auto => /> /#. 
have -> : Pr[ Game2k(A).main() @ &m : res] = 
          Pr[ Dist.Sample(D2).main(keygen) @&m : res].
- byequiv (_ : ={glob A,glob Sim, glob RO} /\ d{2} = keygen ==> _) => //. 
  proc. inline D2.guess. wp.
  swap{1} 2 -1. swap{2} 4 -1. 
  seq 1 3 : (={glob A,glob Sim,RO.m,pk,sk}); last by sim.
  by auto => /> /#. 
apply: ler_trans keygen_good_sdist;rewrite sdistC.
exact (Dist.adv_sdist (D2)).
qed.

(* Reduction to the EF_KOA game. Note that [RedKOA], beeing an
adversary, only gets access to the [get] procedure of the RO and
therefore cannot reprogam the oracle in the way the simulation game
does. Thus the random oracle passed to the CMA adversary A is hidden
behind an overlay containing the reprogramming necessary during the
simulated signing queries. However, since a successful forgery by A
must be on a fresh message, any such forgery is also a valid forgery
with respect to the underlying (unpatched) oracle.

For strong unforgeability, the argument becomes more involved, as the
adversary can hit the overlay if he manages to break comutational
unique response of the ID scheme. *)

local lemma KOA_bound &m : 
     Pr [ Game2k(A).main() @ &m : res ] 
  <= Pr [ EF_KOA_RO(IDS_Sig(P,V),RedKOA(A,Sim),RO).main() @ &m : res ].
proof.
byequiv (_: ={glob RO,glob A,glob Sim} ==> res{1} => res{2}) => //.
proc; inline{2} 2. 
seq 4 3 : (={m,sig,pk} 
          /\ (RO.m{1} = (union_map ORedKOA.overlay RO.m){2})
          /\ ={qs,pk}(OGame2,ORedKOA)
          /\ forall w m, (w,m) \in ORedKOA.overlay{2} => m \in ORedKOA.qs{2}
          ).
- inline{2} 3; wp.
  call(: ={glob Sim} /\ ={pk,qs}(OGame2,ORedKOA) 
         /\ (RO.m{1} = (union_map ORedKOA.overlay RO.m){2})
         /\ forall w m, (w,m) \in ORedKOA.overlay{2} => m \in ORedKOA.qs{2}).
  + proc; inline RO.set; wp.
    while (={k,ot,glob Sim} /\ ={pk}(OGame2,ORedKOA)); 1: by sim. 
    auto => />; smt(mem_rcons mem_set set_union_map_l).
  + proc. wp. sp. if{2}.
    * inline*. auto => /> &1 hO c Hc. 
      smt(set_union_map_r set_union_map_l mem_union_map 
          get_setE get_set_sameE mergeE).
    * auto => />.
      smt(set_union_map_r set_union_map_l mem_union_map 
          get_setE get_set_sameE mergeE).
  by inline* ; auto => />; smt(merge_empty mem_empty).
- inline{1} 3; inline{1} 2 ; wp. 
  conseq (:_ ==> is_valid{1} /\ ! (m{1} \in OGame2.qs{1}) => is_valid{2}); 1: smt().
  inline IDS_Sig(P,V,RO).verify.
  case (m{1} \in OGame2.qs{1}). 
  + by conseq (:_ ==> true);[smt()|inline*; auto].
  inline*; swap 6 -5.
  seq 1 1 : (#pre /\ r{1} = r0{2}); first by auto.
  sp 5 5. 
  if; first by auto => />; smt(mem_union_map). 
  conseq (: _ ==> ={is_valid}); 1: smt().
  - auto => />; smt(set_union_map_r set_union_map_l mem_union_map 
          get_setE get_set_sameE mergeE).
  - auto => />; smt(set_union_map_r set_union_map_l mem_union_map 
          get_setE get_set_sameE mergeE).
qed.

import RField.

op bound1 = (qS * kappa)%r * (qS * kappa + qH)%r * alpha.
op bound2 = (qH + 1)%r * (kappa * qS)%r * alpha.

lemma FSabort_bound &m : 
   Pr [ EF_CMA_RO(IDS_Sig(P, V), A, RO, O_CMA_Default).main() @ &m : res] 
<= Pr [ EF_KOA_RO(IDS_Sig(P,V),RedKOA(A,Sim),RO).main() @ &m : res ] 
 + (Pr [Game0(A,Oracle1b_CMA).main() @ &m : Oracle1b_CMA.bad ] + gamma + bound1 + bound2 + gamma).

rewrite hop1 addrC -!addrA.
apply: (ler_trans _ _ _ (hop1a &m) _); rewrite addrC ler_add2l.
apply: (ler_trans _ _ _ (hop0 &m) _); rewrite addrC. rewrite ler_add2l.
apply: (ler_trans _ _ _ (hop2 &m) _); rewrite addrC.
apply ler_add. exact bad2_bound.
apply: (ler_trans _ _ _ (hop3 &m) _); rewrite addrC. rewrite ler_add2l.
rewrite hop4 hop5. 
apply: (ler_trans _ _ _ (hop6 &m) _); rewrite addrC ler_add2l.
exact KOA_bound.
qed.

end section PROOF.

end OpBased.
