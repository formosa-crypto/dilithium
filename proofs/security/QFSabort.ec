(* ---------------------------------------------------------------------------------------------- 

First (failed/incomplete) attempt at generalizing Andreas Hülsing's
QROM Fiat-Shamir proof to aborts. Fails due to the reporogramming
inside the while loop barring us from replacing the loop body with a
call to the Honest_Execution transcript oracle: the oracle does not
provide challenge and comittment when the response phase fails.
   
   ---------------------------------------------------------------------------------------------- *)
require import Int Real List FSet Distr RealExp.
require QDigitalSignaturesRO T_QROM.

require import IDSabort.
import IDS.
(* *********************************************************************** *)
(*                      IDS-based Signatures                               *)
(* *********************************************************************** *)


(* ********************* Cloning Signature Theory ************************ *) 

(* Defining used types for:
   - Messages
   - Signatures
   and defining an (abstract) bound on the number of signature queries  *)
type M.
type Sig = W*Z.
(*  bound on number of sig queries *)
op qs_bound : int.
(* bound on number of ro queries *)
op ro_bound : int.
axiom gez_sb : 0 <= qs_bound.

(* maximal number of iterations allowed for signing *)
op reject_bound : { int | 0 < reject_bound } as reject_bound_gt0.


clone import QDigitalSignaturesRO as DSS with 
type pk_t <- PK,
type sk_t <- SK,
type msg_t <- M,
type sig_t <- Sig,
type RO.from <- W*M,
type RO.hash <- C,
op Stateless.q_efcma <- qs_bound
 proof Stateless.ge0_qefcma by rewrite gez_sb.


import DSS.Stateless.
import DSS.Stateless_RO.
import DSS.RO.

(* ******** Defining the signature scheme (generic FS signature) ************* *)
module (IDS_Sig (P: Prover, V:Verifier) : Scheme_RO) (O:QRO) : Scheme = {
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
      c <@ O.h {(w,m)};
      oz <@ P.response(sk,c);
    }
    return (w,oget oz);
  }
  
  proc verify(pk:PK, m:M, s:Sig):bool = {
    var result,c,w,z;
    (w,z) <- s;
    c <@ O.h{(w,m)};
    result <@ V.verify(pk,w,c,z);
    return result; 
  }
}.

theory T1.

(* ********************* IDS based on operators ****************** *) 

(* This will simplify the proof here but may render it less
   generic. Will have to see if this is usable. *)

op verify : PK -> W -> C -> Z -> bool.
op dC : C distr = dhash.

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

op keygen : (PK * SK) distr.
op commit : SK -> (W * Pstate) distr.
op response : SK -> C -> Pstate -> Z option.

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

(*****  Cloning theory for reprogrammable QROMs **************)
(* -- tricky part: Aligning with the QROM definition used in 
                   the signature theory                      *)
require T_Repro.
clone import T_Repro.
clone import Reprogram with
  type T_QROM.from <- (W*M),
  type T_QROM.hash <- C,
  theory T_QROM.MUFF <- RO.MUFF,
  op T_QROM.dhash <- RO.dhash, 
  type side <- Pstate,
  (* TOTHINK: Are these the actual bounds *)
  op rep_ctr = reject_bound * qs_bound,
  op query_ctr = reject_bound * qs_bound + ro_bound + 1. (* ??? *)


(* ----------------------------------------------------------------------*)
(*                           Start proof                                 *)
(* ----------------------------------------------------------------------*)

(* The following is the actual reduction that can break EF_KOA using 
   an EF_CMA adversary. The first module is the sign oracle the reduction 
   implements, and the second module is the reduction itself. *)

module (CMA_KOA_Red_Oracle (Sim : HVZK_Sim, O: QRO_r): SOracle_CMA)  = {    
    include var BaseOracle

    var pk: PK

    proc init(pki: PK) : unit = {
      pk <- pki;
      qs <- [];
    }

    proc sign(m: M) : Sig = {
      var sig: Sig;
      var w,c,z;
      var t <- None;

      qs <- rcons qs m;
      while (t = None) {  
        t <@ Sim.get_trans(pk);
      } 
      (w, c, z) <- oget t;
      O.set((w,m),c);
      return (w,z);      
    }
}.


 (* The actual reduction. (This builds step-wise, 
    see the reduction below for the steps)
  *)


module (KOA_Forger (A : Adv_EFCMA_RO, Sim : HVZK_Sim): Adv_EFKOA_RO) (RO: QRO) = {
    
    module R = Wrapped_QRO(RO)
    module O = CMA_KOA_Red_Oracle(Sim, R)
    module A = A(R,O)

    proc forge(pk:PK) : (M*Sig) = {
      var m': M;
      var sig': Sig;

      R.init();
      O.init(pk);
      (m', sig') <@ A.forge(pk);
      return (m',sig'); 
    }
  }.

(* -------------- Reduction to HVZK --------------------- *)
(* First part: The oracle. Uses a transcript oracle  *)

(*
module (OracleRed_HVZK ( OSim : HVZK_Oracle ) : SOracle_CMA)  = {
    include var BaseOracle

    proc init() : unit = {
      qs <- [];
    }

    proc sign(m: M) : Sig = {
      var sig: Sig;
      var w,c,z;

      qs <- rcons qs m;
      (w, c, z) <@ OSim.get_trans();
      Rep_QRO.set((w,m),c);
      return (w,z);      
    }
}.

(* Reduction: Simulates Game3 or Game4 to depending on the given oracle *)
module (Red_HVZK ( A : Adv_EFCMA_RO) : HVZK_Distinguisher) (OSim: HVZK_Oracle) = {
  module R = Rep_QRO
  module O = OracleRed_HVZK(OSim)
  module A = A(R,O)

  proc distinguish (pk: PK): bool = {
      var m': M;
      var sig': Sig;
      var is_valid: bool;
      var is_fresh: bool;
      var w', c', z', nrqs;

      R.init();
      O.init();
      (m', sig') <@ A.forge(pk);
      (w', z') <- sig'; 
      c' <@ R.h {(w',m')};
      is_valid <- verify pk w' c' z';
      is_fresh <@ O.fresh(m');
      nrqs <@ O.nr_queries();

      return is_valid /\ is_fresh /\ nrqs <= qs_bound;
  }
}.

*)

(* Old approach to bound number of queries. 
We should actually solve this using the cost logic 

module Wrap_SO (O: SOracle_CMA) : SOracle_CMA = {
  var qc : int
  
  proc sign(m : M) : Sig = {
    var sig;
    
    qc <- qc + 1;
    sig <@ O.sign(m);
    
    return sig;
    }
}.
*)

section.


(* For all adversaries A ... *)
declare module A <: Adv_EFCMA_RO {-QRO, -Rep_QRO, -RepO, -O_CMA_Default, -P, -V, -HVZK_HE_Oracle, -HVZK_Sim_Oracle, -CMA_KOA_Red_Oracle, -Wrapped_QRO(* , -OracleRed_HVZK *)}.
(* For all simulators Sim ... *)
declare module Sim <: HVZK_Sim {-QRO, -Rep_QRO, -O_CMA_Default, -P, -V, -A, -HVZK_HE_Oracle, -HVZK_Sim_Oracle, -CMA_KOA_Red_Oracle, -Wrapped_QRO(* , -OracleRed_HVZK *)}.    
(* Old approach to bound number of queries. 
We should actually solve this using the cost logic 

declare axiom A_query_bound &m :
 (forall (SO <: SOracle_CMA) (RO <: QRO_i),
 hoare[ A(Wrapped_QRO(RO), Wrap_SO(SO)).forge : 
     Wrapped_QRO.ch = 0 /\ Wrap_SO.qc = 0
     ==> Wrapped_QRO.ch <= ro_bound /\ Wrap_SO.qc <= qs_bound]).
*)

declare axiom A_ll : forall (R <: QRO{-A} ) (O <: SOracle_CMA{-A} ),
  islossless O.sign => islossless R.h => islossless A(R, O).forge.

(* ----------------------------------------------------------------------*)
(*                            First game hop:                            *)
(* Simply replace the generic game by one that uses our scheme           *)
(*             (Oracle is defined above)                                 *)
(* ----------------------------------------------------------------------*)

(* CMA oracle for EF-CMA game that is tailored to the given IDS_Sig 
   (First game hop switches from default orcale to this one) *)
 module (Oracle1_CMA : Oracle_CMA) (S : Scheme)  = {
    include var BaseOracle
    import var O_CMA_Default 

    proc init(ski: SK) : unit = {
      sk <- ski;
      qs <- [];
    }

    proc sign(m: M) : Sig = {
      var pstate;
      var sig: Sig;
      var c,k;
      var w <- witness;
      var oz <- None;
      qs <- rcons qs m;

      k <- 0;
      while (oz = None) { 
        (w, pstate) <$ commit sk;
        c <@ Rep_QRO.h{(w,m)};
        oz <- response sk c pstate;
        k <- k + 1;
      } 
      return (w,oget oz);      
    }
  }.
 
(*   *)   
lemma hop1 &m : 
  Pr [EF_CMA_RO(IDS_Sig(P, V), A, QRO, O_CMA_Default).main() @ &m : res] =
  Pr [EF_CMA_RO(IDS_Sig(P, V), A, Rep_QRO, Oracle1_CMA).main() @ &m : res].
proof.
byequiv => //. proc; inline *; wp.
call (: ={glob O_CMA_Default, glob BaseOracle} 
        /\ QRO.h{1} = Rep_QRO.f{2} 
        /\ Rep_QRO.prog_list {2} = []). 
+ proc; inline*. swap{1} 8 -2. wp. 
  while (={oz,w,m,glob O_CMA_Default, glob BaseOracle} 
         /\ sk{1} = O_CMA_Default.sk{2} /\ m0{1} = m{2}
         /\ QRO.h{1} = Rep_QRO.f{2} 
         /\ Rep_QRO.prog_list {2} = []); first by auto => /= />.
  by auto => />.
+ by proc; inline*; auto.
by auto => />.
qed.


local module (Oracle1a_CMA : Oracle_CMA) (S : Scheme)  = {
  include var BaseOracle
  import var O_CMA_Default 
  var bad : bool

   proc init(ski: SK) : unit = {
     sk <- ski;
     qs <- [];
     bad <- false;
  }

   proc sign(m: M) : Sig = {
     var pstate;
     var sig: Sig;
     var c,k;
     var w <- witness;
     var oz <- None;
     qs <- rcons qs m;

     k <- 0;
     while (oz = None /\ k < reject_bound) { 
       (w, pstate) <$ commit sk;
       c <@ Rep_QRO.h{(w,m)};
       oz <- response sk c pstate;
       k <- k+1;
     } 
     bad <- bad || oz = None; 
     return  (w,oget oz);      
   }
}.

local lemma hop1a &m : 
  Pr [EF_CMA_RO(IDS_Sig(P, V), A, Rep_QRO, Oracle1_CMA).main()  @ &m : res]
  <=  Pr [EF_CMA_RO(IDS_Sig(P, V), A, Rep_QRO, Oracle1a_CMA).main() @ &m : 
          res /\ ! Oracle1a_CMA.bad ] +
      Pr [EF_CMA_RO(IDS_Sig(P, V), A, Rep_QRO, Oracle1a_CMA).main() @ &m : 
          Oracle1a_CMA.bad ].
proof.
byequiv => //.
proc; inline*; wp. 
conseq (: _ ==> !Oracle1a_CMA.bad{2} => ={glob Rep_QRO, BaseOracle.qs, m, sig, pk}). 
- by auto => /> /#.
call (: Oracle1a_CMA.bad, ={glob Rep_QRO, BaseOracle.qs, O_CMA_Default.sk}).
- exact A_ll.
- proc; wp. conseq />.  
  splitwhile{1} 5 : (k < reject_bound).
  seq 5 5 : (={w,oz,Rep_QRO.ch, BaseOracle.qs}); 1: by sim. 
  case (oz{2} = None); 2: by rcondf{1} 1; by auto.
  conseq (:_ ==> true) (: _ ==> true : =1%r) _; 1: smt(). 
  admit.
- move => *. islossless. admit. 
- move => *; proc. admit.
- proc. auto.
- move => *; islossless. 
- move => *; proc; auto. 
by auto => /> /#.
qed.

(* ----------------------------------------------------------------------*)
(*                           Second game hop:                            *)
(* First real modification of oracle: First sample c, then reprogram RO  *)
(*                                                                       *)
(* ----------------------------------------------------------------------*)

(* Second SIGN oracle: First samples challenge, then programs the QRO. This
   handles the reprogramming bound  *)
local module (Oracle2_CMA : Oracle_CMA) (S : Scheme)  = {
    include var BaseOracle
    import var O_CMA_Default
    import var Oracle1a_CMA

    proc init(ski: SK) : unit = {
      sk <- ski;
      qs <- [];
      bad <- false;
    }

    proc sign(m: M) : Sig = {
      var pstate;
      var sig: Sig;
      var c,k;
      var w <- witness;
      var oz <- None;
      qs <- rcons qs m;

      k <- 0;
      while (oz = None /\ k < reject_bound) { 
        (w, pstate) <$ commit sk;
        (* new part: first sample c, then program Rep_QRO *) 
        c <$ dC; 
        Rep_QRO.set((w,m),c);
        oz <- response sk c pstate;
        k <- k+1;
      } 
      bad <- bad || oz = None; 
      return (w,oget oz);      
   }
}.

(* *** Core of the reduction to reprogramming game: Oracle used by the 
       reduction (distinguisher) that lets the RepO-Oracle O handle the 
       computation of the commitment and computation of the challenge. 
*)
module (Distinguisher_Oracle (RO: QRO, O: RepO_t) : Oracle_CMA) (S : Scheme)  = {
    include var BaseOracle
    import var O_CMA_Default

    proc init(ski: SK) : unit = {
      sk <- ski;
      qs <- [];
    }

    proc sign(m: M) : Sig = {
      var pstate;
      var sig: Sig;
      var p : pT;
      var c,wm, w,k;
      var oz <- None;

      w <- witness;
      qs <- rcons qs m;   

      k <- 0;
      while (oz = None /\ k < reject_bound) {     
        p <- dmap (commit sk) (fun (x:W*Pstate) => ((x.`1,m),x.`2));
        (wm, pstate) <@ O.repro(p);
        w <- wm.`1;
        c <@ RO.h {(w, m)};
        oz <- response sk c pstate;
        k <- k+1;
      }
      return (w,oget oz);      
    }
}.

(* Necessary as we are given an already initialized oracle that we want to hand over to the signature game. So we have to add an empty init() method. *)
module DummyRO (RO : QRO) : QRO_i = {
   include RO
   proc init() = {}
}.

(* The actual reduction to the reprogramming game: 
   It is just running the signature game with the above oracle 
   in place of the signing oracle *) 
module D(RO: QRO, O: RepO_t) = {
   proc distinguish = EF_CMA_RO(IDS_Sig(P, V), A, DummyRO(RO), Distinguisher_Oracle(RO, O)).main
}.

(* TODO: preserve bad event, requires an D that also checks that bad wasn's set *) 
local lemma hop2 &m : 
    `|Pr [EF_CMA_RO(IDS_Sig(P, V), A, Rep_QRO, Oracle1a_CMA).main() @ &m : res] -  
      Pr [EF_CMA_RO(IDS_Sig(P, V), A, Rep_QRO, Oracle2_CMA).main() @ &m : res]| <= 
       (3%r/2%r) * rep_ctr%r * sqrt (query_ctr%r*p_max_bound).
proof.
(* We prove the lemma by first proving the following in two steps:
   `|Pr [EF_CMA_RO(IDS_Sig(P, V), A, Rep_QRO, Oracle1_CMA).main() @ &m : res] -  
    Pr [EF_CMA_RO(IDS_Sig(P, V), A, Rep_QRO, Oracle2_CMA).main() @ &m : res]|
   = 
   `|Pr[ReproGame(QRO, D).main(false) @ &m:res]
   - Pr[ReproGame(QRO, D).main(true) @ &m:res]|.
*)
have -> : 
   Pr[EF_CMA_RO(IDS_Sig(P, V), A, Rep_QRO, Oracle1a_CMA).main() @ &m : res] 
    = Pr[ReproGame(QRO,D).main(false) @ &m:res].
byequiv (: ={glob A} /\ b{2} = false ==> ={res}) => //. proc. inline*. wp.
conseq (: _ ==> ={m,sig,pk,sk,BaseOracle.qs} 
             /\ ={prog_list}(Rep_QRO,Wrapped_QRO)
             /\ Rep_QRO.f{1} = QRO.h{2}
        ); first by move => />. 
call (: ={BaseOracle.qs,O_CMA_Default.sk} 
          /\ RepO.b{2} = false
          /\ ={prog_list}(Rep_QRO,Wrapped_QRO) /\ Rep_QRO.prog_list{1} = []
          /\ Rep_QRO.f{1} = QRO.h{2}); first last.
- by proc; inline*; auto.
- by auto.
proc; inline*; wp. 
while (  ={BaseOracle.qs,O_CMA_Default.sk,w,oz,k,m} 
          /\ RepO.b{2} = false
          /\ ={prog_list}(Rep_QRO,Wrapped_QRO) /\ Rep_QRO.prog_list{1} = []
          /\ Rep_QRO.f{1} = QRO.h{2}); last by auto.
rcondf{2} 6; 1: by auto. 
conseq (: _ ==> ={w,oz,k}); 1: by auto. wp.
rnd (fun (x:W*Pstate) => ((x.`1,m{2}),x.`2)) (fun (x: (W*M)*Pstate) => (x.`1.`1,x.`2)).
auto => /> &1 &2. 
split => [|_]; 1: by move => [[w m] st] /supp_dmap />.
split => [|_]. 
- move => [[w m] st] /supp_dmap -[[w' st']] /> ?. 
  by rewrite dmap1E /(\o); apply mu_eq => /#.
case => w st /> /=. smt(supp_dmap).

have -> : 
   Pr[EF_CMA_RO(IDS_Sig(P, V), A, Rep_QRO, Oracle2_CMA).main() @ &m : res] 
    = Pr[ReproGame(QRO,D).main(true) @ &m:res].
byequiv (: ={glob A} /\ b{2} = true ==> ={res}) => //. proc. inline*. wp.
conseq (: _ ==> ={m,sig,pk,sk,BaseOracle.qs} 
             /\ ={prog_list}(Rep_QRO,Wrapped_QRO)
             /\ Rep_QRO.f{1} = QRO.h{2}
        ); first by move => />. 
call (: ={BaseOracle.qs,O_CMA_Default.sk} 
          /\ RepO.b{2} = true
          /\ ={prog_list}(Rep_QRO,Wrapped_QRO)
          /\ Rep_QRO.f{1} = QRO.h{2}); first last.
- by proc; inline*; auto.
- by auto.
proc; inline*; wp. 
while (  ={BaseOracle.qs,O_CMA_Default.sk,w,oz,k,m} 
          /\ RepO.b{2} = true
          /\ ={prog_list}(Rep_QRO,Wrapped_QRO)
          /\ Rep_QRO.f{1} = QRO.h{2}); last by auto.
rcondt{2} 6; 1: by auto. 
conseq (: _ ==> ={w,oz,k} /\ Rep_QRO.prog_list{1} = Wrapped_QRO.prog_list{2} ); 1: by auto.
wp. rnd. 
rnd (fun (x:W*Pstate) => ((x.`1,m{2}),x.`2)) (fun (x: (W*M)*Pstate) => (x.`1.`1,x.`2)).
auto => /> &1 &2. 
split => [|_]; 1: by move => [[w m] st] /supp_dmap />.
split => [|_]. 
- move => [[w m] st] /supp_dmap -[[w' st']] /> ?. 
  by rewrite dmap1E /(\o); apply mu_eq => /#.
case => w st /> /=. smt(supp_dmap).
apply (qrom_reprogramming D QRO &m _).
admit.
qed.

(* ----------------------------------------------------------------------*)
(*                           Third game hop:                             *)
(* Second modification of oracle:                                        *)
(*             use Honest_Execution to obtain transcript                 *)
(* ----------------------------------------------------------------------*)

(* new SIGN oracle *)
local module (Oracle3_CMA : SOracle_CMA)  = {
    include var BaseOracle 
    var sk: SK
    var pk: PK
    var bad : bool
    
    module HE = Honest_Execution(P,V)

    proc init(pki: PK, ski: SK) : unit = {
      pk <- pki;
      sk <- ski;
      qs <- [];
      bad <- false;
    }

    proc sign(m: M) : Sig = {
      var sig: Sig;
      var w,c,z,k;
      var ot <- None;
      qs <- rcons qs m;
      
      (* new part: instead of computing w,c,z, we get them from an external oracle *)
      k <- 0;
      while (ot = None /\ k < reject_bound) { 
        ot <@ HE.get_trans(pk,sk);
        Rep_QRO.set((w,m),c); (* we don't have w and c *)
        k <- k+1;
      } 
      bad <- bad || ot = None;
      (w,c,z) <- oget ot;
      return (w, z);      
    }
}.

 (* This time we also have to change the game as the oracle needs the public key. 
    Game 3 is otherwise the EF_CMA_RO game with IDS_Sig.verify inlined. *)
 local module Game3(R: QRO_ri, A : Adv_EFCMA_RO) = {
    module O = Oracle3_CMA
    module A = A(R,O)

    proc main() : bool = {
      var pk: PK;
      var sk: SK;
      var m': M;
      var sig': Sig;
      var is_valid: bool;
      var is_fresh: bool;
      var w', c', z', nrqs;

      (pk, sk) <$ keygen;
      R.init();
      O.init(pk,sk);
      (m', sig') <@ A.forge(pk);
      (w', z') <- sig'; 
      c' <@ R.h {(w',m')};
      is_valid <- verify pk w' c' z';
      is_fresh <@ O.fresh(m');
      nrqs <@ O.nr_queries();

      return is_valid /\ is_fresh /\ nrqs <= qs_bound; 
    }
  }.

(* This is simply a rewriting proof, nothing interesting *)
local lemma hop3 &m : 
  Pr [EF_CMA_RO(IDS_Sig(P, V), A, Rep_QRO, Oracle2_CMA).main() @ &m : 
      res /\ !Oracle1a_CMA.bad] =
  Pr [Game3(Rep_QRO, A).main() @ &m : res /\ !Oracle3_CMA.bad].
proof.
(* byequiv (: ={glob A} ==> ={res}) => //. *)
(* proc; inline*; auto. *)
(* call (: ={glob Rep_QRO,BaseOracle.qs}  /\ ={sk}(O_CMA_Default,Oracle3_CMA)). *)
(* - proc. wp.  *)
(*   while (={k,glob Rep_QRO,BaseOracle.qs} /\ ={sk}(O_CMA_Default,Oracle3_CMA)). *)

byequiv (: ={glob A} ==> 
            (res /\ !Oracle1a_CMA.bad){1} <=> (res /\ !Oracle3_CMA.bad){2}) => //.
proc; inline *; auto.
call (_: Oracle3_CMA.bad, 
      ={glob Rep_QRO,BaseOracle.qs} 
      /\ ={bad}(Oracle1a_CMA,Oracle3_CMA)
      /\ ={sk}(O_CMA_Default,Oracle3_CMA),
      Oracle1a_CMA.bad{1} /\ Oracle3_CMA.bad{2}).
- exact: A_ll.
- proc. wp. inline Oracle3_CMA.HE.get_trans P.commit V.challenge P.response.
  while (={glob Rep_QRO,BaseOracle.qs,k} 
         /\ ={sk}(O_CMA_Default,Oracle3_CMA) 
         /\ (omap (fun z => (w,z)) oz){1} = (omap (fun x: W * C * Z  => (x.`1,x.`3)) ot){2}).
  + inline*; auto => /> &1 &2 ? -[w st] ? c /=.
    admit.
  admit.
- move => &2 Hbad. conseq />. proc. wp. conseq (:_ ==> true). smt(). 
  (* need to prove termination, need sound rule *) admit.
- move => &1. admit.
- proc. conseq />. sim.
- by move => &1 *; proc; auto.
- by move => &1 *; proc; auto.
by swap{1} 4 -3; auto => /> /#.
qed.


(* ----------------------------------------------------------------------*)
(*                          Fourth game hop:                             *)
(* Third modification of oracle:                                         *)
(* use HVZK Simulator in place of Honest_Execution to obtain transcript  *)
(* ----------------------------------------------------------------------*)

(* new oracle that uses Sim *)
local module (Oracle4_CMA (Sim : HVZK_Sim): SOracle_CMA)  = {
    include var BaseOracle
    var pk: PK

    proc init(pki: PK) : unit = {
      pk <- pki;
      qs <- [];
    }

    proc sign(m: M) : Sig = {
      var sig: Sig;

      var w,c,z;

      qs <- rcons qs m;

      (w, c, z) <@ Sim.get_trans(pk);
      
      Rep_QRO.set((w,m),c);

      return (w,z);      
    }
}.

 (* This is essentially the game from before, 
    we just do not give the sk to the oracle 
    and use Sim
  *)
 local module Game4(R: QRO_ri, A : Adv_EFCMA_RO, Sim : HVZK_Sim) = {
    module O = Oracle4_CMA(Sim)
    module A = A(R, O)

    proc main() : bool = {
      var pk: PK;
      var sk: SK;
      var m': M;
      var sig': Sig;
      var is_valid: bool;
      var is_fresh: bool;
      var w', c', z', nrqs;

      (pk, sk) <$ keygen;
      R.init();
      O.init(pk);

      (m', sig') <@ A.forge(pk);
      
      (w', z') <- sig'; 
      c' <@ R.h {(w',m')};
      is_valid <- verify pk w' c' z';
      is_fresh <@ O.fresh(m');
      nrqs <@ O.nr_queries();

      return is_valid /\ is_fresh /\ nrqs <= qs_bound; 
    }
  }.


local lemma hop4 &m : 
  `|  Pr [Game3(Rep_QRO, A).main() @ &m : res] -
      Pr [Game4(Rep_QRO, A, Sim).main() @ &m : res]|
   =
   `|Pr [HVZK_Game (Sim, P, V, Red_HVZK(A)).main(qs_bound, false) @ &m : res] -
     Pr [HVZK_Game (Sim, P, V, Red_HVZK(A)).main(qs_bound, true) @ &m : res]|.
proof.
have -> : Pr [Game3(Rep_QRO, A).main() @ &m : res] 
           = Pr [HVZK_Game (Sim, P, V, Red_HVZK(A)).main(qs_bound, false) @ &m : res].  
byequiv => //. proc. rcondf {2} 2. auto. conseq />. auto.
inline *.
auto. call ( _ : ={glob Rep_QRO} /\  ={pk,sk}(Oracle3_CMA,HVZK_HE_Oracle) 
               /\ ={BaseOracle.qs}).
+ proc. inline *. wp. rnd. wp. rnd. by auto. 
+ proc. by auto. 
+ wp. by auto => />.
have -> : Pr [Game4(Rep_QRO, A, Sim).main() @ &m : res] =
            Pr [HVZK_Game (Sim, P, V, Red_HVZK(A)).main(qs_bound, true) @ &m : res].
byequiv => //. proc. rcondt {2} 2. auto. conseq />. auto.
inline *.
auto. call ( _ : ={glob Rep_QRO, glob Sim} /\  ={pk}(Oracle4_CMA,HVZK_Sim_Oracle) 
               /\ ={BaseOracle.qs}).
+ proc. inline *. wp. call ( _ : true). by auto.
+ proc. by auto.
+ wp. by auto => />.
done.
qed.


(* The KOA_Forger succeeds if A succeeds *)

print EF_KOA.

local lemma hop5 &m : 
  Pr [Game4(Rep_QRO, A, Sim).main() @ &m : res] <=
  Pr [EF_KOA_RO(IDS_Sig(P, V), KOA_Forger(A, Sim), QRO).main() @ &m : res].
proof.
  byequiv => //. proc. inline *. wp. simplify.
  seq 7 11 : (#pre /\ ={pk,sk} /\ ={BaseOracle.qs} /\ ={pk}(Oracle4_CMA,CMA_KOA_Red_Oracle)
        /\ Rep_QRO.f{1} = QRO.h{2} /\ ={prog_list, ch}(Rep_QRO, Wrapped_QRO)
        /\ BaseOracle.qs{1} = [] /\ Rep_QRO.prog_list{1} = [] 
        /\ Rep_QRO.ch{1} = 0 /\ pk{1} = pk1{2}).
  auto. swap {2} 3 -2. by auto.
  call ( : ={glob Sim} /\  ={BaseOracle.qs} /\ ={pk}(Oracle4_CMA,CMA_KOA_Red_Oracle)
        /\ Rep_QRO.f{1} = QRO.h{2} /\ ={prog_list, ch}(Rep_QRO, Wrapped_QRO)
        /\ forall w m c, (((w,m),c) \in Rep_QRO.prog_list{1}) => (m \in BaseOracle.qs{1}) 
).
+ proc. auto. inline {1} 3. inline {2} 3. auto. call ( _ : true ). auto => /> *. by smt(mem_rcons). 
+ proc. inline *. by auto. 
+ auto. move => />. move => &mem forgery querylist proglist consistant_lists vrytrue frgrynew sizeqrylst. 
+ have -> : (QRO.h{mem} (forgery.`2.`1, forgery.`1)) = (if assoc proglist (forgery.`2.`1, forgery.`1) = None then
              QRO.h{mem} (forgery.`2.`1, forgery.`1)
            else oget (assoc proglist (forgery.`2.`1, forgery.`1))); trivial. 
+ have -> : assoc proglist (forgery.`2.`1, forgery.`1) = None; trivial. by smt(assocP).
qed.

lemma main_result &m : 
  Pr [EF_CMA_RO(IDS_Sig(P, V), A, QRO, O_CMA_Default).main() @ &m : res]
    <=  Pr [EF_KOA_RO(IDS_Sig(P, V), KOA_Forger(A, Sim), QRO).main() @ &m : res] 
       +  `|Pr [HVZK_Game (Sim, P, V, Red_HVZK(A)).main(qs_bound, false) @ &m : res] -
             Pr [HVZK_Game (Sim, P, V, Red_HVZK(A)).main(qs_bound, true) @ &m : res]|
       +  (3%r/2%r) * rep_ctr%r * sqrt (query_ctr%r*p_max_bound).
proof.
smt(hop1 hop2 hop3 hop4 hop5).
qed.
end section.
end T1.
