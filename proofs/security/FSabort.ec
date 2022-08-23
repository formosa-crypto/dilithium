(* ---------------------------------------------------------------------------------------------- 
   
   Verification of the proof of the Fiat-Shamir transform
   using lossy identification schemes by
   Eike Kiltz and Vadim Lyubashevsky and Christian Schaffner 
   in https://eprint.iacr.org/2017/916  
   
   ---------------------------------------------------------------------------------------------- *)
require import Int Real List FSet Distr RealExp SmtMap.
require import DistrExtras.
require DigitalSignaturesRO PROM ReprogOnce.

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

op [lossless uniform] dC : C distr.

clone import DigitalSignaturesRO as DSS with 
type DS.pk_t <- PK,
type DS.sk_t <- SK,
type DS.msg_t <- M,
type DS.sig_t <- Sig,
type PRO.in_t <- W*M,
type PRO.out_t <- C, 
op   PRO.dout <- fun _ => dC.

import DSS.PRO.
import DSS.DS.Stateless.

(* ******** Defining the signature scheme (generic FS signature) ************* *)
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

theory T1.

(* ********************* IDS based on operators ****************** *) 

(* This will simplify the proof here but may render it less
   generic. Will have to see if this is usable. *)

op keygen : (PK * SK) distr.
op commit : SK -> (W * Pstate) distr.
op response : SK -> C -> Pstate -> Z option. (* TODO: should be respond *)
op verify : PK -> W -> C -> Z -> bool.

const alpha, gamma : real.
axiom foo : mu keygen 
               (fun k : PK * SK => p_max (dfst (commit k.`2)) <= alpha) >= 1%r - gamma.

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

(*

module (CMA_KOA_Red_Oracle (Sim : HVZK_Sim, O: PRO.RO): SOracle_CMA)  = {    
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

*)

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

section PROOF. 

declare module A <: Adv_EFCMA_RO{-RO,-P,-V,-HVZK_HE_Oracle,-HVZK_Sim_Oracle, -O_CMA_Default}.

declare axiom A_ll : forall (R <: Hash{-A} ) (O <: SOracle_CMA{-A} ),
  islossless O.sign => islossless R.get => islossless A(R, O).forge.

(*
declare axiom A_query_bound &m :
 (forall (SO <: SOracle_CMA) (RO <: QRO_i),
 hoare[ A(Wrapped_QRO(RO), Wrap_SO(SO)).forge : 
     Wrapped_QRO.ch = 0 /\ Wrap_SO.qc = 0
     ==> Wrapped_QRO.ch <= ro_bound /\ Wrap_SO.qc <= qs_bound]).
*)

module Game0 (A:Adv_EFCMA_RO,O:Oracle_CMA) = EF_CMA_RO(IDS_Sig(P,V),A,RO,O).

declare module Sim <: HVZK_Sim {-RO,-P,-V,-HVZK_HE_Oracle,-HVZK_Sim_Oracle,-A}.

declare axiom Sim_perfect_HVZK k : k \in keygen => 
  equiv [ Honest_Execution(P,V).get_trans ~ Sim.get_trans : 
          arg{1} = k /\ arg{2} = k.`1 ==> ={res}].

(* ----------------------------------------------------------------------*)
(*                            First game hop:                            *)
(* Simply replace the generic game by one that uses our scheme           *)
(*             (Oracle is defined above)                                 *)
(* ----------------------------------------------------------------------*)

(* CMA oracle for EF-CMA game that is tailored to the given IDS_Sig 
   (First game hop switches from default orcale to this one) *)

print DS.Stateless.BaseOracle.

local module (Oracle1_CMA : Oracle_CMA) (S : Scheme)  = {
    include var O_CMA_Default(S) [-sign]

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
        c <@ RO.get((w,m));
        oz <- response sk c pstate;
        k <- k + 1;
      } 
      return (w,oget oz);      
    }
  }.
 
(*   *)   
local lemma hop1 &m : 
  Pr [ Game0(A, O_CMA_Default).main() @ &m : res] = 
  Pr [ Game0(A, Oracle1_CMA).main() @ &m : res].
proof.
byequiv => //. proc. inline{1} 2; inline {2} 2.
seq 4 4 : (={glob O_CMA_Default,RO.m, m, sig,pk,sk}); last by sim.
call (: ={RO.m,glob O_CMA_Default}); [|by sim|by inline*; auto => />].
proc; inline{1} 1; swap{1} 8 -2; wp.
while (={oz,w,m,glob O_CMA_Default, glob RO} 
       /\ sk{1} = O_CMA_Default.sk{2} 
       /\ m0{1} = m{2}); by inline*; auto => />.
qed.

local module (Oracle1b_CMA : Oracle_CMA) (S : Scheme)  = {
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
     var c,k;
     var w <- witness;
     var oz <- None;
     qs <- rcons qs m;

     k <- 0;
     while (oz = None /\ k < reject_bound) { 
       (w, pstate) <$ commit sk;
       c <@ RO.get((w,m));
       oz <- response sk c pstate;
       k <- k+1;
     } 
     bad <- bad \/ oz = None; 
     return if oz <> None then (w,oget oz) else witness;
   }
}.

local lemma hop1a &m : 
     Pr [Game0(A,Oracle1_CMA).main()  @ &m : res] 
  <=   Pr [Game0(A,Oracle1b_CMA).main() @ &m : res /\ ! Oracle1b_CMA.bad ] 
     + Pr [Game0(A,Oracle1b_CMA).main() @ &m :          Oracle1b_CMA.bad ].
proof.
byequiv => //.
proc; inline*; wp. 
(*
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
*)
admit.
qed.

(* ----------------------------------------------------------------------*)
(*                           Second game hop:                            *)
(* First real modification of oracle: First sample c, then reprogram RO  *)
(*                                                                       *)
(* ----------------------------------------------------------------------*)

(* Second SIGN oracle: First samples challenge, then programs the QRO. This
   handles the reprogramming bound  *)
local module (Oracle2_CMA : Oracle_CMA) (S : Scheme)  = {
    import var O_CMA_Default(S)
    include var Oracle1b_CMA(S) [-sign]
    var bad2 : bool

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
        bad2 <- bad2 \/ (w,m) \in RO.m;
        c <$ dC; 
        RO.set((w,m),c);
        oz <- response sk c pstate;
        k <- k+1;
      } 
      (* bad <- bad || oz = None;  *)
      return (w,oget oz);      
   }
}.

local lemma hop2 &m : 
  Pr [Game0(A,Oracle1b_CMA).main() @ &m : res ] 
  <=   Pr [Game0(A,Oracle2_CMA).main() @ &m : res /\ !Oracle2_CMA.bad2]
     + Pr [Game0(A,Oracle2_CMA).main() @ &m : Oracle2_CMA.bad2].
admitted.

local module (Oracle3_CMA : Oracle_CMA) (S : Scheme)  = {
    import var O_CMA_Default(S)
    include var Oracle1b_CMA(S) [-sign]
    var bad2 : bool

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

clone ReprogOnce as R1 with 
  type M <- M,
  type W <- W,
  type C <- C,
  op dC <- dC.
  (* type ST <- Pstate, *)
  (* theory RRej.OnlyRej.RO <- DSS.PRO. *)

print R1.adv_bound.

(* This should be the actual bound once adv_bound has been fixed *)
op magic_number : real. 

local lemma hop3 &m : 
     Pr [Game0(A,Oracle2_CMA).main() @ &m : res ] 
  <= Pr [Game0(A,Oracle3_CMA).main() @ &m : res ] + magic_number.
admitted.

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
    while (ot = None /\ k < reject_bound) { 
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
    (pk, sk) <$ keygen;
    OGame1.init(sk,pk);
    (m, sig) <@ A(RO,OGame1).forge(pk);
    is_valid <@ IDS_Sig(P,V,RO).verify(pk, m, sig);
    is_fresh <@ OGame1.fresh(m);
    nrqs <@ OGame1.nr_queries();
    
    return nrqs <= q_efcma /\ is_valid /\ is_fresh;
  }
}.

local lemma hop4 &m : 
  Pr [Game0(A,Oracle3_CMA).main() @ &m : res ] = Pr [Game1(A).main() @ &m : res ].
proof.
byequiv (: ={glob A} ==> _) => //; proc; inline{1} 2. 
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
    while (ot = None /\ k < reject_bound) { 
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
    (pk, sk) <$ keygen;
    OGame2.init(pk);
    (m, sig) <@ A(RO,OGame2).forge(pk);
    is_valid <@ IDS_Sig(P,V,RO).verify(pk, m, sig);
    is_fresh <@ OGame1.fresh(m);
    nrqs <@ OGame1.nr_queries();
    
    return nrqs <= q_efcma /\ is_valid /\ is_fresh;
  }
}.

(* We only handle the case where the HVZK advantate is actually O *)
local lemma hop4 &m : 
  Pr [Game1(A).main() @ &m : res ] = Pr [Game2(A).main() @ &m : res ].





(* The KOA_Forger succeeds if A succeeds *)

(* local lemma hop5 &m :  *)
(*   Pr [Game4(Rep_QRO, A, Sim).main() @ &m : res] <= *)
(*   Pr [EF_KOA_RO(IDS_Sig(P, V), KOA_Forger(A, Sim), QRO).main() @ &m : res]. *)

(* lemma main_result &m :  *)
(*   Pr [EF_CMA_RO(IDS_Sig(P, V), A, QRO, O_CMA_Default).main() @ &m : res] *)
(*     <=  Pr [EF_KOA_RO(IDS_Sig(P, V), KOA_Forger(A, Sim), QRO).main() @ &m : res]  *)
(*        +  `|Pr [HVZK_Game (Sim, P, V, Red_HVZK(A)).main(qs_bound, false) @ &m : res] - *)
(*              Pr [HVZK_Game (Sim, P, V, Red_HVZK(A)).main(qs_bound, true) @ &m : res]| *)
(*        +  (3%r/2%r) * rep_ctr%r * sqrt (query_ctr%r*p_max_bound). *)


