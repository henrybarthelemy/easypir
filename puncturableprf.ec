require import AllCore Distr FSet.

require (*--*) PRF.

(* Puncturable PRF but not a private one, we don't attempt to hide x, just f(x) *)
(* Written by Henry Barthelemy *)
type K.
type D.
type R.
type PK = {key : K; x : D option}.

op dK: { K distr | is_lossless dK } as dK_ll.
op F : K -> D -> R.

module PPRF1 = {

  (* Gets a key from distribution dK and create pK with no punture point *)
  proc init() : PK = {
    var k;
    var pk : PK;
    k <$ dK;
    pk <- {| key = k; x = None; |};
    return pk;
  }

  (* Puncture pK at point x if it is not already punctured, otherwise do nothing *)
  proc puncture(x: D, pk : PK): PK = {
    if (pk.`x = None) {
      pk <- {| key = pk.`key; x = Some x |};
    }
    return pk;
  }

  (* If pk is not puntured at x, return the value of PRF at x *)
  proc f(x: D, pk: PK): R option  = {
    var r : R option;
    r <- if pk.`x = Some x then None else Some (F pk.`key x);
    return r;
  }
}.

module PuncturablePrfCorrectnessGame = {
  proc f(xp: D, xi: D): bool = {
    var k;
    var pk;
    var x1, x2;
    k <@ PPRF1.init();
    pk <@ PPRF1.puncture(xp, k);
    x1 <@ PPRF1.f(xi, k);
    x2 <@ PPRF1.f(xi, pk);
    return x1 = x2;
  }
}.

    (* PPRF is correct if for key k, puncture point x' with resulting punctured key pk,
    PPRF.f(x, k) = PPRF.f(x, pk) for all points where x' <> x *)
lemma pprf_correctness &m xp1 xi1 : xp1 <> xi1 =>
    Pr [PuncturablePrfCorrectnessGame.f(xp1, xi1) @ &m : res = true] = 1%r.
proof.
move => xp_noteq_xi.
byphoare (_: xi <> xp ==> res = true) => // {&m}.
conseq (: _ ==> true) (: _ ==> res = true) => //.
proc; inline; wp; simplify.
rnd. skip. move => &hr xi_noteq_xp k _.
  have xi_neq_xp : (xi{hr} = xp{hr}) = false by smt().
  have simplified_if: (if xp{hr} = xi{hr} then None else Some (F k xi{hr})) = Some (F k xi{hr}) by smt().
  rewrite simplified_if; simplify; trivial.
  proc; inline; wp; simplify; rnd; skip. move => &hr H; simplify; smt(dK_ll).
  smt().
qed.

(* Security Proofs Ideal/Real Setup *)

  (* Security Notions *)
module type PPRF = {
  proc init(): unit
  proc f(_ : D): R option
  proc punc(_: D): unit
}.


module PPRF_Real: PPRF = {
  var pk : PK

  (* Gets a key from distribution dK and create pK with no punture point *)
  proc init() : unit = {
    var k;
    var pk : PK;
    k <$ dK;
    pk <- {| key = k; x = None; |};
  }

  (* Puncture pK at point x if it is not already punctured, otherwise do nothing *)
  proc punc(x: D): unit = {
    if (pk.`x = None) {
      pk <- {| key = pk.`key; x = Some x |};
    }
    
  }

  (* If pk is not puntured at x, return the value of PRF at x *)
  proc f(x: D): R option  = {
    var r : R option;
    r <- if pk.`x = Some x then None else Some (F pk.`key x);
    return r;
  }
}.

section Correctness.

lemma pprf_correctness_1 &m1 &m2 k xp xi o:
    xp <> xi
    /\ PPRF_Real.pk.`key{m1} = k
    /\ PPRF_Real.pk.`key{m2} = k
    /\ PPRF_Real.pk.`x{m1} = None
    /\ PPRF_Real.pk.`x{m2} = Some xp
    =>
     Pr[PPRF_Real.f(xi) @ &m1 : res = o] = 
     Pr[PPRF_Real.f(xi) @ &m2 : res = o].
    proof.
    move => [xp_xi_neq [m1k [mk2 [m1none mk2xp]]]].
    byequiv => //.
    proc; inline; wp; skip.
    move => &1 &2.
    smt.
  qed.
  
lemma pprf_correctness_2 &m1 &m2 k xp xi o:
    xp <> xi
    /\ PPRF_Real.pk.`key{m1} = k
    /\ PPRF_Real.pk.`key{m2} = k
    /\ PPRF_Real.pk.`x{m1} = None
    /\ PPRF_Real.pk.`x{m2} = Some xp
    =>
    equiv [PPRF_Real.f ~ PPRF_Real.f : true ==> ={res}.
    proof.
    move => [xp_xi_neq [m1k [mk2 [m1none mk2xp]]]].
    byequiv => //.
    proc; inline; wp; skip.
    move => &1 &2.
    move => [x2xieq [pk2 [x1xieq pk1]]].
    admit.
  qed.

      (*

          byequiv => //.
      proc; inline; wp; skip;
    move => &1 &2 h1. split.
    move => h2 h3;
      have same : x{1} = x{2} by smt();
      have xi_xp : x{1} = xi by smt();
      have nxp : PPRF_Real.pk{2}.`Top.x <> Some x{2} by smt.
      have eqif1 : (if PPRF_Real.pk{2}.`Top.x = Some x{2} then None
      else Some (F PPRF_Real.pk{2}.`key x{2})) = Some (F PPRF_Real.pk{2}.`key x{2}) by smt().
      rewrite eqif1.
      have pk1 : PPRF_Real.pk{1} = PPRF_Real.pk{m1} by smt.
      have h2s :  PPRF_Real.pk{1}.`Top.x = None /\ PPRF_Real.pk{1}.`key = k => Some (F PPRF_Real.pk{1}.`key x{1}) =
      o by smt().
      *)

  
end section Correctness.
 
require import FMap.
op dR: { D -> R distr | forall x, is_lossless (dR x) /\ forall x, is_full (dR x)} as dR_ll.

module PPRF_Ideal : PPRF = {
  var m : (D,R) fmap
  var punc_x : D option
  var coll : bool

  proc init(): unit = {
    m  <- empty;
    punc_x <- None;
    coll <- false;
  }

  proc punc(x:D): unit = {
    if (punc_x = None) {
      punc_x <- Some x;
    }
  }

  proc f(x:D): R option = {
    var r;
    if (x \notin m) {
      r <$ dR x;
      coll   <- coll \/ rng m r;
      m.[x]  <- r;
    }
    return if punc_x = Some x then None else Some (oget m.[x]);
  }

}.

module type PPRF_Oracles = {
  proc f(_: D): R option
}.

module type Distinguisher (P: PPRF_Oracles) = {
  proc distinguish(): bool
}.

    (* We limit our distiniguisher to have q calls *)
    (* This is to express a computationally bounded adversary through a computationally bounded oracle *)

op q : { int | 0 <= q } as ge0_q.

module DBounder (D : Distinguisher) (F : PPRF_Oracles) = {
  module FBounder = {
    var c:int

    proc f(x:D): R option = {
      var r <- witness;
      if (c < q) {
        r <@ F.f(x);
        c <- c + 1;
      }
      return r;
    }
  }

  proc distinguish(): bool = {
    var b;
    FBounder.c <- 0;
    b <@ D(FBounder).distinguish();
    return b;
  }
}.


section BoundedPPRF.

  (* 3 STEPS *)
  (* Concretely bound the real PRF to a bounding based on number of calls *)
  (* Prove PRF_Real ~ PRF_Ideal *)

declare module D <: Distinguisher {-PPRF_Real, -DBounder}.

(* Sometimes reductions can be lossy *) 
declare axiom D_ll (O <: PPRF_Oracles {-D}): islossless O.f => islossless D(O).distinguish.

module Exp_IND (P: PPRF) (D: Distinguisher) = {
  proc main(): bool = {
    var b;
    P.init();
    b <@ D(P).distinguish();
    return b;
  }
}.

op uD: { D distr | is_uniform uD /\ is_lossless uD /\ is_full uD } as uD_uf_fu.

lemma PPRF_Collision_Strong &m:
    Pr[Exp_IND(PPRF_Ideal, DBounder(D)).main() @ &m: PPRF_Ideal.coll]
      <= (q^2 - q)%r / 2%r * mu uD (pred1 witness). (* (q^2 - q) / 2 * (1/|D|) *) (* q^2 - q / 2|D| *)
proof.
  admit. 
qed.

lemma PPRF_Collision_Weak &m:
    Pr[Exp_IND(PPRF_Ideal, DBounder(D)).main() @ &m: PPRF_Ideal.coll]
      <= (q^2)%r * mu uD (pred1 witness). (* (q^2) / (1/|D|) *)
proof.
  admit. 
qed.


end section BoundedPPRF.

section RealIdealIND.

declare module D <: Distinguisher {-PPRF_Real, -PPRF_Ideal}.

lemma RealIdeal &m : Pr[Exp_IND(PPRF_Real,D).main() @ &m: res] = Pr[Exp_IND(PPRF_Ideal,D).main() @ &m: res].
proof.
  admit.
qed.

end section RealIdealIND.





(* Some other proofs reasoning about punctured PRF *)

module Experiement3 = {
  proc f(x: D): R option = {
    var r;
    var pk;
    pk <@ PPRF1.init();
    pk <@ PPRF1.puncture(x, pk);
    r <@ PPRF1.f(x, pk);
    return r;
  }
}. 

module Experiement4 = {
  proc f(x: D): R option = {
    var r;
    var pk;
    pk <@ PPRF1.init();
    r <@ PPRF1.f(x, pk);
    return r;
  }
}. 

lemma punctured_gets_none2 &m xi : Pr [Experiement3.f(xi) @ &m : res = None] = 1%r.
proof.
byphoare.    
  proc; inline; wp; simplify.
  rnd; skip; simplify; smt(dK_ll).
  trivial. trivial.
qed.

lemma notpunctured_gets_some2 &m xi : Pr [Experiement4.f(xi) @ &m : res <> None] = 1%r.
proof.
byphoare.    
  proc; inline; wp; simplify.
  rnd; skip; simplify; smt(dK_ll).
  trivial. trivial. 
qed.


(* Approaching Puncturable PRF from a more OOD way *)

module PuncturablePRF = {
  var k : K
  var x_punctured: D option  

  proc init() = {
    k <$ dK;
    x_punctured <- None;
  }

  proc puncture(x: D) = {
    x_punctured <- Some x;
  }
  
  proc f(x: D) = {
    var r : R option;
    r <- if x_punctured = Some x then None else Some (F k x);
    return r;
  }
}.

module Experiement = {
  proc f(x: D): R option = {
    var r;
    PuncturablePRF.puncture(x);
    r <@ PuncturablePRF.f(x);
    return r;
  }
}.

module Experiement2 = {
  proc f(x: D): R option = {
    var r;
    PuncturablePRF.init();
    r <@ PuncturablePRF.f(x);
    return r;
  }
}.
    
lemma punctured_gets_none &m xi : Pr [Experiement.f(xi) @ &m : res = None] = 1%r.
proof.
byphoare.    
  proc; inline; wp; simplify.
  trivial. trivial. trivial.
qed.
      
lemma notpunctured_gets_some &m xi : Pr [Experiement2.f(xi) @ &m : res <> None] = 1%r.
proof.
byphoare.    
  proc; inline; wp; simplify.
  rnd; skip; simplify; smt(dK_ll).
  trivial. trivial. 
qed.
