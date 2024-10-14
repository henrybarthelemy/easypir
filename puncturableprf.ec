require import AllCore Distr FSet.

(* Puncturable PRF but not a private one, we don't attempt to hide x, just f(x) *)
(* Written by Henry Barthelemy *)
type K.
type D.
type R.
type PK = {key : K; x : D option}.

op dK: { K distr | is_lossless dK } as dK_ll.
op F : K -> D -> R.

module PuncturablePsuedoRF = {

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
    k <@ PuncturablePsuedoRF.init();
    pk <@ PuncturablePsuedoRF.puncture(xp, k);
    x1 <@ PuncturablePsuedoRF.f(xi, k);
    x2 <@ PuncturablePsuedoRF.f(xi, pk);
    return x1 = x2;
  }
}.

lemma pprf_correctness &m xp1 xi1 : xp1 <> xi1 =>
    Pr [PuncturablePrfCorrectnessGame.f(xp1, xi1) @ &m : res = true] = 1%r.
proof.
move => xp_noteq_xi.
byphoare (_: xi <> xp ==> res = true) => // {&m}.
conseq (: _ ==> true) (: _ ==> res = true) => //.
proc; inline; wp; simplify.
rnd. skip. move => &hr xi_noteq_xp k _.
  have neq2 : (xi{hr} = xp{hr}) = false by smt().
  have simplified_if: (if xp{hr} = xi{hr} then None else Some (F k xi{hr})) = Some (F k xi{hr}) by smt().
  rewrite simplified_if; simplify; trivial.
  proc; inline; wp; simplify; rnd; skip. move => &hr H; simplify; smt(dK_ll).
  smt().
qed.





(* Some other proofs reasoning about punctured PRF *)

module Experiement3 = {
  proc f(x: D): R option = {
    var r;
    var pk;
    pk <@ PuncturablePsuedoRF.init();
    pk <@ PuncturablePsuedoRF.puncture(x, pk);
    r <@ PuncturablePsuedoRF.f(x, pk);
    return r;
  }
}. 

module Experiement4 = {
  proc f(x: D): R option = {
    var r;
    var pk;
    pk <@ PuncturablePsuedoRF.init();
    r <@ PuncturablePsuedoRF.f(x, pk);
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
