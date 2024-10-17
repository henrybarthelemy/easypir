(* Puncturable Psuedorandom Set *)
(* File created by Henry Barthelemy *)
require import AllCore Distr FSet List.
require (*--*) Puncturableprf.


(* Size of database *)
op S : int -> int. (* SN defined to be s(n) = sqrt(n) / 2 *)
op sqrt : int -> int.
axiom sqrt_def (x y : int) : (sqrt x = y) = (y * y = x).
op div: int -> int -> int.
axiom div_def (x y z : int) : (div x y = z) = (z * y = x).
axiom sq (x: int) : S(x) = div (sqrt x) 2.
 

type K.
type D = int.

clone import Puncturableprf as PPRF
   with type D <- D,
        type R <- D,
        type K <- K.

type SK = {n: int; k: PPRF.PK}.

module PPRFm = PPRF.PuncturablePsuedoRF.

op consIfSome (x: int option) (ls: int list) =
    with x = Some y => y :: ls
    with  x = None => ls.

lemma cons_with_none (ls : int list) : (consIfSome None ls = ls) by smt().
    
module PuncturablePRS = {
  proc gen(n : int): SK = {
    var k;
    var sk;
    (* The construction has some generation attemps... might skip and come back after *)
    k <@ PPRFm.init();
    sk <- {| n = n; k = k; |};
    return sk;
  }

  proc punc(sk: SK, i: int): SK = {
    var n <- sk.`n;
    var pk <- sk.`k;
    (* TODO *)
    return sk;
  }

  proc eval(sk: SK): int list = {
    var n <- sk.`n;
    var pk <- sk.`k;
    var i <- 1;
    var acc <- [];
    var cur_x_option: int option; 
    while (i < n) {
      cur_x_option <@ PPRFm.f(i, pk);
      if (cur_x_option <> None) {
        acc <- consIfSome cur_x_option acc;
      }
      i <- i + 1;
    }

    return acc;
  }


  
}.
