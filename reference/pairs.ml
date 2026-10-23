(* Dependent pairs, assembled independently with the builder of looping.ml,
   as theories/MLTT/Pairs.v: IsTrue b = elimBool (λ_. Type0) Unit Void b,
   and the pairs and projections around Σb:Bool. IsTrue b. *)

open Looping
module P = Pts_native

let universe i = Sort (P.Univ i)
let bool = Const P.Bool

let is_true =
  ann (abs ["b"] (ElimBool (ann (abs ["z"] (universe 0)) (arrow bool (universe 1)),
                            Const P.Unit, Const P.Void, name "b")))
    (arrow bool (universe 0))

let true_sigma = Sum ("b", bool, Apply (is_true, name "b"))
let sigma_ctx = [build [] true_sigma]

let true_pair = Pairing (Const P.BTrue, Const P.Tt)
let false_pair = Pairing (Const P.BFalse, Const P.Tt)
let bools = Times (bool, bool)
let bool_pair = Pairing (Const P.BTrue, Const P.BFalse)
let first_of_pair = First (ann bool_pair bools)
let sigma_of_universe = Sum ("b", bool, universe 0)
