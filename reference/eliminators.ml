(* The eliminators of Void and Unit, assembled independently with the builder
   of looping.ml, as theories/MLTT/Eliminators.v. *)

open Looping
module P = Pts_native

let universe i = Sort (P.Univ i)

(* Void in the context A : Type0, v : Void. *)
let void_ctx = ["v", Const P.Void; "A", universe 0]
let void_family = ann (abs ["z"] (name "A")) (arrow (Const P.Void) (universe 0))
let void_elim = ElimVoid (void_family, name "v")

(* C u = elimUnit (λ_. Type0) Bool u, and elimUnit C true u. *)
let unit_universe = ann (abs ["w"] (universe 0)) (arrow (Const P.Unit) (universe 1))
let unit_family =
  ann (abs ["u"] (ElimUnit (unit_universe, Const P.Bool, name "u")))
    (arrow (Const P.Unit) (universe 0))
let unit_elim u = ElimUnit (unit_family, Const P.BTrue, u)
let unit_ctx = ["u", Const P.Unit]
