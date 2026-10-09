(* [choose] of the minimal MLTT, assembled independently with the builder of
   looping.ml, as theories/MLTT/Choose.v: in the context A B : Type0,

     choose : Πb:Bool. A → B → (if b then A else B)
     choose = λb x y. elimBool (λb'. if b' then A else B) x y b

   where [if b then A else B] is [elimBool (λ_. Type0) A B b]. *)

open Looping
module P = Pts_native

let universe i = Sort (P.Univ i)
let bool = Const P.Bool

let universe_family = ann (abs ["b"] (universe 0)) (arrow bool (universe 1))
let cond b = ElimBool (universe_family, name "A", name "B", b)
let choose_ty = pi "b" bool (arrows [name "A"; name "B"] (cond (name "b")))
let choose_family = ann (abs ["b"] (cond (name "b"))) (arrow bool (universe 0))

let choose =
  ann (abs ["b"; "x"; "y"] (ElimBool (choose_family, name "x", name "y", name "b"))) choose_ty

let choose_swapped =
  ann (abs ["b"; "x"; "y"] (ElimBool (choose_family, name "y", name "x", name "b"))) choose_ty

let low_family = ann (abs ["b"] (universe 0)) (arrow bool (universe 0))

let types_ctx = ["B", universe 0; "A", universe 0]
let args_ctx = ["c", name "B"; "a", name "A"] @ types_ctx
let open_ctx = ("b", bool) :: args_ctx

let in_ctx g =
  List.fold_right
    (fun (x, a) (names, out) -> (x :: names, build names a :: out)) g ([], [])
  |> snd

let term_in g t = build (List.map fst g) t
let choose_at b = call choose [b; name "a"; name "c"]
