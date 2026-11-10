(* Hurkens' looping combinator in pure System U-, independently assembled
   from the native PTS syntax.  The names below follow Geuvers--Verkoelen,
   section 4, and the terms are written with the builder of named.ml. *)

(* TODO(elim-inductive-types): remove this comment once elim-inductive-types
   builds against this reference.  Its reference/ takes the named-term
   builder from this module: [module L = Looping] in conversions.ml,
   diff.ml, diff_recursion.ml and recursion_native.ml, [open Looping] in
   data.ml and programs.ml, [Looping.named] in recursion_native.mli.  The
   builder is now in named.ml.  Its Makefile also copies from here
   [EXTERNAL := ... pts_native.ml looping.ml constants.ml families.ml ...]
   without named.ml, which looping.ml, constants.ml and families.ml open.
   Fix there: add named.ml to EXTERNAL before looping.ml, and take the
   builder from Named (or make this module [include Named]). *)
open Named
module P = Pts_native

(* V : Box and U : Box.  Only the three binders A in V, sb, and le
   range over Box; the other Lego "Type" occurrences are Star. *)
let kind_v =
  pi "A" box
    (arrows [arrow (arrow (name "A") star) (arrow (name "A") star);
             name "A"] star)

let kind_u = arrow kind_v star
let relation a = arrow (arrow a star) (arrow a star)

let sb =
  ann
    (abs ["A"; "r"; "a"; "z"]
       (call (name "r") [call (name "z") [name "A"; name "r"]; name "a"]))
    (pi "A" box (arrows [relation (name "A"); name "A"] kind_u))

let le =
  ann
    (abs ["i"; "x"]
       (call (name "x")
          [abs ["A"; "r"; "a"]
             (call (name "i") [call sb [name "A"; name "r"; name "a"]])]))
    (arrows [arrow kind_u star; kind_u] star)

let induct_body =
  pi "x" kind_u (arrow (call le [name "i"; name "x"])
                       (call (name "i") [name "x"]))

let induct = ann (abs ["i"] induct_body) (arrow (arrow kind_u star) star)
let wf = ann (abs ["z"] (call induct [call (name "z") [kind_u; le]])) kind_u
let g = call sb [kind_u; le]

let i_term =
  ann
    (abs ["x"]
       (arrow
          (pi "i" (arrow kind_u star)
             (arrow (call le [name "i"; name "x"])
                    (call (name "i") [call g [name "x"]])))
          (name "β")))
    (arrow kind_u star)

let shift_family i =
  abs ["y"] (call (name i) [call g [name "y"]])

let omega =
  ann
    (abs ["i"; "y"]
       (call (name "y")
          [wf; abs ["x"] (call (name "y") [call g [name "x"]])]))
    (pi "i" (arrow kind_u star)
       (arrow (call induct [name "i"]) (call (name "i") [wf])))

let lemma =
  abs ["x"; "p"; "q"]
    (call (name "f")
       [call (name "q")
          [i_term; name "p";
           abs ["i"] (call (name "q") [shift_family "i"])]])

let lemma2 =
  ann
    (abs ["x"]
       (call (name "x")
          [i_term; lemma;
           abs ["i"] (call (name "x") [shift_family "i"])]))
    (arrow
       (pi "i" (arrow kind_u star)
          (arrow (call induct [name "i"]) (call (name "i") [wf])))
       (name "β"))

let paradox = call lemma2 [omega]
let looping_type_named =
  pi "β" star (arrow (arrow (name "β") (name "β")) (name "β"))

let l0 = ann (abs ["β"; "f"] paradox) looping_type_named
let lemma_ann = ann lemma (call induct [i_term])

(* The recurrence from Lemma 3: WF_1 = WF, P_1 = lemma o G,
   Q_1 i = omega (i o G).  The annotations make later members
   synthesize their types in the bidirectional checker. *)
let rec wf_k k =
  if k <= 1 then wf else call g [wf_k (k - 1)]

let p_ty k = call le [i_term; wf_k k]
let q_ty k =
  pi "i" (arrow kind_u star)
    (arrow (call le [name "i"; wf_k k])
           (call (name "i") [call g [wf_k k]]))

let rec p_k k =
  if k <= 1 then abs ["x"] (call lemma_ann [call g [name "x"]])
  else abs ["x"] (call (ann (p_k (k - 1)) (p_ty (k - 1)))
                       [call g [name "x"]])

let rec q_k k =
  if k <= 1 then abs ["i"] (call omega [shift_family "i"])
  else abs ["i"] (call (ann (q_k (k - 1)) (q_ty (k - 1)))
                       [shift_family "i"])

let l_named n =
  if n = 0 then l0
  else
    let k = n + 1 in
    ann
      (abs ["β"; "f"] (call lemma_ann [wf_k k; p_k k; q_k k]))
      looping_type_named

let looping n =
  if n < 0 then invalid_arg "looping: negative index";
  build [] (l_named n)

let looping_ty = build [] looping_type_named

(* In the context beta : Star, f : beta -> beta, innermost first. *)
let looping_applied n =
  P.App (P.App (looping n, P.Var 1), P.Var 0)
