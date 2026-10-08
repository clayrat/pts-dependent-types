(* Hurkens' looping combinator in pure System U-, independently assembled
   from the native PTS syntax.  The names below follow Geuvers--Verkoelen,
   section 4.  A small named-term builder keeps the construction readable;
   resolving a missing name raises an error instead of inventing a term. *)

module P = Pts_native

type named =
  | Sort of P.sort
  | Name of string
  | Product of string * named * named
  | Lambda of string * named
  | Apply of named * named
  | Annotate of named * named

let star = Sort P.Star
let box = Sort P.Box
let name x = Name x
let pi x a b = Product (x, a, b)
let arrow a b = pi "_" a b
let arrows domains codomain = List.fold_right arrow domains codomain
let abs names body = List.fold_right (fun x body -> Lambda (x, body)) names body
let call f args = List.fold_left (fun f arg -> Apply (f, arg)) f args
let ann body ty = Annotate (body, ty)

let rec index_of x = function
  | [] -> None
  | y :: rest ->
      if x = y then Some 0 else Option.map succ (index_of x rest)

let ( let* ) = Result.bind

let rec resolve names = function
  | Sort sort -> Ok (P.Srt sort)
  | Name x ->
      if x = "_" then Error x
      else (match index_of x names with
            | Some index -> Ok (P.Var index)
            | None -> Error x)
  | Product (x, domain, codomain) ->
      let* domain = resolve names domain in
      let* codomain = resolve (x :: names) codomain in
      Ok (P.Pi (domain, codomain))
  | Lambda (x, body) ->
      let* body = resolve (x :: names) body in
      Ok (P.Lam body)
  | Apply (fn, arg) ->
      let* fn = resolve names fn in
      let* arg = resolve names arg in
      Ok (P.App (fn, arg))
  | Annotate (body, ty) ->
      let* body = resolve names body in
      let* ty = resolve names ty in
      Ok (P.Ann (body, ty))

let build names t =
  match resolve names t with
  | Ok term -> term
  | Error x -> invalid_arg ("unbound name in looping combinator: " ^ x)

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
