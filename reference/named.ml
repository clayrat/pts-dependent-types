(* The named-term builder of the examples, as theories/PTS/Named.v and
   theories/PTS/Build.v: terms written with names, resolved to de Bruijn
   indices of the native syntax.  Resolving a missing name raises an
   error instead of inventing a term. *)

module P = Pts_native

type named =
  | Sort of P.sort
  | Name of string
  | Product of string * named * named
  | Lambda of string * named
  | Apply of named * named
  | Annotate of named * named
  | Arrow of named * named        (* binds nothing *)
  | Const of P.term               (* a closed atom: a primitive, or a constant *)
  | ElimVoid of named * named
  | ElimUnit of named * named * named
  | ElimBool of named * named * named * named
  | Sum of string * named * named   (* Σx:A. B *)
  | Times of named * named          (* A × B, binds nothing *)
  | Pairing of named * named
  | First of named
  | Second of named
  | Match of string * P.sort * named * named * named list
      (* match x in D return P with b₁ | … end, into the sort *)
  | Fixpoint of string * named * int * named
      (* fix f : A {struct k} := b, binding f in b *)

let star = Sort P.Star
let box = Sort P.Box
let name x = Name x
let pi x a b = Product (x, a, b)
let arrow a b = Arrow (a, b)
let arrows domains codomain = List.fold_right arrow domains codomain
let abs names body = List.fold_right (fun x body -> Lambda (x, body)) names body
let call f args = List.fold_left (fun f arg -> Apply (f, arg)) f args
let ann body ty = Annotate (body, ty)

let rec index_of x = function
  | [] -> None
  | y :: rest ->
      if x = y then Some 0 else Option.map succ (index_of x rest)

let ( let* ) = Result.bind

(* Every element, or the first error, as [mapM] of Common/Result.v. *)
let rec map_result f = function
  | [] -> Ok []
  | x :: xs ->
      let* y = f x in
      let* ys = map_result f xs in
      Ok (y :: ys)

let rec resolve names = function
  | Sort sort -> Ok (P.Srt sort)
  | Name x ->
      (match index_of x names with
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
  | Const t -> Ok t
  | ElimVoid (c, e) ->
      let* c = resolve names c in
      let* e = resolve names e in
      Ok (P.ElimVoid (c, e))
  | ElimUnit (c, branch, u) ->
      let* c = resolve names c in
      let* branch = resolve names branch in
      let* u = resolve names u in
      Ok (P.ElimUnit (c, branch, u))
  | ElimBool (c, yes, no, b) ->
      let* c = resolve names c in
      let* yes = resolve names yes in
      let* no = resolve names no in
      let* b = resolve names b in
      Ok (P.ElimBool (c, yes, no, b))
  (* The codomain is resolved around the arrow and lifted past its binder. *)
  | Arrow (domain, codomain) ->
      let* domain = resolve names domain in
      let* codomain = resolve names codomain in
      Ok (P.Pi (domain, P.lift 1 codomain))
  | Sum (x, first, second) ->
      let* first = resolve names first in
      let* second = resolve (x :: names) second in
      Ok (P.Sigma (first, second))
  | Times (first, second) ->
      let* first = resolve names first in
      let* second = resolve names second in
      Ok (P.Sigma (first, P.lift 1 second))
  | Pairing (a, b) ->
      let* a = resolve names a in
      let* b = resolve names b in
      Ok (P.Pair (a, b))
  | First p -> let* p = resolve names p in Ok (P.Fst p)
  | Second p -> let* p = resolve names p in Ok (P.Snd p)
  | Match (d, s, motive, scrutinee, branches) ->
      let* motive = resolve names motive in
      let* scrutinee = resolve names scrutinee in
      let* branches = map_result (resolve names) branches in
      Ok (P.Case (d, s, motive, scrutinee, branches))
  | Fixpoint (f, ty, k, body) ->
      let* ty = resolve names ty in
      let* body = resolve (f :: names) body in
      Ok (P.Fix (ty, k, body))

let build names t =
  match resolve names t with
  | Ok term -> term
  | Error x -> invalid_arg ("unbound name: " ^ x)

let universe i = Sort (P.Univ i)
