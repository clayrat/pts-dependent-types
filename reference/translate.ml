(* A native translator from PCF to U-, independent of the extract.  It has
   its own PCF syntax and follows the bidirectional checker of
   strictness-pcf with two mutually recursive functions, like the Rocq
   [tr] with its single structural function: the same translation and the
   same first error.  The target terms are assembled with the builder and
   the encodings of looping.ml and encodings.ml. *)

open Looping
module E = Encodings

type ty = Nat | Arrow of ty * ty

type term =
  | Var of string
  | Lam of string * term
  | App of term * term
  | Num of int
  | Succ of term
  | Pred of term
  | Ifz of term * term * term
  | Fix of ty * term
  | Ann of term * ty

type ctx = (string * ty) list            (* innermost entry first *)

type pcf_error =
  | Unbound of string
  | NoSynth of term
  | NotFun of term * ty
  | LamNotFun of term * ty
  | Mismatch of term * ty * ty           (* term, expected, inferred *)

type error =
  | IllTyped of pcf_error
  | Name of string
  | TargetRejected of Pts_native.error     (* the U- checker rejects the output *)
  | TargetUndecided of Pts_native.term     (* it runs out of fuel *)

let rec tr_ty = function
  | Nat -> E.c_nat
  | Arrow (a, b) -> arrow (tr_ty a) (tr_ty b)

let ( let* ) = Result.bind

(* Synthesis: the translation and the PCF type. *)
let rec infer (g : ctx) t =
  match t with
  | Var x ->
      (match List.assoc_opt x g with
       | Some a -> Ok (name x, a)
       | None -> Error (Unbound x))
  | Num n -> Ok (E.numeral n, Nat)
  | Succ u -> let* u = check g u Nat in Ok (call E.c_succ [u], Nat)
  | Pred u -> let* u = check g u Nat in Ok (call E.c_pred [u], Nat)
  | App (f, u) ->
      let* f', ft = infer g f in
      (match ft with
       | Arrow (a, b) -> let* u = check g u a in Ok (call f' [u], b)
       | Nat -> Error (NotFun (f, Nat)))
  | Fix (a, u) -> let* u = check g u (Arrow (a, a)) in Ok (call l0 [tr_ty a; u], a)
  | Ann (u, a) -> let* u = check g u a in Ok (ann u (tr_ty a), a)
  | Lam _ | Ifz _ -> Error (NoSynth t)

(* Checking against [expected]. *)
and check g t expected =
  match t, expected with
  | Lam (x, body), Arrow (a, b) -> let* body = check ((x, a) :: g) body b in Ok (abs [x] body)
  | Lam _, Nat -> Error (LamNotFun (t, Nat))
  | Ifz (c, a, b), _ ->
      let* c = check g c Nat in
      let* a = check g a expected in
      let* b = check g b expected in
      Ok (E.ifz (tr_ty expected) c a b)
  | _ ->
      let* t', inferred = infer g t in
      if inferred = expected then Ok t' else Error (Mismatch (t, expected, inferred))

let resolve_ctx g =
  List.fold_right
    (fun (x, a) acc ->
      let* names, out = acc in
      let* a = resolve names (tr_ty a) in
      Ok (x :: names, a :: out))
    g (Ok ([], []))

let translate g t a =
  match check g t a with
  | Error e -> Error (IllTyped e)
  | Ok u ->
      (match resolve_ctx g with
       | Error x -> Error (Name x)
       | Ok (names, g') ->
           (match resolve names u with
            | Error x -> Error (Name x)
            | Ok u -> Ok (g', u)))

let translate_program t = Result.map snd (translate [] t Nat)

(* Every output checked: the native U- checker runs on the translation
   against the translated type, and only an accepted one is returned. *)
let translated_type a = build [] (tr_ty a)

let translate_checked fuel g t a =
  match translate g t a with
  | Error e -> Error e
  | Ok (g', u) ->
      (match snd (Pts_native.run_check Pts_native.system_u_minus fuel g' u (translated_type a)) with
       | Pts_native.Accepted () -> Ok (g', u)
       | Pts_native.Rejected e -> Error (TargetRejected e)
       | Pts_native.Undecided v -> Error (TargetUndecided v))

let translate_program_checked fuel t = Result.map snd (translate_checked fuel [] t Nat)
