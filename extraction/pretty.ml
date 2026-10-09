(* Printing for the extracted PTS development.

   Terms are printed with names in place of de Bruijn indices.  A binder
   whose domain is a sort is named A, B, …, any other x, y, …; a λ under
   an annotation takes its name from the annotated Π.  A Π whose body does
   not use its variable is printed as an arrow.  A variable outside the
   given names is printed as #k, its de Bruijn index in the unnamed outer
   context: trace events carry open terms without their context.

   [depth] bounds the printed nesting; deeper compound subterms become "…", which
   keeps traces of large terms readable.  The printers are total: a
   dangling index or a malformed term never raises. *)
open Deptypes

let subscript n =
  let digits = [| "₀"; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉" |] in
  String.concat ""
    (List.map
       (fun c -> digits.(Char.code c - Char.code '0'))
       (List.of_seq (String.to_seq (string_of_int n))))

let pp_sort = function
  | Star -> "∗"
  | Box -> "□"
  | Tri -> "△"
  | Univ i -> "Type" ^ subscript i

let fresh candidates scope =
  let rec go suffix =
    match List.find_opt (fun c -> not (List.mem (c ^ suffix) scope)) candidates with
    | Some c -> c ^ suffix
    | None -> go (suffix ^ "'")
  in
  go ""

let type_names = [ "A"; "B"; "C"; "X"; "Y"; "Z" ]
let term_names = [ "x"; "y"; "z"; "u"; "v"; "w" ]

let binder_name domain scope =
  match domain with
  | Some (Srt _) -> fresh type_names scope
  | _ -> fresh term_names scope

let lookup_name names n =
  match List.nth_opt names n with
  | Some s -> s
  | None -> "#" ^ string_of_int (n - List.length names)

let atomic = function
  | Srt _ | Var _ | Void | Unit | Tt | Bool | BTrue | BFalse -> true
  | _ -> false

(* Levels: 0 binder, arrow or annotation; 1 application; 2 atom.  [hint]
   is the type a λ is checked against, when an annotation gives it.  An
   atom is always printed; a compound term at depth 1 becomes "…". *)
let rec pp_at depth hint names level t =
  let paren wanted s = if level > wanted then "(" ^ s ^ ")" else s in
  if depth <= 1 && not (atomic t) then "…"
  else
    let pp = pp_at (depth - 1) None in
    let spine head args = paren 1 (String.concat " " (head :: List.map (pp names 2) args)) in
    match t with
    | Srt s -> pp_sort s
    | Var n -> lookup_name names n
    | Pi (a, b) when not (free_in 0 b) ->
        paren 0 (pp names 1 a ^ " → " ^ pp ("_" :: names) 0 b)
    | Pi (a, b) ->
        let x = binder_name (Some a) names in
        paren 0 ("Π" ^ x ^ ":" ^ pp names 0 a ^ ". " ^ pp (x :: names) 0 b)
    | Lam b ->
        let domain, body_hint =
          match hint with Some (Pi (a, bt)) -> (Some a, Some bt) | _ -> (None, None)
        in
        let x = binder_name domain names in
        paren 0 ("λ" ^ x ^ ". " ^ pp_at (depth - 1) body_hint (x :: names) 0 b)
    | App (f, a) -> paren 1 (pp names 1 f ^ " " ^ pp names 2 a)
    | Ann (u, a) -> "(" ^ pp_at (depth - 1) (Some a) names 1 u ^ " : " ^ pp names 0 a ^ ")"
    | Void -> "Void"
    | Unit -> "Unit"
    | Tt -> "tt"
    | Bool -> "Bool"
    | BTrue -> "true"
    | BFalse -> "false"
    | ElimVoid (c, e) -> spine "elimVoid" [ c; e ]
    | ElimUnit (c, x, u) -> spine "elimUnit" [ c; x; u ]
    | ElimBool (c, x, y, b) -> spine "elimBool" [ c; x; y; b ]

let pp_term ?(depth = max_int) ?(names = []) t = pp_at depth None names 0 t

(* Names for a context, innermost entry first as in [ctx]. *)
let ctx_names (g : ctx) =
  List.fold_right (fun a names -> binder_name (Some a) names :: names) g []

let pp_ctx (g : ctx) =
  let names = ctx_names g in
  let rec entries g names =
    match (g, names) with
    | a :: g', x :: names' -> entries g' names' @ [ x ^ " : " ^ pp_term ~names:names' a ]
    | _ -> []
  in
  match entries g names with [] -> "·" | es -> String.concat ", " es

let pp_error ?(depth = max_int) ?(names = []) e =
  let pp = pp_term ~depth ~names in
  match e with
  | EUnboundVar n -> "unbound variable #" ^ string_of_int n
  | ENotInSystem s -> pp_sort s ^ " is not a sort of this system"
  | ETopSort s -> "the sort " ^ pp_sort s ^ " has no type"
  | ENoRule (t, s1, s2) ->
      "no rule (" ^ pp_sort s1 ^ ", " ^ pp_sort s2 ^ ", _) for " ^ pp t
  | ENotASort (t, ty) -> pp t ^ " has type " ^ pp ty ^ ", not a sort"
  | ENotAPi (t, ty) -> pp t ^ " has type " ^ pp ty ^ ", not a Π-type"
  | EMismatch (t, expected, inferred) ->
      pp t ^ " has type " ^ pp inferred ^ ", expected " ^ pp expected
  | EStuckType (t, expected, inferred) ->
      "cannot compare the type " ^ pp inferred ^ " of " ^ pp t ^ " with " ^ pp expected
      ^ ": evaluation is stuck"
  | ECannotInfer t -> "cannot infer the type of " ^ pp t ^ "; annotate it"
  | ENoPrimitives t -> pp t ^ ": the primitives are off in this system"
  | EBadFamily (c, expected, actual) ->
      "result family " ^ pp c ^ " is over " ^ pp actual ^ ", expected over " ^ pp expected

let rec drop n l = if n <= 0 then l else match l with [] -> [] | _ :: l' -> drop (n - 1) l'

(* [ctx] is the input context of the run: the phase markers are open in
   it (an entry at level k in its k outermost entries), so they are
   printed with its names; the other events are printed with #k. *)
let pp_event ?(depth = max_int) ?(ctx = []) ?names ev =
  let pp = pp_term ~depth in
  let names = match names with Some names -> names | None -> ctx_names ctx in
  match ev with
  | EvCtxEntry (k, a) ->
      let outer = drop (List.length names - k) names in
      let x = match List.nth_opt names (List.length names - 1 - k) with Some x -> x | None -> "?" in
      "context entry " ^ x ^ " : " ^ pp_term ~depth ~names:outer a
  | EvExpected a -> "expected type: " ^ pp_term ~depth ~names a
  | EvTerm t -> "term: " ^ pp_term ~depth ~names t
  | EvAxiom (s, s') -> "  axiom " ^ pp_sort s ^ " : " ^ pp_sort s'
  | EvRule (s1, s2, s3) ->
      "  rule (" ^ pp_sort s1 ^ ", " ^ pp_sort s2 ^ ", " ^ pp_sort s3 ^ ")"
  | EvUnfoldSort (t, ty, s) -> "  " ^ pp t ^ " : " ^ pp ty ^ " ⇝ " ^ pp_sort s
  | EvUnfoldPi (t, ty, a, b) ->
      let pi = Pi (a, b) in
      if term_eqb ty pi then "  " ^ pp t ^ " : " ^ pp ty
      else "  " ^ pp t ^ " : " ^ pp ty ^ " ⇝ " ^ pp pi
  | EvArg (u, a) -> "  argument " ^ pp u ^ " : " ^ pp a
  | EvSubst (b, u, b') ->
      "  codomain [" ^ pp u ^ "/x] " ^ pp_term ~depth ~names:[ "x" ] b ^ " = " ^ pp b'
  | EvConv (a, t, v) ->
      if term_eqb a t then "  " ^ pp a ^ " ≡ " ^ pp t
      else "  " ^ pp a ^ " ≡ " ^ pp t ^ ", both ⇝ " ^ pp v
  | EvFamily (c, d, s) -> "  family " ^ pp c ^ " over " ^ pp d ^ " into " ^ pp_sort s

let pp_answer ?(depth = max_int) ?(names = []) pp_value = function
  | Accepted a -> (match pp_value a with "" -> "accepted" | s -> "accepted: " ^ s)
  | Rejected e -> "rejected: " ^ pp_error ~depth ~names e
  | Undecided t -> "undecided: out of fuel while typing " ^ pp_term ~depth ~names t

let pp_observation ?(depth = max_int) = function
  | ObsNumeral k -> string_of_int k
  | ObsOtherNormal t -> "normal form " ^ pp_term ~depth t ^ ", not a numeral"
  | ObsStuck t -> "stuck at " ^ pp_term ~depth t
  | ObsOutOfFuel _ -> "no normal form within the fuel"

let pp_eval_result ?(depth = max_int) ?(names = []) = function
  | NormalForm t -> "normal form " ^ pp_term ~depth ~names t
  | StuckTerm t -> "stuck at " ^ pp_term ~depth ~names t
  | OutOfFuel t -> "out of fuel at " ^ pp_term ~depth ~names t
