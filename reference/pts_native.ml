(* A readable OCaml counterpart of the executable Rocq PTS development.

   This file is independent of the generated code.  It uses the same raw
   syntax, normal-order strategy, fuel convention, checker rules, errors and
   trace events.  The native implementation is not covered by the Rocq
   proofs; reference/diff.ml compares it with the extracted implementation.

   As in the extracted OCaml, indices, universe levels and fuel are ints.
   Public callers should supply nonnegative values small enough to avoid
   machine-int overflow. *)

type sort = Star | Box | Tri | Univ of int

type term =
  | Srt of sort | Var of int | Pi of term * term | Lam of term
  | App of term * term | Ann of term * term
  | Void | ElimVoid of term * term
  | Unit | Tt | ElimUnit of term * term * term
  | Bool | BTrue | BFalse | ElimBool of term * term * term * term

type ctx = term list                         (* innermost entry first *)

type spec = {
  sort_allowed : sort -> bool;
  axiom : sort -> sort option;
  product : sort -> sort -> sort option;
  primitive_sort : sort option;
}

let named_sort = function Star | Box | Tri -> true | Univ _ -> false
let u_axiom = function Star -> Some Box | Box -> Some Tri | _ -> None

let lambda_star = {
  sort_allowed = (function Star -> true | _ -> false);
  axiom = (function Star -> Some Star | _ -> None);
  product = (fun a b -> match a, b with Star, Star -> Some Star | _ -> None);
  primitive_sort = None;
}

let u_minus_product a b =
  match a, b with
  | (Star | Box), Star -> Some Star
  | (Box | Tri), Box -> Some Box
  | _ -> None

let system_u_minus = {
  sort_allowed = named_sort;
  axiom = u_axiom;
  product = u_minus_product;
  primitive_sort = None;
}

let system_u = {
  system_u_minus with
  product = (fun a b ->
    match a, b with Tri, Star -> Some Star | _ -> u_minus_product a b);
}

let pure_predicative = {
  sort_allowed = (function Univ _ -> true | _ -> false);
  axiom = (function Univ i -> Some (Univ (i + 1)) | _ -> None);
  product = (fun a b ->
    match a, b with Univ i, Univ j -> Some (Univ (max i j)) | _ -> None);
  primitive_sort = None;
}

let predicative = { pure_predicative with primitive_sort = Some (Univ 0) }

(* Shifting and substitution use a cutoff.  [subst1 body argument] replaces
   index zero and shifts the open argument under every binder it crosses. *)
let rec lift_from amount cutoff = function
  | Var n -> Var (if n < cutoff then n else n + amount)
  | Pi (a, b) -> Pi (lift_from amount cutoff a, lift_from amount (cutoff + 1) b)
  | Lam b -> Lam (lift_from amount (cutoff + 1) b)
  | App (f, a) -> App (lift_from amount cutoff f, lift_from amount cutoff a)
  | Ann (t, a) -> Ann (lift_from amount cutoff t, lift_from amount cutoff a)
  | ElimVoid (c, e) -> ElimVoid (lift_from amount cutoff c, lift_from amount cutoff e)
  | ElimUnit (c, branch, u) ->
      ElimUnit (lift_from amount cutoff c, lift_from amount cutoff branch,
                lift_from amount cutoff u)
  | ElimBool (c, yes, no, b) ->
      ElimBool (lift_from amount cutoff c, lift_from amount cutoff yes,
                lift_from amount cutoff no, lift_from amount cutoff b)
  | (Srt _ | Void | Unit | Tt | Bool | BTrue | BFalse) as t -> t

let lift amount t = lift_from amount 0 t

let subst1 body argument =
  let rec go depth = function
    | Var n when n = depth -> lift depth argument
    | Var n -> Var (if n > depth then n - 1 else n)
    | Pi (a, b) -> Pi (go depth a, go (depth + 1) b)
    | Lam b -> Lam (go (depth + 1) b)
    | App (f, a) -> App (go depth f, go depth a)
    | Ann (t, a) -> Ann (go depth t, go depth a)
    | ElimVoid (c, e) -> ElimVoid (go depth c, go depth e)
    | ElimUnit (c, branch, u) -> ElimUnit (go depth c, go depth branch, go depth u)
    | ElimBool (c, yes, no, b) ->
        ElimBool (go depth c, go depth yes, go depth no, go depth b)
    | (Srt _ | Void | Unit | Tt | Bool | BTrue | BFalse) as t -> t
  in
  go 0 body

let lookup (gamma : ctx) index =
  match List.nth_opt gamma index with
  | None -> None
  | Some a -> Some (lift (index + 1) a)

type shape = Step of term | Neutral | Normal | Stuck

let normal_part shape rebuild continue =
  match shape with
  | Step u -> Step (rebuild u)
  | Neutral | Normal -> continue ()
  | Stuck -> Stuck

let head_part shape rebuild continue =
  match shape with
  | Step u -> Step (rebuild u)
  | Neutral -> continue ()
  | Normal | Stuck -> Stuck

(* The redexes at the root, shared by both evaluators: β, erasure of an
   annotation, ι on a constructor. *)
let contract = function
  | App (Lam b, a) -> Some (subst1 b a)
  | Ann (t, _) -> Some t
  | ElimUnit (_, branch, Tt) -> Some branch
  | ElimBool (_, yes, _, BTrue) -> Some yes
  | ElimBool (_, _, no, BFalse) -> Some no
  | _ -> None

(* One leftmost-outermost step, or the reason no step is possible.  The
   continuations avoid inspecting later components until they are needed. *)
let rec classify t =
  match contract t with
  | Some u -> Step u
  | None ->
      match t with
      | Var _ -> Neutral
      | Srt _ | Void | Unit | Tt | Bool | BTrue | BFalse -> Normal
      | Pi (a, b) ->
          normal_part (classify a) (fun a' -> Pi (a', b)) (fun () ->
          normal_part (classify b) (fun b' -> Pi (a, b')) (fun () -> Normal))
      | Lam b -> normal_part (classify b) (fun b' -> Lam b') (fun () -> Normal)
      | App (f, a) ->
          head_part (classify f) (fun f' -> App (f', a)) (fun () ->
          normal_part (classify a) (fun a' -> App (f, a')) (fun () -> Neutral))
      | Ann _ -> Stuck                     (* unreachable: [contract] erases it *)
      | ElimVoid (c, e) ->
          head_part (classify e) (fun e' -> ElimVoid (c, e')) (fun () ->
          normal_part (classify c) (fun c' -> ElimVoid (c', e)) (fun () -> Neutral))
      | ElimUnit (c, branch, u) ->
          head_part (classify u) (fun u' -> ElimUnit (c, branch, u')) (fun () ->
          normal_part (classify c) (fun c' -> ElimUnit (c', branch, u)) (fun () ->
          normal_part (classify branch) (fun b' -> ElimUnit (c, b', u))
            (fun () -> Neutral)))
      | ElimBool (c, yes, no, b) ->
          head_part (classify b) (fun b' -> ElimBool (c, yes, no, b')) (fun () ->
          normal_part (classify c) (fun c' -> ElimBool (c', yes, no, b)) (fun () ->
          normal_part (classify yes) (fun y' -> ElimBool (c, y', no, b)) (fun () ->
          normal_part (classify no) (fun n' -> ElimBool (c, yes, n', b))
            (fun () -> Neutral))))

let rec head_step t =
  match contract t with
  | Some _ as step -> step
  | None ->
      match t with
      | App (f, a) -> Option.map (fun f' -> App (f', a)) (head_step f)
      | ElimVoid (c, e) -> Option.map (fun e' -> ElimVoid (c, e')) (head_step e)
      | ElimUnit (c, branch, u) ->
          Option.map (fun u' -> ElimUnit (c, branch, u')) (head_step u)
      | ElimBool (c, yes, no, b) ->
          Option.map (fun b' -> ElimBool (c, yes, no, b')) (head_step b)
      | _ -> None

type eval_result = NormalForm of term | StuckTerm of term | OutOfFuel of term
type head_result = HeadForm of term | HeadOutOfFuel of term
type conv_result = ConvEqual of term | ConvDifferent | ConvOutOfFuel | ConvStuck

let rec normalize_trace fuel t =
  match classify t with
  | Step _ when fuel <= 0 -> [t], OutOfFuel t
  | Step u ->
      let trace, result = normalize_trace (fuel - 1) u in
      t :: trace, result
  | Neutral | Normal -> [t], NormalForm t
  | Stuck -> [t], StuckTerm t

(* The checker needs only the answer, so it does not build a trace. *)
let rec normalize fuel t =
  match classify t with
  | Step _ when fuel <= 0 -> OutOfFuel t
  | Step u -> normalize (fuel - 1) u
  | Neutral | Normal -> NormalForm t
  | Stuck -> StuckTerm t

let rec whnf fuel t =
  match head_step t with
  | None -> HeadForm t
  | Some _ when fuel <= 0 -> HeadOutOfFuel t
  | Some u -> whnf (fuel - 1) u

let convert fuel t u =
  if t = u then ConvEqual t
  else
    match normalize fuel t, normalize fuel u with
    | NormalForm t', NormalForm u' ->
        if t' = u' then ConvEqual t' else ConvDifferent
    | StuckTerm _, _ | _, StuckTerm _ -> ConvStuck
    | _ -> ConvOutOfFuel

type error =
  | EUnboundVar of int | ENotInSystem of sort | ETopSort of sort
  | ENoRule of term * sort * sort | ENotASort of term * term
  | ENotAPi of term * term | EMismatch of term * term * term
  | EStuckType of term * term * term | ECannotInfer of term
  | ENoPrimitives of term | EBadFamily of term * term * term

type event =
  | EvCtxEntry of int * term | EvExpected of term | EvTerm of term
  | EvAxiom of sort * sort | EvRule of sort * sort * sort
  | EvUnfoldSort of term * term * sort
  | EvUnfoldPi of term * term * term * term
  | EvArg of term * term | EvSubst of term * term * term
  | EvConv of term * term * term | EvFamily of term * term * sort

type failure = Reject of error | NoFuel of term
type 'a answer = Accepted of 'a | Rejected of error | Undecided of term

(* A step of the checker succeeds or stops the run.  Events go to a queue
   owned by the run, so the ones emitted before a failure are kept. *)
type 'a checked = ('a, failure) result

let return = Result.ok
let ( let* ) = Result.bind
let reject error = Error (Reject error)
let no_fuel term = Error (NoFuel term)

type checker = {
  infer_in : ctx -> term -> term checked;
  check_in : ctx -> term -> term -> unit checked;
}

(* The checker for one specification and fuel budget, like [Section Check]
   in Check.v: [spec], [fuel] and the event [log] are fixed for the run. *)
let make_checker spec fuel log =
  let emit event = Queue.add event log; Ok () in

  let axiom sort =
    match spec.axiom sort with
    | Some result -> let* () = emit (EvAxiom (sort, result)) in return result
    | None -> reject (if spec.sort_allowed sort then ETopSort sort else ENotInSystem sort)
  in
  let rule term domain codomain =
    match spec.product domain codomain with
    | Some result ->
        let* () = emit (EvRule (domain, codomain, result)) in return result
    | None -> reject (ENoRule (term, domain, codomain))
  in
  let primitive term =
    match spec.primitive_sort with
    | Some sort -> return sort
    | None -> reject (ENoPrimitives term)
  in
  let as_sort term ty =
    match whnf fuel ty with
    | HeadForm (Srt sort) ->
        if ty = Srt sort then return sort
        else let* () = emit (EvUnfoldSort (term, ty, sort)) in return sort
    | HeadForm other -> reject (ENotASort (term, other))
    | HeadOutOfFuel _ -> no_fuel term
  in
  let as_pi term ty =
    match whnf fuel ty with
    | HeadForm (Pi (domain, codomain)) ->
        let* () = emit (EvUnfoldPi (term, ty, domain, codomain)) in
        return (domain, codomain)
    | HeadForm other -> reject (ENotAPi (term, other))
    | HeadOutOfFuel _ -> no_fuel term
  in
  let check_conv term inferred expected =
    match convert fuel inferred expected with
    | ConvEqual common -> emit (EvConv (inferred, expected, common))
    | ConvDifferent -> reject (EMismatch (term, expected, inferred))
    | ConvStuck -> reject (EStuckType (term, expected, inferred))
    | ConvOutOfFuel -> no_fuel term
  in
  let family result_family family_type expected_domain =
    let* domain, codomain = as_pi result_family family_type in
    match convert fuel domain expected_domain with
    | ConvEqual _ ->
        let* sort = as_sort result_family codomain in
        emit (EvFamily (result_family, expected_domain, sort))
    | ConvOutOfFuel -> no_fuel result_family
    | ConvDifferent | ConvStuck ->
        reject (EBadFamily (result_family, expected_domain, domain))
  in

  (* Two explicit modes make the checker easier to read than the
     structurally recursive Rocq [tc].  Synthesis never guesses a type for
     a lambda. *)
  let rec infer gamma term =
    match term with
    | Srt sort ->
        let* result = axiom sort in return (Srt result)
    | Var index ->
        (match lookup gamma index with
         | Some ty -> return ty | None -> reject (EUnboundVar index))
    | Pi (domain, codomain) ->
        let* domain_sort = infer_sort gamma domain in
        let* codomain_sort = infer_sort (domain :: gamma) codomain in
        let* result = rule term domain_sort codomain_sort in
        return (Srt result)
    | Lam _ -> reject (ECannotInfer term)
    | App (fn, argument) ->
        let* function_ty = infer gamma fn in
        let* domain, codomain = as_pi fn function_ty in
        let* () = check gamma argument domain in
        let* () = emit (EvArg (argument, domain)) in
        let result_ty = subst1 codomain argument in
        let* () = emit (EvSubst (codomain, argument, result_ty)) in
        return result_ty
    | Ann (body, ty) ->
        let* _ = infer_sort gamma ty in
        let* () = check gamma body ty in
        return ty
    | Void | Unit | Bool ->
        let* sort = primitive term in return (Srt sort)
    | Tt -> let* _ = primitive term in return Unit
    | BTrue | BFalse -> let* _ = primitive term in return Bool
    | ElimVoid (result_family, scrutinee) ->
        let* () = elim_family gamma term result_family Void in
        let* () = check gamma scrutinee Void in
        return (App (result_family, scrutinee))
    | ElimUnit (result_family, branch, scrutinee) ->
        let* () = elim_family gamma term result_family Unit in
        let* () = check gamma branch (App (result_family, Tt)) in
        let* () = check gamma scrutinee Unit in
        return (App (result_family, scrutinee))
    | ElimBool (result_family, yes, no, scrutinee) ->
        let* () = elim_family gamma term result_family Bool in
        let* () = check gamma yes (App (result_family, BTrue)) in
        let* () = check gamma no (App (result_family, BFalse)) in
        let* () = check gamma scrutinee Bool in
        return (App (result_family, scrutinee))

  and check gamma term expected =
    match term with
    | Lam body ->
        let* domain, codomain = as_pi term expected in
        check (domain :: gamma) body codomain
    | _ ->
        let* inferred = infer gamma term in
        check_conv term inferred expected

  (* [ty] synthesizes a sort. *)
  and infer_sort gamma ty =
    let* kind = infer gamma ty in
    as_sort ty kind

  (* The start of an eliminator over [domain]: primitives are on, and the
     result family is a family over [domain]. *)
  and elim_family gamma term result_family domain =
    let* _ = primitive term in
    let* family_ty = infer gamma result_family in
    family result_family family_ty domain
  in

  let rec check_ctx = function
    | [] -> return ()
    | ty :: outer ->
        let* () = check_ctx outer in
        let* () = emit (EvCtxEntry (List.length outer, ty)) in
        let* _ = infer_sort outer ty in
        return ()
  in
  let check_type gamma = function
    | Srt sort when spec.sort_allowed sort -> return ()
    | Srt sort -> reject (ENotInSystem sort)
    | ty ->
        let* _ = infer_sort gamma ty in
        return ()
  in
  let infer_in gamma term =
    let* () = check_ctx gamma in
    let* () = emit (EvTerm term) in
    infer gamma term
  in
  let check_in gamma term expected =
    let* () = check_ctx gamma in
    let* () = emit (EvExpected expected) in
    let* () = check_type gamma expected in
    let* () = emit (EvTerm term) in
    check gamma term expected
  in
  { infer_in; check_in }

let run spec fuel task =
  let log = Queue.create () in
  let answer = match task (make_checker spec fuel log) with
    | Ok value -> Accepted value
    | Error (Reject error) -> Rejected error
    | Error (NoFuel term) -> Undecided term
  in
  List.of_seq (Queue.to_seq log), answer

let run_infer spec fuel gamma term =
  run spec fuel (fun checker -> checker.infer_in gamma term)

let run_check spec fuel gamma term expected =
  run spec fuel (fun checker -> checker.check_in gamma term expected)

(* A small direct demo, so [ocaml reference/pts_native.ml] works like the
   standalone reference file in strictness-pcf.  Rich named printing stays
   in extraction/pretty.ml; here the indices remain visible. *)
let show_sort = function
  | Star -> "∗" | Box -> "□" | Tri -> "△"
  | Univ i -> "Type_" ^ string_of_int i

let rec show_term = function
  | Srt s -> show_sort s | Var n -> "#" ^ string_of_int n
  | Pi (a, b) -> "(Π:" ^ show_term a ^ ". " ^ show_term b ^ ")"
  | Lam b -> "(λ. " ^ show_term b ^ ")"
  | App (f, a) -> "(" ^ show_term f ^ " " ^ show_term a ^ ")"
  | Ann (t, a) -> "(" ^ show_term t ^ " : " ^ show_term a ^ ")"
  | Void -> "Void" | Unit -> "Unit" | Tt -> "tt"
  | Bool -> "Bool" | BTrue -> "true" | BFalse -> "false"
  | ElimVoid (c, e) -> "elimVoid(" ^ show_term c ^ ", " ^ show_term e ^ ")"
  | ElimUnit (c, branch, u) ->
      "elimUnit(" ^ show_term c ^ ", " ^ show_term branch ^ ", " ^ show_term u ^ ")"
  | ElimBool (c, yes, no, b) ->
      "elimBool(" ^ show_term c ^ ", " ^ show_term yes ^ ", " ^
      show_term no ^ ", " ^ show_term b ^ ")"

let show_error = function
  | EUnboundVar n -> "unbound #" ^ string_of_int n
  | ENotInSystem s -> "foreign sort " ^ show_sort s
  | ETopSort s -> "top sort " ^ show_sort s
  | ENoRule (_, a, b) -> "no Π-rule for (" ^ show_sort a ^ ", " ^ show_sort b ^ ")"
  | ENotASort (t, ty) -> show_term t ^ " has non-sort type " ^ show_term ty
  | ENotAPi (t, ty) -> show_term t ^ " has non-Π type " ^ show_term ty
  | EMismatch (_, expected, actual) ->
      "expected " ^ show_term expected ^ ", inferred " ^ show_term actual
  | EStuckType (_, expected, actual) ->
      "stuck comparing " ^ show_term actual ^ " with " ^ show_term expected
  | ECannotInfer t -> "annotate " ^ show_term t
  | ENoPrimitives t -> "primitives off: " ^ show_term t
  | EBadFamily (_, expected, actual) ->
      "family domain " ^ show_term actual ^ ", expected " ^ show_term expected

let show_answer show_value = function
  | Accepted value ->
      let printed = show_value value in
      if printed = "" then "accepted" else "accepted: " ^ printed
  | Rejected error -> "rejected: " ^ show_error error
  | Undecided term -> "out of fuel while typing " ^ show_term term

let run_examples () =
  let id_ty = Pi (Srt Star, Pi (Var 0, Var 1)) in
  let id_tm = Ann (Lam (Lam (Var 0)), id_ty) in
  let forbidden = Pi (Var 0, Srt Star) in
  let show_infer label spec gamma term =
    let _, answer = run_infer spec 100 gamma term in
    Printf.printf "  %-25s %s\n" label (show_answer show_term answer)
  in
  print_endline "Native PTS reference:";
  show_infer "U⁻ identity" system_u_minus [] id_tm;
  show_infer "U⁻ forbidden (∗, □)" system_u_minus [Srt Star] forbidden;
  show_infer "U⁻ primitive Bool" system_u_minus [] Bool;
  let _, result = run_check predicative 100 [] BTrue Bool in
  Printf.printf "  %-25s %s\n" "predicative true : Bool"
    (show_answer (fun () -> "") result)

let () =
  if Filename.basename Sys.argv.(0) = "pts_native.ml" then run_examples ()
