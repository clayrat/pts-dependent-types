(* A readable OCaml counterpart of the executable Rocq PTS development.

   This file is independent of the generated code.  It uses the same raw
   syntax, normal-order strategy, fuel convention, checker rules, errors and
   trace events.  The native implementation is not covered by the Rocq
   proofs; reference/diff.ml compares it with the extracted implementation.

   As in the extracted OCaml, indices, universe levels and fuel are ints.
   Public callers should supply nonnegative values small enough to avoid
   machine-int overflow.

   Evaluation and checking take a signature of constants (inductive types,
   constructors, eliminator instances, δ-constants) as an optional [~sg];
   without it they run in the empty signature, as the developments of
   lecture 6 do. *)

type sort = Star | Box | Tri | Univ of int

(* A constant: an inductive type, its constructor, the eliminator instance
   for motives into Type_j, or a δ-constant. *)
type gref = Ind of string | Ctor of string * string | Elim of string * int | Def of string

type term =
  | Srt of sort | Var of int | Pi of term * term | Lam of term
  | App of term * term | Ann of term * term
  | Void | ElimVoid of term * term
  | Unit | Tt | ElimUnit of term * term * term
  | Bool | BTrue | BFalse | ElimBool of term * term * term * term
  | Sigma of term * term | Pair of term * term | Fst of term | Snd of term
  | Const of gref

type ctx = term list                         (* innermost entry first *)

(* [sigma] forms Σ, like [product] forms Π; [constants] lets terms mention
   the constants of a signature. *)
type spec = {
  sort_allowed : sort -> bool;
  axiom : sort -> sort option;
  product : sort -> sort -> sort option;
  primitive_sort : sort option;
  sigma : sort -> sort -> sort option;
  constants : bool;
}

let named_sort = function Star | Box | Tri -> true | Univ _ -> false
let u_axiom = function Star -> Some Box | Box -> Some Tri | _ -> None

let lambda_star = {
  sort_allowed = (function Star -> true | _ -> false);
  axiom = (function Star -> Some Star | _ -> None);
  product = (fun a b -> match a, b with Star, Star -> Some Star | _ -> None);
  primitive_sort = None;
  sigma = (fun _ _ -> None);
  constants = false;
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
  sigma = (fun _ _ -> None);
  constants = false;
}

let system_u = {
  system_u_minus with
  product = (fun a b ->
    match a, b with Tri, Star -> Some Star | _ -> u_minus_product a b);
}

let max_rule a b = match a, b with Univ i, Univ j -> Some (Univ (max i j)) | _ -> None

let pure_predicative = {
  sort_allowed = (function Univ _ -> true | _ -> false);
  axiom = (function Univ i -> Some (Univ (i + 1)) | _ -> None);
  product = max_rule;
  primitive_sort = None;
  sigma = (fun _ _ -> None);
  constants = false;
}

(* Σ follows the rule of Π, and constants are on, only with the primitives. *)
let predicative =
  { pure_predicative with primitive_sort = Some (Univ 0); sigma = max_rule; constants = true }

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
  | Sigma (a, b) -> Sigma (lift_from amount cutoff a, lift_from amount (cutoff + 1) b)
  | Pair (a, b) -> Pair (lift_from amount cutoff a, lift_from amount cutoff b)
  | Fst p -> Fst (lift_from amount cutoff p)
  | Snd p -> Snd (lift_from amount cutoff p)
  | (Srt _ | Void | Unit | Tt | Bool | BTrue | BFalse | Const _) as t -> t

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
    | Sigma (a, b) -> Sigma (go depth a, go (depth + 1) b)
    | Pair (a, b) -> Pair (go depth a, go depth b)
    | Fst p -> Fst (go depth p)
    | Snd p -> Snd (go depth p)
    | (Srt _ | Void | Unit | Tt | Bool | BTrue | BFalse | Const _) as t -> t
  in
  go 0 body

(* Parallel substitution: index n becomes [sb n]; under a binder index 0
   stays and the others are shifted past it. *)
let rec subst sb = function
  | Var n -> sb n
  | Pi (a, b) -> Pi (subst sb a, subst (under sb) b)
  | Lam b -> Lam (subst (under sb) b)
  | App (f, a) -> App (subst sb f, subst sb a)
  | Ann (t, a) -> Ann (subst sb t, subst sb a)
  | ElimVoid (c, e) -> ElimVoid (subst sb c, subst sb e)
  | ElimUnit (c, branch, u) -> ElimUnit (subst sb c, subst sb branch, subst sb u)
  | ElimBool (c, yes, no, b) -> ElimBool (subst sb c, subst sb yes, subst sb no, subst sb b)
  | Sigma (a, b) -> Sigma (subst sb a, subst (under sb) b)
  | Pair (a, b) -> Pair (subst sb a, subst sb b)
  | Fst p -> Fst (subst sb p)
  | Snd p -> Snd (subst sb p)
  | (Srt _ | Void | Unit | Tt | Bool | BTrue | BFalse | Const _) as t -> t

and under sb n = if n = 0 then Var 0 else lift 1 (sb (n - 1))

let rec closed_above k = function
  | Var n -> n < k
  | Pi (a, b) | Sigma (a, b) -> closed_above k a && closed_above (k + 1) b
  | Lam b -> closed_above (k + 1) b
  | App (f, a) | Ann (f, a) | ElimVoid (f, a) | Pair (f, a) -> closed_above k f && closed_above k a
  | ElimUnit (c, branch, u) -> closed_above k c && closed_above k branch && closed_above k u
  | ElimBool (c, yes, no, b) ->
      closed_above k c && closed_above k yes && closed_above k no && closed_above k b
  | Fst p | Snd p -> closed_above k p
  | Srt _ | Void | Unit | Tt | Bool | BTrue | BFalse | Const _ -> true

(* Spines and telescopes.  [vars base n] are the variables of a telescope
   of n entries lying [base] binders up, outermost first. *)
let apps head args = List.fold_left (fun f a -> App (f, a)) head args

let spine t =
  let rec go t args = match t with App (f, a) -> go f (a :: args) | head -> (head, args) in
  go t []

let pis tys body = List.fold_right (fun ty body -> Pi (ty, body)) tys body
let rec lams n body = if n = 0 then body else Lam (lams (n - 1) body)
let vars base n = List.init n (fun i -> Var (base + n - 1 - i))

let rec take n = function x :: xs when n > 0 -> x :: take (n - 1) xs | _ -> []
let rec drop n = function _ :: xs when n > 0 -> drop (n - 1) xs | l -> l

(* Signatures, as PTS/Signature.v: classified descriptions after Dybjer's
   schema, eliminator instances with the flag of active ι-rules, and
   δ-constants, newest first.  Built from [empty_signature] by [sig_add],
   a signature keeps every term closed in its telescope: types and bodies,
   and the parts of a description.  [sig_add] checks only the new entry,
   as the older ones were checked when they were added. *)
type field = FArg of term | FRec of term list * term list

type ctor_desc = { ctor_name : string; ctor_fields : field list; ctor_indices : term list }

type ind_desc = {
  ind_name : string;
  ind_params : term list;
  ind_indices : term list;
  ind_level : int;
  ind_ctors : ctor_desc list;
}

type entry =
  | EInd of ind_desc
  | EElim of string * int * term * bool      (* D, j, the type, active ι-rules *)
  | EDef of string * term * term             (* f, the type, the body *)

type signature = entry list

let empty_signature = []

let telescope_closed k tys = List.for_all Fun.id (List.mapi (fun i ty -> closed_above (k + i) ty) tys)

(* [k]: the parameters and the previous fields. *)
let field_closed k = function
  | FArg a -> closed_above k a
  | FRec (domains, indices) ->
      telescope_closed k domains
      && List.for_all (closed_above (k + List.length domains)) indices

let ctor_closed p c =
  List.for_all Fun.id (List.mapi (fun l fd -> field_closed (p + l) fd) c.ctor_fields)
  && List.for_all (closed_above (p + List.length c.ctor_fields)) c.ctor_indices

let entry_closed = function
  | EInd d ->
      let p = List.length d.ind_params in
      telescope_closed 0 d.ind_params && telescope_closed p d.ind_indices
      && List.for_all (ctor_closed p) d.ind_ctors
  | EElim (_, _, ty, _) -> closed_above 0 ty
  | EDef (_, ty, body) -> closed_above 0 ty && closed_above 0 body

let sig_add sg entry = if entry_closed entry then Some (entry :: sg) else None

let find_ind sg name =
  List.find_map (function EInd d when d.ind_name = name -> Some d | _ -> None) sg

let find_elim sg name level =
  List.find_map (function
    | EElim (d, j, ty, active) when d = name && j = level -> Some (ty, active)
    | _ -> None) sg

let find_def sg name =
  List.find_map (function EDef (f, ty, body) when f = name -> Some (ty, body) | _ -> None) sg

let find_ctor ctors name =
  let rec go i = function
    | [] -> None
    | c :: rest -> if c.ctor_name = name then Some (i, c) else go (i + 1) rest
  in
  go 0 ctors

(* The types of a declaration: [D : Π(Δ). Πθ̄. Type_i] and
   [c : Π(Δ). Π(fields). D Δ ū]; a recursive field at position l applies D
   to the parameters, which lie past its domains and the l earlier fields. *)
let field_type d p l = function
  | FArg a -> a
  | FRec (domains, indices) ->
      pis domains (apps (Const (Ind d)) (vars (List.length domains + l) p @ indices))

let ind_type d = pis (d.ind_params @ d.ind_indices) (Srt (Univ d.ind_level))

let ctor_type d c =
  let p = List.length d.ind_params in
  pis (d.ind_params @ List.mapi (field_type d.ind_name p) c.ctor_fields)
    (apps (Const (Ind d.ind_name)) (vars (List.length c.ctor_fields) p @ c.ctor_indices))

(* Parameters, motive, one method per constructor, indices, object. *)
let elim_arity d =
  List.length d.ind_params + 1 + List.length d.ind_ctors + List.length d.ind_indices + 1

let sig_type sg = function
  | Ind name -> Option.map ind_type (find_ind sg name)
  | Ctor (name, c) ->
      Option.bind (find_ind sg name) (fun d ->
        Option.map (fun (_, cd) -> ctor_type d cd) (find_ctor d.ind_ctors c))
  | Elim (name, j) -> Option.map fst (find_elim sg name j)
  | Def f -> Option.map fst (find_def sg f)

let delta sg = function Def f -> Option.map snd (find_def sg f) | _ -> None

(* An instance with active rules applied to its full arity. *)
let elim_view sg t =
  match spine t with
  | Const (Elim (name, j)), args ->
      (match find_elim sg name j, find_ind sg name with
       | Some (_, true), Some d when List.length args = elim_arity d -> Some (name, j, d, args)
       | _ -> None)
  | _ -> None

let full_elim sg t = Option.is_some (elim_view sg t)

(* ι by the scheme of the description.  On [elim_D[j] Δ P m̄ ū (c_k Δ' ā)]
   the method [m_k] gets each field and, right after a recursive field
   [a : Πȳ:B̄. D Δ v̄], its hypothesis [λȳ. elim_D[j] Δ P m̄ v̄ (a ȳ)]:
   [pre] are the parameters, motive and methods, and the indices v̄ are
   instantiated with [env], the earlier fields and the parameters,
   innermost first. *)
let hypothesis name j pre env domains indices a =
  let m = List.length domains in
  let inst n = if n < m then Var n else lift m (Option.value (List.nth_opt env (n - m)) ~default:(Var 0)) in
  lams m (apps (Const (Elim (name, j)))
    (List.map (lift m) pre @ List.map (subst inst) indices @ [apps (lift m a) (vars 0 m)]))

let rec method_args name j pre env fields xs =
  match fields, xs with
  | FArg _ :: fields, a :: xs -> a :: method_args name j pre (a :: env) fields xs
  | FRec (domains, indices) :: fields, a :: xs ->
      a :: hypothesis name j pre env domains indices a :: method_args name j pre (a :: env) fields xs
  | _ -> []

let iota sg t =
  match elim_view sg t with
  | None -> None
  | Some (name, j, d, args) ->
      let p = List.length d.ind_params and k = List.length d.ind_ctors in
      (match spine (List.nth args (List.length args - 1)) with
       | Const (Ctor (name', c)), xargs when name' = name ->
           (match find_ctor d.ind_ctors c with
            | Some (i, cd) when List.length xargs = p + List.length cd.ctor_fields ->
                Option.map (fun m ->
                  apps m (method_args name j (take (p + 1 + k) args) (List.rev (take p args))
                            cd.ctor_fields (drop p xargs)))
                  (List.nth_opt (take k (drop (p + 1) args)) i)
            | _ -> None)
       | _ -> None)

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
   annotation, ι on a constructor or a pair, and δ and ι of the signature. *)
let contract sg t =
  match t with
  | App (Lam b, a) -> Some (subst1 b a)
  | App _ -> iota sg t
  | Ann (t, _) -> Some t
  | ElimUnit (_, branch, Tt) -> Some branch
  | ElimBool (_, yes, _, BTrue) -> Some yes
  | ElimBool (_, _, no, BFalse) -> Some no
  | Fst (Pair (a, _)) -> Some a
  | Snd (Pair (_, b)) -> Some b
  | Const g -> delta sg g
  | _ -> None

(* One leftmost-outermost step, or the reason no step is possible.  The
   continuations avoid inspecting later components until they are needed.
   A full spine of an eliminator instance is scanned object first. *)
let rec classify ?(sg = empty_signature) t =
  let classify = classify ~sg in
  match contract sg t with
  | Some u -> Step u
  | None ->
      match t with
      | Var _ | Const _ -> Neutral
      | Srt _ | Void | Unit | Tt | Bool | BTrue | BFalse -> Normal
      | Pi (a, b) ->
          normal_part (classify a) (fun a' -> Pi (a', b)) (fun () ->
          normal_part (classify b) (fun b' -> Pi (a, b')) (fun () -> Normal))
      | Sigma (a, b) ->
          normal_part (classify a) (fun a' -> Sigma (a', b)) (fun () ->
          normal_part (classify b) (fun b' -> Sigma (a, b')) (fun () -> Normal))
      | Lam b -> normal_part (classify b) (fun b' -> Lam b') (fun () -> Normal)
      | App (f, a) when full_elim sg t ->
          head_part (classify a) (fun a' -> App (f, a')) (fun () ->
          head_part (classify f) (fun f' -> App (f', a)) (fun () -> Neutral))
      | App (f, a) ->
          head_part (classify f) (fun f' -> App (f', a)) (fun () ->
          normal_part (classify a) (fun a' -> App (f, a')) (fun () -> Neutral))
      | Pair (a, b) ->
          normal_part (classify a) (fun a' -> Pair (a', b)) (fun () ->
          normal_part (classify b) (fun b' -> Pair (a, b')) (fun () -> Normal))
      | Fst p -> head_part (classify p) (fun p' -> Fst p') (fun () -> Neutral)
      | Snd p -> head_part (classify p) (fun p' -> Snd p') (fun () -> Neutral)
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

let rec head_step sg t =
  let head_step = head_step sg in
  match contract sg t with
  | Some _ as step -> step
  | None ->
      match t with
      | App (f, a) when full_elim sg t -> Option.map (fun a' -> App (f, a')) (head_step a)
      | App (f, a) -> Option.map (fun f' -> App (f', a)) (head_step f)
      | Fst p -> Option.map (fun p' -> Fst p') (head_step p)
      | Snd p -> Option.map (fun p' -> Snd p') (head_step p)
      | ElimVoid (c, e) -> Option.map (fun e' -> ElimVoid (c, e')) (head_step e)
      | ElimUnit (c, branch, u) ->
          Option.map (fun u' -> ElimUnit (c, branch, u')) (head_step u)
      | ElimBool (c, yes, no, b) ->
          Option.map (fun b' -> ElimBool (c, yes, no, b')) (head_step b)
      | _ -> None

type eval_result = NormalForm of term | StuckTerm of term | OutOfFuel of term
type head_result = HeadForm of term | HeadOutOfFuel of term
type conv_result = ConvEqual of term | ConvDifferent | ConvOutOfFuel | ConvStuck

let rec normalize_trace ?(sg = empty_signature) fuel t =
  match classify ~sg t with
  | Step _ when fuel <= 0 -> [t], OutOfFuel t
  | Step u ->
      let trace, result = normalize_trace ~sg (fuel - 1) u in
      t :: trace, result
  | Neutral | Normal -> [t], NormalForm t
  | Stuck -> [t], StuckTerm t

(* The checker needs only the answer, so it does not build a trace. *)
let rec normalize ?(sg = empty_signature) fuel t =
  match classify ~sg t with
  | Step _ when fuel <= 0 -> OutOfFuel t
  | Step u -> normalize ~sg (fuel - 1) u
  | Neutral | Normal -> NormalForm t
  | Stuck -> StuckTerm t

let rec whnf ?(sg = empty_signature) fuel t =
  match head_step sg t with
  | None -> HeadForm t
  | Some _ when fuel <= 0 -> HeadOutOfFuel t
  | Some u -> whnf ~sg (fuel - 1) u

let convert ?(sg = empty_signature) fuel t u =
  if t = u then ConvEqual t
  else
    match normalize ~sg fuel t, normalize ~sg fuel u with
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
  | ENoSigmaRule of term * sort * sort | ENotASigma of term * term
  | ENoDecls of term | EUnknownConst of gref

type event =
  | EvCtxEntry of int * term | EvExpected of term | EvTerm of term
  | EvAxiom of sort * sort | EvRule of sort * sort * sort
  | EvUnfoldSort of term * term * sort
  | EvUnfoldPi of term * term * term * term
  | EvArg of term * term | EvSubst of term * term * term
  | EvConv of term * term * term | EvFamily of term * term * sort
  | EvSigmaRule of sort * sort * sort
  | EvUnfoldSigma of term * term * term * term

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

(* The checker for one specification, signature and fuel budget, like
   [Section Check] in Check.v: [spec], [sg], [fuel] and the event [log] are
   fixed for the run. *)
let make_checker spec sg fuel log =
  let whnf = whnf ~sg and convert = convert ~sg in
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
  let sigma_rule term first second =
    match spec.sigma first second with
    | Some result ->
        let* () = emit (EvSigmaRule (first, second, result)) in return result
    | None -> reject (ENoSigmaRule (term, first, second))
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
  let as_sigma term ty =
    match whnf fuel ty with
    | HeadForm (Sigma (first, second)) ->
        let* () = emit (EvUnfoldSigma (term, ty, first, second)) in
        return (first, second)
    | HeadForm other -> reject (ENotASigma (term, other))
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
     a lambda or a pair. *)
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
    | Sigma (first, second) ->
        let* first_sort = infer_sort gamma first in
        let* second_sort = infer_sort (first :: gamma) second in
        let* result = sigma_rule term first_sort second_sort in
        return (Srt result)
    | Pair _ -> reject (ECannotInfer term)
    | Fst pair ->
        let* pair_ty = infer gamma pair in
        let* first, _ = as_sigma pair pair_ty in
        return first
    | Snd pair ->
        let* pair_ty = infer gamma pair in
        let* _, second = as_sigma pair pair_ty in
        let result_ty = subst1 second (Fst pair) in
        let* () = emit (EvSubst (second, Fst pair, result_ty)) in
        return result_ty
    | Const g ->
        if not spec.constants then reject (ENoDecls term)
        else (match sig_type sg g with
              | Some ty -> return ty
              | None -> reject (EUnknownConst g))

  and check gamma term expected =
    match term with
    | Lam body ->
        let* domain, codomain = as_pi term expected in
        check (domain :: gamma) body codomain
    | Pair (a, b) ->
        let* first, second = as_sigma term expected in
        let* () = check gamma a first in
        let second_ty = subst1 second a in
        let* () = emit (EvSubst (second, a, second_ty)) in
        check gamma b second_ty
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

let run spec sg fuel task =
  let log = Queue.create () in
  let answer = match task (make_checker spec sg fuel log) with
    | Ok value -> Accepted value
    | Error (Reject error) -> Rejected error
    | Error (NoFuel term) -> Undecided term
  in
  List.of_seq (Queue.to_seq log), answer

let run_infer ?(sg = empty_signature) spec fuel gamma term =
  run spec sg fuel (fun checker -> checker.infer_in gamma term)

let run_check ?(sg = empty_signature) spec fuel gamma term expected =
  run spec sg fuel (fun checker -> checker.check_in gamma term expected)

(* A small direct demo, so [ocaml reference/pts_native.ml] works like the
   standalone reference file in strictness-pcf.  Rich named printing stays
   in extraction/pretty.ml; here the indices remain visible. *)
let show_sort = function
  | Star -> "∗" | Box -> "□" | Tri -> "△"
  | Univ i -> "Type_" ^ string_of_int i

let show_gref = function
  | Ind d -> d | Ctor (_, c) -> c | Def f -> f
  | Elim (d, j) -> "elim" ^ d ^ "[" ^ string_of_int j ^ "]"

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
  | Sigma (a, b) -> "(Σ:" ^ show_term a ^ ". " ^ show_term b ^ ")"
  | Pair (a, b) -> "⟨" ^ show_term a ^ ", " ^ show_term b ^ "⟩"
  | Fst p -> "fst(" ^ show_term p ^ ")"
  | Snd p -> "snd(" ^ show_term p ^ ")"
  | Const g -> show_gref g

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
  | ENoSigmaRule (_, a, b) -> "no Σ-rule for (" ^ show_sort a ^ ", " ^ show_sort b ^ ")"
  | ENotASigma (t, ty) -> show_term t ^ " has non-Σ type " ^ show_term ty
  | ENoDecls t -> "constants off: " ^ show_term t
  | EUnknownConst g -> "unknown constant " ^ show_gref g

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
    (show_answer (fun () -> "") result);
  let _, result = run_check predicative 100 [] (Pair (BTrue, Tt)) (Sigma (Bool, Unit)) in
  Printf.printf "  %-25s %s\n" "⟨true, tt⟩ : Bool × Unit"
    (show_answer (fun () -> "") result)

let () =
  if Filename.basename Sys.argv.(0) = "pts_native.ml" then run_examples ()
