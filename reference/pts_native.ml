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

type sort = Star | Box | Tri | Univ of int | Prp   (* Prp is Prop *)

(* A constant: an inductive type, its constructor, the eliminator instance
   for motives into the sort s, Type_j or Prop, or a δ-constant. *)
type gref = Ind of string | Ctor of string * string | Elim of string * sort | Def of string

type term =
  | Srt of sort | Var of int | Pi of term * term | Lam of term
  | App of term * term | Ann of term * term
  | Void | ElimVoid of term * term
  | Unit | Tt | ElimUnit of term * term * term
  | Bool | BTrue | BFalse | ElimBool of term * term * term * term
  | Sigma of term * term | Pair of term * term | Fst of term | Snd of term
  | Const of gref
  | Case of string * sort * term * term * term list
      (* match x in D return P with b₁ | … end, into the sort; the branches
         in the order of the constructors *)
  | Fix of term * int * term
      (* fix f : A {struct k} := b, with f index 0 in b *)

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

let named_sort = function Star | Box | Tri -> true | Univ _ | Prp -> false
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

(* λC: all four rules over ∗ and □, the product in the sort of its codomain. *)
let coc = {
  sort_allowed = (function Star | Box -> true | _ -> false);
  axiom = (function Star -> Some Box | _ -> None);
  product = (fun a b -> match a, b with (Star | Box), (Star | Box) -> Some b | _ -> None);
  primitive_sort = None;
  sigma = (fun _ _ -> None);
  constants = false;
}

(* Prop beside the hierarchy, Prop : Type₁.  Π into Prop is in Prop; Σ has
   its own rules and always lives in Type. *)
let predicative_prop = {
  sort_allowed = (function Univ _ | Prp -> true | _ -> false);
  axiom = (function Prp -> Some (Univ 1) | Univ i -> Some (Univ (i + 1)) | _ -> None);
  product = (fun a b ->
    match a, b with
    | (Univ _ | Prp), Prp -> Some Prp
    | Prp, Univ j -> Some (Univ j)
    | _ -> max_rule a b);
  primitive_sort = Some (Univ 0);
  sigma = (fun a b ->
    match a, b with
    | Univ i, Prp -> Some (Univ i)
    | Prp, Univ j -> Some (Univ j)
    | Prp, Prp -> Some (Univ 0)
    | _ -> max_rule a b);
  constants = true;
}

(* Binding in [result], for the guard and the checker. *)
let ( let* ) = Result.bind

(* The one traversal of de Bruijn terms behind shifting and substitution:
   [map_vars f depth t] replaces each variable [Var n] of [t], met under
   [depth] binders (counting from the root at [depth]), by [f depth n], and
   rebuilds every other former. *)
let rec map_vars f depth = function
  | Var n -> f depth n
  | Pi (a, b) -> Pi (map_vars f depth a, map_vars f (depth + 1) b)
  | Lam b -> Lam (map_vars f (depth + 1) b)
  | App (g, a) -> App (map_vars f depth g, map_vars f depth a)
  | Ann (t, a) -> Ann (map_vars f depth t, map_vars f depth a)
  | ElimVoid (c, e) -> ElimVoid (map_vars f depth c, map_vars f depth e)
  | ElimUnit (c, branch, u) -> ElimUnit (map_vars f depth c, map_vars f depth branch, map_vars f depth u)
  | ElimBool (c, yes, no, b) ->
      ElimBool (map_vars f depth c, map_vars f depth yes, map_vars f depth no, map_vars f depth b)
  | Sigma (a, b) -> Sigma (map_vars f depth a, map_vars f (depth + 1) b)
  | Pair (a, b) -> Pair (map_vars f depth a, map_vars f depth b)
  | Fst p -> Fst (map_vars f depth p)
  | Snd p -> Snd (map_vars f depth p)
  | Case (d, s, m, x, bs) -> Case (d, s, map_vars f depth m, map_vars f depth x, List.map (map_vars f depth) bs)
  | Fix (a, k, b) -> Fix (map_vars f depth a, k, map_vars f (depth + 1) b)
  | (Srt _ | Void | Unit | Tt | Bool | BTrue | BFalse | Const _) as t -> t

(* [lift_from amount cutoff t] shifts the indices of [t] from [cutoff] up
   by [amount].  A zero shift returns [t] itself, so that substitution at
   depth zero shares the substituted term rather than copying it. *)
let lift_from amount cutoff t =
  if amount = 0 then t else map_vars (fun depth n -> Var (if n < depth then n else n + amount)) cutoff t

let lift amount t = lift_from amount 0 t

(* [subst1 body argument] replaces index zero by [argument], shifted past
   the binders it is put under, and decrements the other free indices. *)
let subst1 body argument =
  map_vars (fun depth n ->
      if n = depth then lift depth argument else Var (if n > depth then n - 1 else n))
    0 body

(* Parallel substitution: index n becomes [sb n].  Under [depth] binders the
   bound indices stay and [sb] is shifted past them, by one [lift depth]
   rather than one shift per binder. *)
let subst sb t =
  map_vars (fun depth n -> if n < depth then Var n else lift depth (sb (n - depth))) 0 t

let rec closed_above k = function
  | Var n -> n < k
  | Pi (a, b) | Sigma (a, b) | Fix (a, _, b) -> closed_above k a && closed_above (k + 1) b
  | Lam b -> closed_above (k + 1) b
  | Case (_, _, m, x, bs) ->
      closed_above k m && closed_above k x && List.for_all (closed_above k) bs
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

(* The body of a fix starts with at least [n] λ. *)
let rec has_lams n b = n = 0 || (match b with Lam b' -> has_lams (n - 1) b' | _ -> false)

(* Signatures, as PTS/Signature.v: classified descriptions after Dybjer's
   schema, eliminator instances with the flag of active ι-rules, and
   δ-constants, newest first.  Built from [empty_signature] by [sig_add],
   a signature keeps every term closed in its telescope: types and bodies,
   and the parts of a description.  [sig_add] checks only the new entry,
   as the older ones were checked when they were added. *)
type field = FArg of term | FRec of term list * term list

type ctor_desc = { ctor_name : string; ctor_fields : field list; ctor_indices : term list }

(* The sorts of the motives of D: every sort of the table, or Prop. *)
type elim_class = PropOnly | AllSorts

type ind_desc = {
  ind_name : string;
  ind_params : term list;
  ind_indices : term list;
  ind_sort : sort;                           (* Type_i or Prop *)
  ind_elim : elim_class;
  ind_ctors : ctor_desc list;
}

type entry =
  | EInd of ind_desc
  | EElim of string * sort * term * bool     (* D, s, the type, active ι-rules *)
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

(* A motive into [s]: a sort of the table that the category of D admits. *)
let allows_elimination spec cls s =
  spec.sort_allowed s && (match cls with AllSorts -> true | PropOnly -> s = Prp)

let find_ind sg name =
  List.find_map (function EInd d when d.ind_name = name -> Some d | _ -> None) sg

let find_elim sg name sort =
  List.find_map (function
    | EElim (d, s, ty, active) when d = name && s = sort -> Some (ty, active)
    | _ -> None) sg

let find_def sg name =
  List.find_map (function EDef (f, ty, body) when f = name -> Some (ty, body) | _ -> None) sg

let find_ctor ctors name =
  let rec go i = function
    | [] -> None
    | c :: rest -> if c.ctor_name = name then Some (i, c) else go (i + 1) rest
  in
  go 0 ctors

(* The types of a declaration: [D : Π(Δ). Πθ̄. s] and
   [c : Π(Δ). Π(fields). D Δ ū]; a recursive field at position l applies D
   to the parameters, which lie past its domains and the l earlier fields. *)
let field_type d p l = function
  | FArg a -> a
  | FRec (domains, indices) ->
      pis domains (apps (Const (Ind d)) (vars (List.length domains + l) p @ indices))

let ind_type d = pis (d.ind_params @ d.ind_indices) (Srt d.ind_sort)

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
  | Elim (name, s) -> Option.map fst (find_elim sg name s)
  | Def f -> Option.map fst (find_def sg f)

let delta sg = function Def f -> Option.map snd (find_def sg f) | _ -> None

(* An instance with active rules applied to its full arity. *)
let elim_view sg t =
  match spine t with
  | Const (Elim (name, s)), args ->
      (match find_elim sg name s, find_ind sg name with
       | Some (_, true), Some d when List.compare_length_with args (elim_arity d) = 0 -> Some (name, s, d, args)
       | _ -> None)
  | _ -> None

let full_elim sg t = Option.is_some (elim_view sg t)

(* ι by the scheme of the description.  On [elim_D[s] Δ P m̄ ū (c_k Δ' ā)]
   the method [m_k] gets each field and, right after a recursive field
   [a : Πȳ:B̄. D Δ v̄], its hypothesis [λȳ. elim_D[s] Δ P m̄ v̄ (a ȳ)]:
   [pre] are the parameters, motive and methods, and the indices v̄ are
   instantiated with [env], the earlier fields and the parameters,
   innermost first. *)
(* [inst m env]: the binders of [env], innermost first, under [m] new ones. *)
let inst m env n = if n < m then Var n else lift m (Option.value (List.nth_opt env (n - m)) ~default:(Var 0))

let hypothesis name s pre env domains indices a =
  let m = List.length domains in
  lams m (apps (Const (Elim (name, s)))
    (List.map (lift m) pre @ List.map (subst (inst m env)) indices @ [apps (lift m a) (vars 0 m)]))

let rec method_args name s pre env fields xs =
  match fields, xs with
  | FArg _ :: fields, a :: xs -> a :: method_args name s pre (a :: env) fields xs
  | FRec (domains, indices) :: fields, a :: xs ->
      a :: hypothesis name s pre env domains indices a :: method_args name s pre (a :: env) fields xs
  | _ -> []

(* [x] is a constructor of [name], described by [d], applied to the
   parameters and to all its fields: its position, its description and the
   fields, as [ctor_view] of Signature.v. *)
let ctor_view name d x =
  match spine x with
  | Const (Ctor (name', c)), xargs when name' = name ->
      (match find_ctor d.ind_ctors c with
       | Some (i, cd) ->
           let p = List.length d.ind_params in
           if List.compare_length_with xargs (p + List.length cd.ctor_fields) = 0 then Some (i, cd, drop p xargs)
           else None
       | None -> None)
  | _ -> None

let iota sg t =
  match elim_view sg t with
  | None -> None
  | Some (name, s, d, args) ->
      let p = List.length d.ind_params and k = List.length d.ind_ctors in
      (match ctor_view name d (List.nth args (List.length args - 1)) with
       | Some (i, cd, fields) ->
           Option.map (fun m ->
             apps m (method_args name s (take (p + 1 + k) args) (List.rev (take p args)) cd.ctor_fields fields))
             (List.nth_opt (take k (drop (p + 1) args)) i)
       | None -> None)

(* match: [Case D s P (c_i Δ' ā) bs ⇝ b_i ā], the parameters skipped. *)
let case_iota sg = function
  | Case (name, _, _, x, bs) ->
      Option.bind (find_ind sg name) (fun d ->
        Option.bind (ctor_view name d x) (fun (i, _, fields) ->
          Option.map (fun b -> apps b fields) (List.nth_opt bs i)))
  | _ -> None

(* The parameters [ps], outermost first, in a term of a description under
   the parameters and [m] more binders.  [env] is [List.rev ps], reversed
   once for a whole telescope. *)
let inst_env env m t = subst (inst m env) t
let inst_params ps m t = inst_env (List.rev ps) m t
let inst_tele env tys = List.mapi (inst_env env) tys

(* [Πθ̄:Θ̄[ps]. D ps θ̄ → s] *)
let case_motive_type d ps s =
  let q = List.length d.ind_indices in
  pis (inst_tele (List.rev ps) d.ind_indices)
    (Pi (apps (Const (Ind d.ind_name)) (List.map (lift q) ps @ vars 0 q), Srt s))

(* [Πȳ:fields[ps]. P ū[ps, ȳ] (c ps ȳ)] *)
let case_branch_type d ps motive c =
  let env = List.rev ps and n = List.length c.ctor_fields in
  pis (inst_tele env (List.mapi (field_type d.ind_name (List.length d.ind_params)) c.ctor_fields))
    (apps (lift n motive)
       (List.map (inst_env env n) c.ctor_indices
        @ [apps (Const (Ctor (d.ind_name, c.ctor_name))) (List.map (lift n) ps @ vars 0 n)]))

(* fix applied up to its structural argument, and its unfolding when that
   argument is a constructor spine. *)
let fix_view t =
  match spine t with
  | Fix (a, k, b), args when List.compare_length_with args (k + 1) = 0 -> Some (a, k, b, args)
  | _ -> None

let fix_unfold t =
  match fix_view t with
  | Some (a, k, b, args) ->
      (match spine (List.nth args k) with
       | Const (Ctor _), _ -> Some (apps (subst1 b (Fix (a, k, b))) args)
       | _ -> None)
  | None -> None

(* Spines contracted at their last argument. *)
(* The number of arguments at which a head computes, as [head_arity] of
   Signature.v: an instance with active rules, a fix up to its structural
   argument.  A spine short of it is a value; an instance without active
   rules never computes and, applied, is stuck. *)
let head_arity sg = function
  | Const (Elim (name, s)) ->
      (match find_elim sg name s, find_ind sg name with
       | Some (_, true), Some d -> Some (elim_arity d)
       | _ -> None)
  | Fix (_, k, _) -> Some (k + 1)
  | _ -> None

(* A spine contracted at its last argument: its head reaches its arity. *)
let full_spine sg t = match spine t with h, args -> head_arity sg h = Some (List.length args)
let spine_iota sg t = match iota sg t with Some u -> Some u | None -> fix_unfold t

(* The guard of fix, as Guard.v: a mark for each variable of the body,
   innermost first; recursive calls must be on a variable marked [Sub m]
   applied to exactly [m] arguments.  A match on the structural argument
   or on a recognized subterm marks the fields its branches bind. *)
type mark = Large | Arg | Sub of int | Self
type guard_error = GPartialCall of term | GNotSubterm of term * term | GShortBody of term

let mark_at ms i = Option.value (List.nth_opt ms i) ~default:Large
let entry_marks k = (Arg :: List.init k (fun _ -> Large)) @ [Self]
let field_mark = function FArg _ -> Large | FRec (domains, _) -> Sub (List.length domains)

let sub_arg ms a =
  match spine a with
  | Var i, args -> (match mark_at ms i with Sub m -> List.compare_length_with args m = 0 | _ -> false)
  | _ -> false

let origin ms x = (match x with Var i -> mark_at ms i = Arg | _ -> false) || sub_arg ms x
let self_headed ms t = match spine t with Var i, _ -> mark_at ms i = Self | _ -> false

let branch_fields sg ms name x =
  if origin ms x then
    match find_ind sg name with
    | Some d -> List.map (fun c -> c.ctor_fields) d.ind_ctors
    | None -> []
  else []

let call_ok k ms t =
  if self_headed ms t then
    let _, args = spine t in
    if k < List.length args then
      let a = List.nth args k in
      if sub_arg ms a then Ok () else Error (GNotSubterm (t, a))
    else Error (GPartialCall t)
  else Ok ()

(* [spine]: [t] is the function part of a maximal spine checked already. *)
let rec guard sg k ms t spine_part =
  let sub ms u = guard sg k ms u false in
  match t with
  | Var i ->
      if spine_part then Ok () else if mark_at ms i = Self then Error (GPartialCall t) else Ok ()
  | App (f, a) ->
      let* () = if spine_part then Ok () else call_ok k ms t in
      let* () = guard sg k ms f true in
      sub ms a
  | Lam b -> sub (Large :: ms) b
  | Pi (a, b) | Sigma (a, b) | Fix (a, _, b) -> let* () = sub ms a in sub (Large :: ms) b
  | Ann (u, a) | ElimVoid (u, a) | Pair (u, a) -> let* () = sub ms u in sub ms a
  | ElimUnit (c, branch, u) -> let* () = sub ms c in let* () = sub ms branch in sub ms u
  | ElimBool (c, yes, no, b) ->
      let* () = sub ms c in let* () = sub ms yes in let* () = sub ms no in sub ms b
  | Fst p | Snd p -> sub ms p
  | Case (name, _, m, x, bs) ->
      let* () = sub ms m in
      let* () = sub ms x in
      let rec peel ms fields b =
        match fields, b with
        | fd :: fields, Lam b' -> peel (field_mark fd :: ms) fields b'
        | _ -> sub ms b
      in
      let rec each fss = function
        | [] -> Ok ()
        | b :: bs ->
            let fields, rest = match fss with fs :: rest -> (fs, rest) | [] -> ([], []) in
            let* () = peel ms fields b in
            each rest bs
      in
      each (branch_fields sg ms name x) bs
  | Srt _ | Void | Unit | Tt | Bool | BTrue | BFalse | Const _ -> Ok ()

(* The body after its k + 1 leading λ; a body without them is refused. *)
let guard_fix sg k b =
  let rec entry n ms b =
    match b with
    | Lam b' when n = 0 -> guard sg k (Arg :: ms) b' false
    | Lam b' -> entry (n - 1) (Large :: ms) b'
    | _ -> Error (GShortBody b)
  in
  entry k [Self] b

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
  | App _ -> spine_iota sg t
  | Case _ -> case_iota sg t
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
      | App (f, a) when full_spine sg t ->
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
      | Case (d, s, m, x, bs) ->
          let rec branches pre = function
            | [] -> Neutral
            | b :: rest ->
                normal_part (classify b) (fun b' -> Case (d, s, m, x, List.rev_append pre (b' :: rest)))
                  (fun () -> branches (b :: pre) rest)
          in
          head_part (classify x) (fun x' -> Case (d, s, m, x', bs)) (fun () ->
          normal_part (classify m) (fun m' -> Case (d, s, m', x, bs)) (fun () -> branches [] bs))
      | Fix (a, k, b) ->
          normal_part (classify a) (fun a' -> Fix (a', k, b)) (fun () ->
          normal_part (classify b) (fun b' -> Fix (a, k, b')) (fun () -> Neutral))

let rec head_step sg t =
  let head_step = head_step sg in
  match contract sg t with
  | Some _ as step -> step
  | None ->
      match t with
      | App (f, a) when full_spine sg t -> Option.map (fun a' -> App (f, a')) (head_step a)
      | App (f, a) -> Option.map (fun f' -> App (f', a)) (head_step f)
      | Case (d, s, m, x, bs) -> Option.map (fun x' -> Case (d, s, m, x', bs)) (head_step x)
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

(* Conversion by normalizing both sides, [convert_full] of Eval.v. *)
let convert_full ?(sg = empty_signature) fuel t u =
  if t = u then ConvEqual t
  else
    match normalize ~sg fuel t, normalize ~sg fuel u with
    | NormalForm t', NormalForm u' ->
        if t' = u' then ConvEqual t' else ConvDifferent
    | StuckTerm _, _ | _, StuckTerm _ -> ConvStuck
    | _ -> ConvOutOfFuel

(* [has_def t]: [t] mentions a δ-constant. *)
let rec has_def = function
  | Const (Def _) -> true
  | Srt _ | Var _ | Void | Unit | Tt | Bool | BTrue | BFalse | Const _ -> false
  | Pi (a, b) | Sigma (a, b) | Fix (a, _, b) | App (a, b) | Ann (a, b) | ElimVoid (a, b) | Pair (a, b) ->
      has_def a || has_def b
  | Lam b | Fst b | Snd b -> has_def b
  | ElimUnit (c, d, u) -> has_def c || has_def d || has_def u
  | ElimBool (c, t, f, b) -> has_def c || has_def t || has_def f || has_def b
  | Case (_, _, p, x, bs) -> has_def p || has_def x || List.exists has_def bs

(* [def_head t]: the head of the spine of [t] is a δ-constant. *)
let rec def_head = function App (f, _) -> def_head f | Const (Def _) -> true | _ -> false

(* The signature with its δ-constants opaque, [sig_opaque] of Signature.v. *)
let opaque sg = List.filter (function EDef _ -> false | _ -> true) sg

(* [conv_lazy] of Eval.v: two normal forms of the opaque signature,
   compared position by position in one pass.  A comparison gives the
   common reduct, if it finds one, and whether it has unfolded
   δ-constants.  A difference found without unfolding, in a spine with a
   δ-constant at the head on one side ([root]: not the function of an
   application), normalizes the two spines with δ. *)
let conv_lazy sg fuel =
  let ( let* ) (m, d) k =
    match m with Some a -> let r, d' = k a in (r, d || d') | None -> (None, d)
  in
  let ret v = (Some v, false) in
  let rec conv root t u =
    match step t u with
    | None, false when root && (def_head t || def_head u) ->
        ((match convert_full ~sg fuel t u with ConvEqual v -> Some v | _ -> None), true)
    | r -> r
  and step t u =
    let cl = conv true and cf = conv false in
    match t, u with
    | Pi (a, b), Pi (a', b') -> let* a1 = cl a a' in let* b1 = cl b b' in ret (Pi (a1, b1))
    | Sigma (a, b), Sigma (a', b') -> let* a1 = cl a a' in let* b1 = cl b b' in ret (Sigma (a1, b1))
    | Lam b, Lam b' -> let* c = cl b b' in ret (Lam c)
    | App (f, a), App (f', a') -> let* g = cf f f' in let* c = cl a a' in ret (App (g, c))
    | Pair (a, b), Pair (a', b') -> let* c = cl a a' in let* d = cl b b' in ret (Pair (c, d))
    | Fst p, Fst p' -> let* q = cl p p' in ret (Fst q)
    | Snd p, Snd p' -> let* q = cl p p' in ret (Snd q)
    | ElimVoid (c, e), ElimVoid (c', e') ->
        let* c1 = cl c c' in let* e1 = cl e e' in ret (ElimVoid (c1, e1))
    | ElimUnit (c, d, x), ElimUnit (c', d', x') ->
        let* c1 = cl c c' in let* d1 = cl d d' in let* x1 = cl x x' in ret (ElimUnit (c1, d1, x1))
    | ElimBool (c, bt, bf, b), ElimBool (c', bt', bf', b') ->
        let* c1 = cl c c' in let* bt1 = cl bt bt' in let* bf1 = cl bf bf' in
        let* b1 = cl b b' in ret (ElimBool (c1, bt1, bf1, b1))
    | Case (d, s, p, x, bs), Case (d', s', p', x', bs') ->
        if d = d' && s = s' then
          let* p1 = cl p p' in let* x1 = cl x x' in let* bs1 = branches bs bs' in
          ret (Case (d, s, p1, x1, bs1))
        else (None, false)
    | Fix (a, k, b), Fix (a', k', b') ->
        if k = k' then let* a1 = cl a a' in let* b1 = cl b b' in ret (Fix (a1, k, b1))
        else (None, false)
    | _ -> ((if t = u then Some t else None), false)
  and branches bs bs' =
    match bs, bs' with
    | [], [] -> ret []
    | b :: bs, b' :: bs' -> let* c = conv true b b' in let* cs = branches bs bs' in ret (c :: cs)
    | _ -> (None, false)
  in
  conv true

(* [convert] of Eval.v: when a side mentions a δ-constant and the sides
   differ, they are normalized with δ-constants opaque and compared lazily
   first; otherwise, and when that does not show them equal,
   [convert_full]. *)
let convert ?(sg = empty_signature) fuel t u =
  let lazy_answer =
    if (has_def t || has_def u) && t <> u then
      match normalize ~sg:(opaque sg) fuel t, normalize ~sg:(opaque sg) fuel u with
      | NormalForm t1, NormalForm u1 -> fst (conv_lazy sg fuel t1 u1)
      | _ -> None
    else None
  in
  match lazy_answer with Some v -> ConvEqual v | None -> convert_full ~sg fuel t u

type error =
  | EUnboundVar of int | ENotInSystem of sort | ETopSort of sort
  | ENoRule of term * sort * sort | ENotASort of term * term
  | ENotAPi of term * term | EMismatch of term * term * term
  | EStuckType of term * term * term | ECannotInfer of term
  | ENoPrimitives of term | EBadFamily of term * term * term
  | ENoSigmaRule of term * sort * sort | ENotASigma of term * term
  | ENoDecls of term | EUnknownConst of gref
  | ENotInductive of term * string * term | EElimSort of string * sort
  | EBranchCount of term * int * int | ENoStructArg of term * int * term
  | EStructNotInductive of term * int * term | EFixBody of term * int
  | ENotGuarded of term * guard_error

type event =
  | EvCtxEntry of int * term | EvExpected of term | EvTerm of term
  | EvAxiom of sort * sort | EvRule of sort * sort * sort
  | EvUnfoldSort of term * term * sort
  | EvUnfoldPi of term * term * term * term
  | EvArg of term * term | EvSubst of term * term * term
  | EvConv of term * term * term | EvFamily of term * term * sort
  | EvSigmaRule of sort * sort * sort
  | EvUnfoldSigma of term * term * term * term
  | EvCase of string * sort * term list * term list
  | EvBranch of string * term | EvFix of int * string | EvGuard of int

type failure = Reject of error | NoFuel of term
type 'a answer = Accepted of 'a | Rejected of error | Undecided of term

(* A step of the checker succeeds or stops the run.  Events go to a queue
   owned by the run, so the ones emitted before a failure are kept. *)
type 'a checked = ('a, failure) result

let return = Result.ok
let reject error = Error (Reject error)
let no_fuel term = Error (NoFuel term)

type checker = {
  infer_in : ctx -> term -> term checked;
  check_in : ctx -> term -> term -> unit checked;
  infer_open : ctx -> term -> term checked;
  infer_spine_open : ctx -> term -> term list checked;
}

(* The checker for one specification, signature and fuel budget, like
   [Section Check] in Check.v: [spec], [sg], [fuel] and [record], which
   receives each event of the trace, are fixed for the run. *)
let make_checker spec sg fuel record =
  let whnf = whnf ~sg and convert = convert ~sg in
  let emit event = record event; Ok () in

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
  (* The type of a scrutinee unfolded to [D ps us]. *)
  let as_ind scrutinee ty name d =
    match whnf fuel ty with
    | HeadForm ty' ->
        let p = List.length d.ind_params in
        (match spine ty' with
         | Const (Ind name'), args
           when name' = name && List.compare_length_with args (p + List.length d.ind_indices) = 0 ->
             return (take p args, drop p args)
         | _ -> reject (ENotInductive (scrutinee, name, ty')))
    | HeadOutOfFuel _ -> no_fuel scrutinee
  in
  (* The [k]-th domain of the type of the fix [term] unfolds to a family. *)
  let rec struct_ind term k0 ty k =
    match whnf fuel ty with
    | HeadForm (Pi (domain, codomain)) ->
        if k > 0 then struct_ind term k0 codomain (k - 1)
        else (match whnf fuel domain with
              | HeadForm domain' ->
                  (match spine domain' with
                   | Const (Ind name), _ ->
                       (match find_ind sg name with
                        | Some _ -> return name
                        | None -> reject (EUnknownConst (Ind name)))
                   | _ -> reject (EStructNotInductive (term, k0, domain')))
              | HeadOutOfFuel _ -> no_fuel term)
    | HeadForm other -> reject (ENoStructArg (term, k0, other))
    | HeadOutOfFuel _ -> no_fuel term
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
    | Case (name, s, motive, scrutinee, branches) ->
        if not spec.constants then reject (ENoDecls term)
        else (match find_ind sg name with
              | None -> reject (EUnknownConst (Ind name))
              | Some d ->
                  if not (allows_elimination spec d.ind_elim s) then reject (EElimSort (name, s))
                  else if List.compare_lengths branches d.ind_ctors <> 0 then
                    reject (EBranchCount (term, List.length d.ind_ctors, List.length branches))
                  else
                    let* scrutinee_ty = infer gamma scrutinee in
                    let* params, indices = as_ind scrutinee scrutinee_ty name d in
                    let* () = emit (EvCase (name, s, params, indices)) in
                    let* () = check gamma motive (case_motive_type d params s) in
                    let* () =
                      List.fold_left2 (fun acc c b ->
                        let* () = acc in
                        let ty = case_branch_type d params motive c in
                        let* () = emit (EvBranch (c.ctor_name, ty)) in
                        check gamma b ty) (return ()) d.ind_ctors branches
                    in
                    return (apps motive (indices @ [scrutinee])))
    | Fix (ty, k, body) ->
        let* _ = infer_sort gamma ty in
        let* name = struct_ind term k ty k in
        let* () = emit (EvFix (k, name)) in
        if has_lams (k + 1) body then
          let* () = check (ty :: gamma) body (lift 1 ty) in
          let* () =
            match guard_fix sg k body with
            | Ok () -> emit (EvGuard k)
            | Error e -> reject (ENotGuarded (term, e))
          in
          return ty
        else reject (EFixBody (term, k))

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
  (* The types of an application and of its prefixes, outermost first, in
     the steps of [infer] and in its order: [infer_spine] of Check.v. *)
  let rec infer_spine gamma term =
    match term with
    | App (fn, argument) ->
        let* types = infer_spine gamma fn in
        (match types with
         | function_ty :: _ ->
             let* domain, codomain = as_pi fn function_ty in
             let* () = check gamma argument domain in
             return (subst1 codomain argument :: types)
         | [] -> return [])
    | _ ->
        let* ty = infer gamma term in
        return [ ty ]
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
  { infer_in; check_in; infer_open = infer; infer_spine_open = infer_spine }

let to_answer = function
  | Ok value -> Accepted value
  | Error (Reject error) -> Rejected error
  | Error (NoFuel term) -> Undecided term

(* A run with its trace, in order, as [run_answer] of Check.v. *)
let run spec sg fuel task =
  let log = Queue.create () in
  let answer = to_answer (task (make_checker spec sg fuel (fun event -> Queue.add event log))) in
  List.of_seq (Queue.to_seq log), answer

(* The same run for its answer alone: the events are dropped as they come,
   so no log is built and the terms they mention are not kept alive until
   the end of the run. *)
let run_quiet spec sg fuel task = to_answer (task (make_checker spec sg fuel ignore))

let run_infer ?(sg = empty_signature) spec fuel gamma term =
  run spec sg fuel (fun checker -> checker.infer_in gamma term)

let run_check ?(sg = empty_signature) spec fuel gamma term expected =
  run spec sg fuel (fun checker -> checker.check_in gamma term expected)

(* [infer] of Check.v alone, in a context taken as checked: the types of
   subterms that erasure asks for (erasure-cic, reference/erase_native.ml).
   diff.ml compares it with [run_answer (infer …)] of the extract.  Callers
   that drop the events use [infer_open_answer]. *)
let run_infer_open ?(sg = empty_signature) spec fuel gamma term =
  run spec sg fuel (fun checker -> checker.infer_open gamma term)

(* [infer_spine] of Check.v, in a context taken as checked: the types of an
   application and of its prefixes, for the erasure of applications. *)
let run_infer_spine_open ?(sg = empty_signature) spec fuel gamma term =
  run spec sg fuel (fun checker -> checker.infer_spine_open gamma term)

(* The answers of [run_infer_open] and [run_infer_spine_open] alone, without
   the trace, which erasure does not use. *)
let infer_open_answer ?(sg = empty_signature) spec fuel gamma term =
  run_quiet spec sg fuel (fun checker -> checker.infer_open gamma term)

let infer_spine_open_answer ?(sg = empty_signature) spec fuel gamma term =
  run_quiet spec sg fuel (fun checker -> checker.infer_spine_open gamma term)

(* Call-by-value evaluation of source programs, as [eval_nested] of
   EvalSrc.v, one application at a time: weak, the function and then the
   argument, constructors and families applied to values are values, and
   so are eliminators and fixes short of their arguments; the budget
   bounds the depth of the evaluation.  The extracted [eval_src] walks
   each spine once and is proved equal to [eval_nested], so diff.ml
   compares it with this direct version. *)
type cbv_result = CbvValue of term | CbvStuck of term | CbvOutOfFuel

let spine_value sg t =
  match spine t with
  | Const (Ctor _), _ | Const (Ind _), _ -> true
  | h, args -> (match head_arity sg h with Some m -> List.compare_length_with args m < 0 | None -> false)

let rec eval_src ?(sg = empty_signature) fuel t =
  if fuel <= 0 then CbvOutOfFuel
  else
    let ev = eval_src ~sg (fuel - 1) in
    let ( let* ) r k = match r with CbvValue v -> k v | other -> other in
    match t with
    | Var _ -> CbvStuck t
    | Srt _ | Pi _ | Sigma _ | Lam _ | Void | Unit | Bool | Tt | BTrue | BFalse | Fix _ -> CbvValue t
    | Const g -> (match delta sg g with Some body -> ev body | None -> CbvValue t)
    | Ann (u, _) -> ev u
    | App (f, a) ->
        let* vf = ev f in
        let* va = ev a in
        (match vf with
         | Lam b -> ev (subst1 b va)
         | _ ->
             let u = App (vf, va) in
             (match spine_iota sg u with
              | Some r -> ev r
              | None -> if spine_value sg u then CbvValue u else CbvStuck u))
    | Pair (a, b) ->
        let* va = ev a in
        let* vb = ev b in
        CbvValue (Pair (va, vb))
    | Fst p -> let* v = ev p in (match v with Pair (a, _) -> CbvValue a | _ -> CbvStuck (Fst v))
    | Snd p -> let* v = ev p in (match v with Pair (_, b) -> CbvValue b | _ -> CbvStuck (Snd v))
    | ElimVoid (c, e) -> let* v = ev e in CbvStuck (ElimVoid (c, v))
    | ElimUnit (c, branch, u) ->
        let* v = ev u in (match v with Tt -> ev branch | _ -> CbvStuck (ElimUnit (c, branch, v)))
    | ElimBool (c, yes, no, b) ->
        let* v = ev b in
        (match v with BTrue -> ev yes | BFalse -> ev no | _ -> CbvStuck (ElimBool (c, yes, no, v)))
    | Case (d, s, m, x, bs) ->
        let* v = ev x in
        let u = Case (d, s, m, v, bs) in
        (match case_iota sg u with Some r -> ev r | None -> CbvStuck u)

(* A small direct demo, so [ocaml reference/pts_native.ml] works like the
   standalone reference file in strictness-pcf.  Rich named printing stays
   in extraction/pretty.ml; here the indices remain visible. *)
let show_sort = function
  | Star -> "∗" | Box -> "□" | Tri -> "△"
  | Univ i -> "Type_" ^ string_of_int i
  | Prp -> "Prop"

(* An instance by the sort of its motives: elimD[j] for Type_j. *)
let show_elim_sort = function Univ j -> string_of_int j | s -> show_sort s

let show_gref = function
  | Ind d -> d | Ctor (_, c) -> c | Def f -> f
  | Elim (d, s) -> "elim" ^ d ^ "[" ^ show_elim_sort s ^ "]"

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
  | Case (d, s, m, x, bs) ->
      "match" ^ d ^ "[" ^ show_elim_sort s ^ "](" ^ show_term x ^ " return " ^ show_term m
      ^ " with " ^ String.concat " | " (List.map show_term bs) ^ ")"
  | Fix (a, k, b) -> "(fix : " ^ show_term a ^ " {struct " ^ string_of_int k ^ "} := " ^ show_term b ^ ")"

let show_guard_error = function
  | GPartialCall c -> "partial call " ^ show_term c
  | GNotSubterm (c, a) -> "call " ^ show_term c ^ " not on a subterm: " ^ show_term a
  | GShortBody b -> "fix body short of its λ at " ^ show_term b

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
  | ENotInductive (t, d, ty) -> show_term t ^ " : " ^ show_term ty ^ " is not in " ^ d
  | EElimSort (d, s) -> "no elimination of " ^ d ^ " into " ^ show_sort s
  | EBranchCount (_, k, n) ->
      string_of_int n ^ " branches for " ^ string_of_int k ^ " constructors"
  | ENoStructArg (_, k, ty) -> "no argument " ^ string_of_int k ^ ": " ^ show_term ty
  | EStructNotInductive (_, k, ty) ->
      "structural argument " ^ string_of_int k ^ " of non-inductive type " ^ show_term ty
  | EFixBody (_, k) -> "fix body without " ^ string_of_int (k + 1) ^ " λ"
  | ENotGuarded (_, g) -> show_guard_error g

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
