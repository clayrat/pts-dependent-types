(* Interface of the native PTS reference.  The checker monad and the
   individual typing steps stay private; callers see the syntax, the
   specifications, signatures, the evaluator and the two traced entry
   points.  Evaluation and checking take a signature as an optional [~sg],
   the empty one by default. *)

(** {1 Syntax} *)

type sort = Star | Box | Tri | Univ of int | Prp   (* Prp is Prop *)

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

(** {1 Specifications} *)

type spec = {
  sort_allowed : sort -> bool;
  axiom : sort -> sort option;
  product : sort -> sort -> sort option;
  primitive_sort : sort option;
  sigma : sort -> sort -> sort option;
  constants : bool;
}

val lambda_star : spec
val system_u_minus : spec
val system_u : spec
val pure_predicative : spec
val predicative : spec
val coc : spec
val predicative_prop : spec

(** {1 Substitution} *)

val lift : int -> term -> term
val subst1 : term -> term -> term
val subst : (int -> term) -> term -> term    (* parallel: index n becomes [sb n] *)
val closed_above : int -> term -> bool

(** {1 Spines and telescopes} *)

val apps : term -> term list -> term
val spine : term -> term * term list
val pis : term list -> term -> term
val lams : int -> term -> term
val vars : int -> int -> term list
val take : int -> 'a list -> 'a list
val drop : int -> 'a list -> 'a list
(* [vars base n]: the variables of a telescope of n entries lying [base]
   binders up, outermost first. *)
val has_lams : int -> term -> bool          (* the body starts with at least n λ *)

(** {1 Signatures} *)

type field = FArg of term | FRec of term list * term list
type ctor_desc = { ctor_name : string; ctor_fields : field list; ctor_indices : term list }
type elim_class = PropOnly | AllSorts      (* the sorts of the motives of D *)
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

type signature = entry list                  (* newest first *)

val empty_signature : signature
val sig_add : signature -> entry -> signature option
val telescope_closed : int -> term list -> bool
(* None if the new entry is not closed; a signature built from
   [empty_signature] by [sig_add] is closed throughout. *)
val find_ind : signature -> string -> ind_desc option
val find_elim : signature -> string -> sort -> (term * bool) option
val find_def : signature -> string -> (term * term) option
val sig_type : signature -> gref -> term option

(* A motive into the sort: a sort of the table that the category admits. *)
val allows_elimination : spec -> elim_class -> sort -> bool

(* The types of a description: [field_type D p l fd] of the field at
   position l, in the context of the p parameters and the earlier fields;
   [D : Π(Δ). Πθ̄. s]; [c : Π(Δ). Π(fields). D Δ ū]. *)
val field_type : string -> int -> int -> field -> term
val ind_type : ind_desc -> term
val ctor_type : ind_desc -> ctor_desc -> term
val method_args : string -> sort -> term list -> term list -> field list -> term list -> term list

(* The arguments of the method in an ι-rule: [method_args D s pre env fields
   xs] gives each field and, after a recursive one, its hypothesis; [pre]
   are the parameters, motive and methods, [env] the parameters, innermost
   first. *)
val iota : signature -> term -> term option

(* match and fix: ι of a match on a constructor; the types of the motive
   and of the branch of a constructor for the parameters [ps]; the
   unfolding of a fix applied up to a structural constructor argument;
   the spines contracted at their last argument. *)
val case_iota : signature -> term -> term option
val inst_params : term list -> int -> term -> term
val case_motive_type : ind_desc -> term list -> sort -> term
val case_branch_type : ind_desc -> term list -> term -> ctor_desc -> term
val fix_unfold : term -> term option
val full_spine : signature -> term -> bool
val spine_iota : signature -> term -> term option

(** {1 The guard of fix} *)

type mark = Large | Arg | Sub of int | Self
type guard_error = GPartialCall of term | GNotSubterm of term * term | GShortBody of term

(* [guard sg k ms t spine]: the recursive calls of [t] for the marks [ms]
   of its variables, innermost first, and the structural position [k];
   [guard_fix sg k b] the body of [Fix A k b] after its leading λ. *)
val entry_marks : int -> mark list
val guard : signature -> int -> mark list -> term -> bool -> (unit, guard_error) result
val guard_fix : signature -> int -> term -> (unit, guard_error) result

(** {1 Evaluation} *)

type shape = Step of term | Neutral | Normal | Stuck

val classify : ?sg:signature -> term -> shape

type eval_result = NormalForm of term | StuckTerm of term | OutOfFuel of term
type head_result = HeadForm of term | HeadOutOfFuel of term
type conv_result = ConvEqual of term | ConvDifferent | ConvOutOfFuel | ConvStuck

val normalize_trace : ?sg:signature -> int -> term -> term list * eval_result
val normalize : ?sg:signature -> int -> term -> eval_result
val whnf : ?sg:signature -> int -> term -> head_result
val convert : ?sg:signature -> int -> term -> term -> conv_result

(** {1 Type checking} *)

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

type 'a answer = Accepted of 'a | Rejected of error | Undecided of term

(* Both entry points check the context first and return events in order. *)
val run_infer : ?sg:signature -> spec -> int -> ctx -> term -> event list * term answer
val run_check : ?sg:signature -> spec -> int -> ctx -> term -> term -> event list * unit answer

(* [infer] of Check.v alone, in a context taken as checked: the types of
   subterms that erasure asks for. *)

(* [infer] of Check.v alone, in a context taken as checked: the types of
   subterms that erasure asks for. *)
val run_infer_open : ?sg:signature -> spec -> int -> ctx -> term -> event list * term answer

(** {1 Call-by-value evaluation} *)

type cbv_result = CbvValue of term | CbvStuck of term | CbvOutOfFuel

val spine_value : signature -> term -> bool
val eval_src : ?sg:signature -> int -> term -> cbv_result

(** {1 Printing} *)

val show_sort : sort -> string
val show_term : term -> string
val show_error : error -> string
val show_answer : ('a -> string) -> 'a answer -> string
