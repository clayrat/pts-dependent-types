(* Interface of the native PTS reference.  The checker monad and the
   individual typing steps stay private; callers see the syntax, the
   specifications, signatures, the evaluator and the two traced entry
   points.  Evaluation and checking take a signature as an optional [~sg],
   the empty one by default. *)

(** {1 Syntax} *)

type sort = Star | Box | Tri | Univ of int

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

(** {1 Substitution} *)

val lift : int -> term -> term
val subst1 : term -> term -> term
val apps : term -> term list -> term

(** {1 Signatures} *)

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

type signature = entry list                  (* newest first *)

val empty_signature : signature
val sig_add : signature -> entry -> signature option
(* None if the new entry is not closed; a signature built from
   [empty_signature] by [sig_add] is closed throughout. *)
val sig_type : signature -> gref -> term option
val iota : signature -> term -> term option

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

type event =
  | EvCtxEntry of int * term | EvExpected of term | EvTerm of term
  | EvAxiom of sort * sort | EvRule of sort * sort * sort
  | EvUnfoldSort of term * term * sort
  | EvUnfoldPi of term * term * term * term
  | EvArg of term * term | EvSubst of term * term * term
  | EvConv of term * term * term | EvFamily of term * term * sort
  | EvSigmaRule of sort * sort * sort
  | EvUnfoldSigma of term * term * term * term

type 'a answer = Accepted of 'a | Rejected of error | Undecided of term

(* Both entry points check the context first and return events in order. *)
val run_infer : ?sg:signature -> spec -> int -> ctx -> term -> event list * term answer
val run_check : ?sg:signature -> spec -> int -> ctx -> term -> term -> event list * unit answer

(** {1 Printing} *)

val show_sort : sort -> string
val show_term : term -> string
val show_error : error -> string
val show_answer : ('a -> string) -> 'a answer -> string
