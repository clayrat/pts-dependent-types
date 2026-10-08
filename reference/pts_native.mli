(* Interface of the native PTS reference.  The checker monad and the
   individual typing steps stay private; callers see the syntax, the
   specifications, the evaluator and the two traced entry points. *)

(** {1 Syntax} *)

type sort = Star | Box | Tri | Univ of int

type term =
  | Srt of sort | Var of int | Pi of term * term | Lam of term
  | App of term * term | Ann of term * term
  | Void | ElimVoid of term * term
  | Unit | Tt | ElimUnit of term * term * term
  | Bool | BTrue | BFalse | ElimBool of term * term * term * term

type ctx = term list                         (* innermost entry first *)

(** {1 Specifications} *)

type spec = {
  sort_allowed : sort -> bool;
  axiom : sort -> sort option;
  product : sort -> sort -> sort option;
  primitive_sort : sort option;
}

val lambda_star : spec
val system_u_minus : spec
val system_u : spec
val pure_predicative : spec
val predicative : spec

(** {1 Substitution} *)

val lift : int -> term -> term
val subst1 : term -> term -> term

(** {1 Evaluation} *)

type shape = Step of term | Neutral | Normal | Stuck

val classify : term -> shape

type eval_result = NormalForm of term | StuckTerm of term | OutOfFuel of term
type head_result = HeadForm of term | HeadOutOfFuel of term
type conv_result = ConvEqual of term | ConvDifferent | ConvOutOfFuel | ConvStuck

val normalize_trace : int -> term -> term list * eval_result
val normalize : int -> term -> eval_result
val whnf : int -> term -> head_result
val convert : int -> term -> term -> conv_result

(** {1 Type checking} *)

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

type 'a answer = Accepted of 'a | Rejected of error | Undecided of term

(* Both entry points check the context first and return events in order. *)
val run_infer : spec -> int -> ctx -> term -> event list * term answer
val run_check : spec -> int -> ctx -> term -> term -> event list * unit answer

(** {1 Printing} *)

val show_sort : sort -> string
val show_term : term -> string
val show_error : error -> string
val show_answer : ('a -> string) -> 'a answer -> string
