(** * Runs of the checker on named terms

    The examples state what the checker answers on a named term in a
    named context ([infers], [checks]), whether conversion shows two named
    terms equal ([converts]), and the error of a refused run
    ([refusal]).  Like PTS.Build, these are conveniences of the examples,
    not part of the kernel; unlike PTS.Build, no module re-exports them,
    so that projects with helpers of the same names are not affected. *)

From Stdlib Require Import String List.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Named Spec Signature Eval Check Build.

(** A run of an entry point of the checker on a named term in a named
    context, innermost entry first: its answer. *)
Definition infers (S : spec) (sg : signature) (fuel : nat) (g : list (string * nterm)) (t : nterm)
  : answer term :=
  snd (run_infer S sg fuel (in_ctx g) (term_in g t)).

Definition checks (S : spec) (sg : signature) (fuel : nat) (g : list (string * nterm)) (t T : nterm)
  : answer unit :=
  snd (run_check S sg fuel (in_ctx g) (term_in g t) (term_in g T)).

(** Whether conversion reports two named terms equal. *)
Definition converts (sg : signature) (fuel : nat) (g : list (string * nterm)) (t u : nterm) : bool :=
  match convert sg fuel (term_in g t) (term_in g u) with ConvEqual _ => true | _ => false end.

(** The error of a refused run. *)
Definition refusal {A} (a : answer A) : option error :=
  match a with Rejected e => Some e | _ => None end.
