(** * Lecture examples

    Terms shared by the regression tests (Tests.v) and the OCaml
    demonstrations (extraction/).  Contexts list the innermost entry
    first, as [ctx] does. *)

From Stdlib Require Import List.
Import ListNotations.
From DepTypes.PTS Require Import Syntax.

(** ** U⁻ *)

(** [ΠA:∗. A → A] and the polymorphic identity. *)
Definition id_ty : term := Pi (Srt Star) (Pi (Var 0) (Var 1)).
Definition id_tm : term := Ann (Lam (Lam (Var 0))) id_ty.

(** [A : ∗, x : A ⊢ id A x : A]. *)
Definition id_applied_ctx : ctx := [Var 0; Srt Star].
Definition id_applied : term := App (App id_tm (Var 1)) (Var 0).

(** [A : ∗ ⊢ A → ∗] needs the rule (∗, □), which U⁻ lacks: types do not
    depend on terms. *)
Definition star_box_ctx : ctx := [Srt Star].
Definition star_box : term := Pi (Var 0) (Srt Star).

(** ** The predicative hierarchy *)

(** Large elimination: the family [λ_. Type_0 : Bool → Type_1] computes a
    type from a boolean; [large_elim_ty] is [Unit]. *)
Definition type_family : term := Ann (Lam (Srt (Univ 0))) (Pi Bool (Srt (Univ 1))).
Definition large_elim_ty : term := ElimBool type_family Unit Bool BTrue.

(** ** Raw terms *)

(** Ω = (λx. x x) (λx. x x), without a normal form; it does not
    synthesize in the annotated kernel (Tests.v, [omega_not_synth]). *)
Definition self_app : term := Lam (App (Var 0) (Var 0)).
Definition raw_omega : term := App self_app self_app.
