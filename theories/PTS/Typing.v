(** * Declarative typing, parameterized by a PTS specification

    [has_type S Γ t A], written [S ;; Γ ⊢ t ∈ A], together with the
    well-formedness of contexts [wf_ctx S Γ].  These are the standard PTS
    rules for sorts, variables, Π, λ, application and conversion, with
    three additions:
    - λ is unannotated: [T_Lam] reads its domain off the Π-type;
    - [Ann t A] has type [A] when [A] is a type of some sort;
    - when [spec_prim S = Some s0], the primitives Void, Unit, Bool with
      their constructors and dependent eliminators.  An eliminator takes a
      result family [C : Πx:T. s] for an arbitrary sort [s]; for [s] a
      universe this is large elimination.

    In [T_App] the argument is substituted into the type of the result,
    [B[u/0]]: this is where terms enter types.

    This system is more liberal than the checker: [T_App] with [T_Lam]
    types the unannotated redex [(λ. b) u], which the checker rejects.
    Completeness of the checker is therefore stated for the annotated
    bidirectional kernel of PTS.Bidir, and reaches this system only after
    annotations are inserted. *)

From Stdlib Require Import List.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Spec Reduction.

Reserved Notation "S ;; G ⊢ t ∈ A" (at level 70, G at next level, t at next level).

Section Typing.
  Variable S : spec.

  Inductive wf_ctx : ctx -> Prop :=
  | W_Nil : wf_ctx []
  | W_Cons : forall G A s,
      has_type G A (Srt s) ->
      wf_ctx (A :: G)

  with has_type : ctx -> term -> term -> Prop :=
  | T_Sort : forall G s s',
      wf_ctx G ->
      spec_axiom S s = Some s' ->
      has_type G (Srt s) (Srt s')
  | T_Var : forall G n A,
      wf_ctx G ->
      lookup G n = Some A ->
      has_type G (Var n) A
  | T_Pi : forall G A B s1 s2 s3,
      has_type G A (Srt s1) ->
      has_type (A :: G) B (Srt s2) ->
      spec_rule S s1 s2 = Some s3 ->
      has_type G (Pi A B) (Srt s3)
  | T_Lam : forall G A B b s,
      has_type (A :: G) b B ->
      has_type G (Pi A B) (Srt s) ->
      has_type G (Lam b) (Pi A B)
  | T_App : forall G f u A B,
      has_type G f (Pi A B) ->
      has_type G u A ->
      has_type G (App f u) (subst1 B u)
  | T_Ann : forall G t A s,
      has_type G A (Srt s) ->
      has_type G t A ->
      has_type G (Ann t A) A
  | T_Conv : forall G t A B s,
      has_type G t A ->
      has_type G B (Srt s) ->
      A ≡ B ->
      has_type G t B
  (** MLTT primitives *)
  | T_Void : forall G s0,
      wf_ctx G -> spec_prim S = Some s0 ->
      has_type G Void (Srt s0)
  | T_ElimVoid : forall G C e s,
      has_type G C (Pi Void (Srt s)) ->
      has_type G e Void ->
      has_type G (ElimVoid C e) (App C e)
  | T_Unit : forall G s0,
      wf_ctx G -> spec_prim S = Some s0 ->
      has_type G Unit (Srt s0)
  | T_Tt : forall G s0,
      wf_ctx G -> spec_prim S = Some s0 ->
      has_type G Tt Unit
  | T_ElimUnit : forall G C c u s,
      has_type G C (Pi Unit (Srt s)) ->
      has_type G c (App C Tt) ->
      has_type G u Unit ->
      has_type G (ElimUnit C c u) (App C u)
  | T_Bool : forall G s0,
      wf_ctx G -> spec_prim S = Some s0 ->
      has_type G Bool (Srt s0)
  | T_True : forall G s0,
      wf_ctx G -> spec_prim S = Some s0 ->
      has_type G BTrue Bool
  | T_False : forall G s0,
      wf_ctx G -> spec_prim S = Some s0 ->
      has_type G BFalse Bool
  | T_ElimBool : forall G C t f b s,
      has_type G C (Pi Bool (Srt s)) ->
      has_type G t (App C BTrue) ->
      has_type G f (App C BFalse) ->
      has_type G b Bool ->
      has_type G (ElimBool C t f b) (App C b).
End Typing.

Notation "S ;; G ⊢ t ∈ A" := (has_type S G t A).

Scheme wf_ctx_mut := Induction for wf_ctx Sort Prop
  with has_type_mut := Induction for has_type Sort Prop.

(** Every typable sort is a sort of the system.  This is where the
    invariant [spec_wf] is needed: the typing rules do not consult
    [spec_sort] themselves. *)
Lemma typed_sort_in_spec : forall S G s A,
    S ;; G ⊢ Srt s ∈ A -> spec_sort S s = true.
Proof.
  intros S G s A H. remember (Srt s) as t eqn:Et.
  induction H; try discriminate.
  - injection Et as ->. edestruct spec_axiom_sorts as [Hs _]; [eassumption | exact Hs].
  - auto.
Qed.
