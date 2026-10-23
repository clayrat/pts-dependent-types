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
      universe this is large elimination;
    - Σ formed by the rules [spec_sigma S], pairs and projections, the
      second one at [B[fst p/0]];
    - when [spec_decls S], the constants of a signature [sg] at their
      closed types.

    Conversion is that of the signature; the judgment is
    [has_type S sg Γ t A], and PTS.EmptySig gives the notation
    [S ;; Γ ⊢ t ∈ A] for the empty signature.

    In [T_App] the argument is substituted into the type of the result,
    [B[u/0]]: this is where terms enter types.

    This system is more liberal than the checker: [T_App] with [T_Lam]
    types the unannotated redex [(λ. b) u], which the checker rejects.
    Completeness of the checker is therefore stated for the annotated
    bidirectional kernel of PTS.Bidir, and reaches this system only after
    annotations are inserted. *)

From Stdlib Require Import List.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Spec Signature Reduction.

Reserved Notation "S ;; G ⊢ t ∈ A" (at level 70, G at next level, t at next level).

Section Typing.
  Variable S : spec.
  Variable sg : signature.
  Local Notation "t ≡ u" := (conv sg t u).

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
      has_type G (ElimBool C t f b) (App C b)
  (** dependent pairs *)
  | T_Sigma : forall G A B s1 s2 s3,
      has_type G A (Srt s1) ->
      has_type (A :: G) B (Srt s2) ->
      spec_sigma S s1 s2 = Some s3 ->
      has_type G (Sigma A B) (Srt s3)
  | T_Pair : forall G A B a b s,
      has_type G (Sigma A B) (Srt s) ->
      has_type G a A ->
      has_type G b (subst1 B a) ->
      has_type G (Pair a b) (Sigma A B)
  | T_Fst : forall G p A B,
      has_type G p (Sigma A B) ->
      has_type G (Fst p) A
  | T_Snd : forall G p A B,
      has_type G p (Sigma A B) ->
      has_type G (Snd p) (subst1 B (Fst p))
  (** constants *)
  | T_Const : forall G g A,
      wf_ctx G -> spec_decls S = true -> sig_type sg g = Some A ->
      has_type G (Const g) A.

  Scheme wf_ctx_mut := Induction for wf_ctx Sort Prop
    with has_type_mut := Induction for has_type Sort Prop.
End Typing.

(** ** Type-correct signatures

    A signature carries only closedness, and the checker trusts the types
    of its constants.  The declarative metatheory needs more: the type of
    every constant is a type, every δ-body has the type of its constant,
    and every ι-contraction of an instance with active rules keeps the
    type of the redex.  Checking each ι-rule against one type in the
    generic context of its parameters, motive, methods and fields, as the
    procedures registering instances do, is the local form of the last
    condition. *)

Definition signature_typed (S : spec) (sg : signature) : Prop :=
  (forall g A, sig_type sg g = Some A -> exists s, has_type S sg [] A (Srt s)) /\
  (forall g A b, sig_type sg g = Some A -> sig_delta sg g = Some b -> has_type S sg [] b A) /\
  (forall G t u T, iota sg t = Some u -> has_type S sg G t T -> has_type S sg G u T).

(** Every typable sort is a sort of the system.  This is where the
    invariant [spec_wf] is needed: the typing rules do not consult
    [spec_sort] themselves. *)
Lemma typed_sort_in_spec : forall S sg G s A,
    has_type S sg G (Srt s) A -> spec_sort S s = true.
Proof.
  intros S sg G s A H. remember (Srt s) as t eqn:Et.
  induction H; try discriminate.
  - injection Et as ->. edestruct spec_axiom_sorts as [Hs _]; [eassumption | exact Hs].
  - auto.
Qed.
