(** * Bidirectional judgments of the annotated kernel

    [synth S Γ t A], written [S ;; Γ ⊢ t ⇑ A]: [t] synthesizes [A].
    [chk S Γ t A], written [S ;; Γ ⊢ t ⇓ A]: [t] checks against [A].

    These are the algorithmic rules the checker implements, and the
    reference for its soundness and completeness.  They are stricter than
    the declarative typing of PTS.Typing: a λ only checks, so a β-redex
    [(λ. b) u] needs an annotation on the λ; the family of an eliminator
    must synthesize; with the primitives switched off, no primitive
    former, constructor or eliminator is accepted.  The declarative system types such terms without
    annotations; it is reached from this kernel by soundness, and from
    unannotated terms only after annotations are inserted.

    Unfolding a type to a sort or to a Π is reduction [⇝*]; comparing two
    types is conversion [≡].  An argument is checked against the domain
    before it is substituted into the codomain, and it is never reduced by
    the rules.

    ** Admissible inputs

    The rules do not check the context or the expected type, and on
    ill-formed ones they derive too much: [Γ ⊢ true ⇓ Ann Bool (Var 0)]
    holds in the empty context by erasing the annotation, although the
    expected type mentions an unbound variable.  The checker validates its
    inputs first, so its contracts are stated for
    - contexts [bwf_ctx S Γ], each entry synthesizing a sort;
    - expected types [btype S Γ A]: either a sort of the system, or a
      term synthesizing a type that unfolds to a sort.  "Has the type of
      some sort" would not do: the top sort △ of U⁻ has no type, yet
      [□ ⇓ △] holds and must be accepted.

    ** Contracts of the checker

    [synth] is a relation, not a function.  Unfolding by an arbitrary
    [⇝*] lets one term synthesize syntactically different types: the same
    application synthesizes [Ann (Srt Star) (Srt Star)] and [Srt Star]
    (see Tests.v).  The executable [infer] returns one of them, so its
    completeness holds up to conversion.

    Soundness: success of [infer] or [check] on admissible inputs yields
    the corresponding judgment.  It holds for every specification and any
    fuel.

    Completeness needs enough fuel, and the fuel is finite only when the
    compared types have normal forms.  λ∗ is not normalizing: typable
    terms without a normal form come from Girard's paradox, in the form
    of Hurkens, and the translation of Ω_ℕ, [L₀ ℕ (λx. x)] with the
    looping combinator of stage 4, is expected to be one.
    No such term is constructed yet, so this is the reason for the
    premise, not a result of the development.  The premise is explicit,
    [normalizing_types S], and the
    statements for [bwf_ctx S Γ] are
    - [Γ ⊢ t ⇑ A] implies that there is [n] such that for all [m ≥ n],
      [infer m Γ t] succeeds with some [A'] and [A' ≡ A];
    - [btype S Γ A] and [Γ ⊢ t ⇓ A] imply that there is [n] such that for
      all [m ≥ n], [check m Γ t A] succeeds.
    [normalizing_types] is an obligation for U⁻ and U (normalization of
    their type level) and for the predicative hierarchy (normalization of
    MLTT); it is not expected for λ∗.  Running out of fuel is a separate
    answer, neither success nor rejection.  Confluence, injectivity of Π
    and uniqueness of synthesized types up to conversion are further
    obligations behind completeness. *)

From Stdlib Require Import List.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Spec Reduction NormalOrder.

Reserved Notation "S ;; G ⊢ t ⇑ A" (at level 70, G at next level, t at next level).
Reserved Notation "S ;; G ⊢ t ⇓ A" (at level 70, G at next level, t at next level).

Section Bidir.
  Variable S : spec.

  Inductive synth : ctx -> term -> term -> Prop :=
  | S_Sort : forall G s s',
      spec_axiom S s = Some s' ->
      synth G (Srt s) (Srt s')
  | S_Var : forall G n A,
      lookup G n = Some A ->
      synth G (Var n) A
  | S_Pi : forall G A B TA TB s1 s2 s3,
      synth G A TA -> TA ⇝* Srt s1 ->
      synth (A :: G) B TB -> TB ⇝* Srt s2 ->
      spec_rule S s1 s2 = Some s3 ->
      synth G (Pi A B) (Srt s3)
  | S_App : forall G f u F A B,
      synth G f F -> F ⇝* Pi A B ->
      chk G u A ->
      synth G (App f u) (subst1 B u)
  | S_Ann : forall G t A T s,
      synth G A T -> T ⇝* Srt s ->
      chk G t A ->
      synth G (Ann t A) A
  (** MLTT primitives *)
  | S_Void : forall G s0,
      spec_prim S = Some s0 -> synth G Void (Srt s0)
  | S_Unit : forall G s0,
      spec_prim S = Some s0 -> synth G Unit (Srt s0)
  | S_Tt : forall G s0,
      spec_prim S = Some s0 -> synth G Tt Unit
  | S_Bool : forall G s0,
      spec_prim S = Some s0 -> synth G Bool (Srt s0)
  | S_True : forall G s0,
      spec_prim S = Some s0 -> synth G BTrue Bool
  | S_False : forall G s0,
      spec_prim S = Some s0 -> synth G BFalse Bool
  | S_ElimVoid : forall G C e TC D K s s0,
      spec_prim S = Some s0 ->
      synth G C TC -> TC ⇝* Pi D K -> D ≡ Void -> K ⇝* Srt s ->
      chk G e Void ->
      synth G (ElimVoid C e) (App C e)
  | S_ElimUnit : forall G C c u TC D K s s0,
      spec_prim S = Some s0 ->
      synth G C TC -> TC ⇝* Pi D K -> D ≡ Unit -> K ⇝* Srt s ->
      chk G c (App C Tt) ->
      chk G u Unit ->
      synth G (ElimUnit C c u) (App C u)
  | S_ElimBool : forall G C t f b TC D K s s0,
      spec_prim S = Some s0 ->
      synth G C TC -> TC ⇝* Pi D K -> D ≡ Bool -> K ⇝* Srt s ->
      chk G t (App C BTrue) ->
      chk G f (App C BFalse) ->
      chk G b Bool ->
      synth G (ElimBool C t f b) (App C b)

  with chk : ctx -> term -> term -> Prop :=
  | C_Lam : forall G b T A B,
      T ⇝* Pi A B ->
      chk (A :: G) b B ->
      chk G (Lam b) T
  | C_Synth : forall G t A B,
      synth G t A ->
      A ≡ B ->
      chk G t B.
End Bidir.

Notation "S ;; G ⊢ t ⇑ A" := (synth S G t A).
Notation "S ;; G ⊢ t ⇓ A" := (chk S G t A).

Scheme synth_mut := Induction for synth Sort Prop
  with chk_mut := Induction for chk Sort Prop.

(** ** Admissible inputs *)

Inductive bwf_ctx (S : spec) : ctx -> Prop :=
| BW_Nil : bwf_ctx S []
| BW_Cons : forall G A T s,
    bwf_ctx S G ->
    S ;; G ⊢ A ⇑ T -> T ⇝* Srt s ->
    bwf_ctx S (A :: G).

Definition btype (S : spec) (G : ctx) (A : term) : Prop :=
  (exists s, A = Srt s /\ spec_sort S s = true) \/
  (exists T s, S ;; G ⊢ A ⇑ T /\ T ⇝* Srt s).

(** ** The normalization premise of completeness *)

Definition normalizing_types (S : spec) : Prop :=
  forall G A, bwf_ctx S G -> btype S G A ->
    exists v, A ⇝ₙ* v /\ nf v.
