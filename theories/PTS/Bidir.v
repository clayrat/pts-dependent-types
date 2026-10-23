(** * Bidirectional judgments of the annotated kernel

    [synth S Γ t A], written [S ;; Γ ⊢ t ⇑ A]: [t] synthesizes [A].
    [chk S Γ t A], written [S ;; Γ ⊢ t ⇓ A]: [t] checks against [A].

    These are the algorithmic rules the checker implements, and the
    reference for its soundness and completeness.  They are stricter than
    the declarative typing of PTS.Typing: a λ only checks, so a β-redex
    [(λ. b) u] needs an annotation on the λ; the family of an eliminator
    must synthesize; with the primitives switched off, no primitive
    former, constructor or eliminator is accepted.  A pair, like a λ, only
    checks, against a type unfolding to a Σ; a projection synthesizes
    from the Σ its argument synthesizes; a constant synthesizes the closed
    type the signature gives it, when the specification allows constants.  The declarative system types such terms without
    annotations; it is reached from this kernel by soundness, and from
    unannotated terms only after annotations are inserted.

    Unfolding a type to a sort or to a Π is reduction [⇝*]; comparing two
    types is conversion [≡].  An argument is checked against the domain
    before it is substituted into the codomain, and it is never reduced by
    the rules.

    Reduction and conversion are those of a signature [sg]: the judgments
    are [synth S sg Γ t A] and [chk S sg Γ t A].  In the sections below the
    notations [S ;; Γ ⊢ t ⇑ A] and [S ;; Γ ⊢ t ⇓ A] refer to the section's
    signature, and PTS.EmptySig gives them for the empty one.

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

From Stdlib Require Import List Bool Arith Relations.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Spec Signature Reduction NormalOrder.

Reserved Notation "S ;; G ⊢ t ⇑ A" (at level 70, G at next level, t at next level).
Reserved Notation "S ;; G ⊢ t ⇓ A" (at level 70, G at next level, t at next level).

Section Bidir.
  Variable S : spec.
  Variable sg : signature.
  Local Notation "t ⇝* u" := (red sg t u).
  Local Notation "t ≡ u" := (conv sg t u).

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
  (** dependent pairs *)
  | S_Sigma : forall G A B TA TB s1 s2 s3,
      synth G A TA -> TA ⇝* Srt s1 ->
      synth (A :: G) B TB -> TB ⇝* Srt s2 ->
      spec_sigma S s1 s2 = Some s3 ->
      synth G (Sigma A B) (Srt s3)
  | S_Fst : forall G p P A B,
      synth G p P -> P ⇝* Sigma A B ->
      synth G (Fst p) A
  | S_Snd : forall G p P A B,
      synth G p P -> P ⇝* Sigma A B ->
      synth G (Snd p) (subst1 B (Fst p))
  (** constants *)
  | S_Const : forall G g A,
      spec_decls S = true -> sig_type sg g = Some A ->
      synth G (Const g) A

  with chk : ctx -> term -> term -> Prop :=
  | C_Lam : forall G b T A B,
      T ⇝* Pi A B ->
      chk (A :: G) b B ->
      chk G (Lam b) T
  | C_Pair : forall G a b T A B,
      T ⇝* Sigma A B ->
      chk G a A ->
      chk G b (subst1 B a) ->
      chk G (Pair a b) T
  | C_Synth : forall G t A B,
      synth G t A ->
      A ≡ B ->
      chk G t B.

  Scheme synth_mut := Induction for synth Sort Prop
    with chk_mut := Induction for chk Sort Prop.
End Bidir.

Section Inputs.
  Variable S : spec.
  Variable sg : signature.
  Local Notation "t ⇝* u" := (red sg t u).
  Local Notation "S ;; G ⊢ t ⇑ A" := (synth S sg G t A).
  Local Notation "S ;; G ⊢ t ⇓ A" := (chk S sg G t A).

(** ** Admissible inputs *)

Inductive bwf_ctx : ctx -> Prop :=
| BW_Nil : bwf_ctx []
| BW_Cons : forall G A T s,
    bwf_ctx G ->
    S ;; G ⊢ A ⇑ T -> T ⇝* Srt s ->
    bwf_ctx (A :: G).

Definition btype (G : ctx) (A : term) : Prop :=
  (exists s, A = Srt s /\ spec_sort S s = true) \/
  (exists T s, S ;; G ⊢ A ⇑ T /\ T ⇝* Srt s).

(** ** The normalization premise of completeness *)

Definition normalizing_types : Prop :=
  forall G A, bwf_ctx G -> btype G A ->
    exists v, clos_refl_trans term (nstep sg) A v /\ nf sg v.

(** ** Extending the context from below

    A judgment about a term whose free variables point into the innermost
    part [D] of the context holds whatever lies below [D]: the rules look
    up only variables of the term.  In particular, a closed term typed in
    the empty context is typed in every context. *)

End Inputs.

Combined Scheme synth_chk_mut from synth_mut, chk_mut.

Section Weaken.
  Variable S : spec.
  Variable sg : signature.
  Local Notation "S ;; G ⊢ t ⇑ A" := (synth S sg G t A).
  Local Notation "S ;; G ⊢ t ⇓ A" := (chk S sg G t A).

Lemma lookup_app_lt : forall D G1 G2 n,
  n < length D -> lookup (D ++ G1) n = lookup (D ++ G2) n.
Proof. intros D G1 G2 n H. unfold lookup. now rewrite !nth_error_app1 by exact H. Qed.

Theorem bidir_weaken :
  (forall G t A, S ;; G ⊢ t ⇑ A -> forall D G1 G2, G = D ++ G1 ->
     closed_above (length D) t = true -> S ;; D ++ G2 ⊢ t ⇑ A) /\
  (forall G t A, S ;; G ⊢ t ⇓ A -> forall D G1 G2, G = D ++ G1 ->
     closed_above (length D) t = true -> S ;; D ++ G2 ⊢ t ⇓ A).
Proof.
  apply synth_chk_mut; intros; subst; cbn [closed_above] in *;
    repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [? ?] end;
    repeat match goal with
    | IH : forall D' G1' G2', ?Gx = D' ++ G1' -> _ -> _ |- _ =>
        first [ specialize (IH D G1 G2 eq_refl) | specialize (IH (_ :: D) G1 G2 eq_refl) ]
    end.
  (* variables: the lookup stays inside [D] *)
  all: try lazymatch goal with
       | H : lookup (?D ++ ?G1) ?n = Some _ |- synth _ _ (?D ++ ?G2) (Var ?n) _ =>
           constructor; rewrite <- (lookup_app_lt D G1 G2 n); [exact H | now apply Nat.ltb_lt]
       end.
  all: econstructor; eauto.
Qed.

Corollary synth_closed : forall G t A,
  S ;; [] ⊢ t ⇑ A -> closed t = true -> S ;; G ⊢ t ⇑ A.
Proof. intros G t A H Hc. exact (proj1 bidir_weaken _ _ _ H [] [] G eq_refl Hc). Qed.

Corollary chk_closed : forall G t A,
  S ;; [] ⊢ t ⇓ A -> closed t = true -> S ;; G ⊢ t ⇓ A.
Proof. intros G t A H Hc. exact (proj2 bidir_weaken _ _ _ H [] [] G eq_refl Hc). Qed.
End Weaken.

(** The lemmas take their signature implicitly: it is fixed by their
    statements. *)
Arguments bidir_weaken S {sg}.
Arguments synth_closed S {sg}.
Arguments chk_closed S {sg}.
