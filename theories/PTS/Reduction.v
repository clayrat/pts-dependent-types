(** * Reduction and conversion

    The contract of conversion for the first kernel: the congruence closure
    of
    - β: [(λ. b) u ⇝ b[u/0]];
    - erasure of annotations: [(t : A) ⇝ t];
    - ι: the computation rules of the eliminators on constructors.

    There is no η, neither for Π nor for the base types: with [f] a
    variable of function type, [λx. f x] and [f] are not convertible.

    Conversion [conv] is the reflexive, symmetric and transitive closure of
    one-step reduction [red1].  The executable conversion of the checker
    will be proved sound against it.

    [red1] contracts any redex, so it is a conversion relation, not an
    evaluation strategy; the evaluator follows normal order, PTS.NormalOrder. *)

From Stdlib Require Import Relations.
From DepTypes.PTS Require Import Syntax.

Reserved Notation "t ⇝ u" (at level 70, no associativity).

Inductive red1 : term -> term -> Prop :=
(** contractions *)
| R_Beta : forall b u, App (Lam b) u ⇝ subst1 b u
| R_Ann : forall t A, Ann t A ⇝ t
| R_UnitTt : forall C c, ElimUnit C c Tt ⇝ c
| R_BoolTrue : forall C t f, ElimBool C t f BTrue ⇝ t
| R_BoolFalse : forall C t f, ElimBool C t f BFalse ⇝ f
(** congruences *)
| R_PiDom : forall A A' B, A ⇝ A' -> Pi A B ⇝ Pi A' B
| R_PiCod : forall A B B', B ⇝ B' -> Pi A B ⇝ Pi A B'
| R_Lam : forall b b', b ⇝ b' -> Lam b ⇝ Lam b'
| R_AppFun : forall f f' a, f ⇝ f' -> App f a ⇝ App f' a
| R_AppArg : forall f a a', a ⇝ a' -> App f a ⇝ App f a'
| R_AnnTerm : forall t t' A, t ⇝ t' -> Ann t A ⇝ Ann t' A
| R_AnnType : forall t A A', A ⇝ A' -> Ann t A ⇝ Ann t A'
| R_ElimVoid1 : forall C C' e, C ⇝ C' -> ElimVoid C e ⇝ ElimVoid C' e
| R_ElimVoid2 : forall C e e', e ⇝ e' -> ElimVoid C e ⇝ ElimVoid C e'
| R_ElimUnit1 : forall C C' c u, C ⇝ C' -> ElimUnit C c u ⇝ ElimUnit C' c u
| R_ElimUnit2 : forall C c c' u, c ⇝ c' -> ElimUnit C c u ⇝ ElimUnit C c' u
| R_ElimUnit3 : forall C c u u', u ⇝ u' -> ElimUnit C c u ⇝ ElimUnit C c u'
| R_ElimBool1 : forall C C' t f b, C ⇝ C' -> ElimBool C t f b ⇝ ElimBool C' t f b
| R_ElimBool2 : forall C t t' f b, t ⇝ t' -> ElimBool C t f b ⇝ ElimBool C t' f b
| R_ElimBool3 : forall C t f f' b, f ⇝ f' -> ElimBool C t f b ⇝ ElimBool C t f' b
| R_ElimBool4 : forall C t f b b', b ⇝ b' -> ElimBool C t f b ⇝ ElimBool C t f b'
where "t ⇝ u" := (red1 t u).

(** Multi-step reduction. *)
Definition red : term -> term -> Prop := clos_refl_trans term red1.

Notation "t ⇝* u" := (red t u) (at level 70, no associativity).

(** Conversion. *)
Definition conv : term -> term -> Prop := clos_refl_sym_trans term red1.

Notation "t ≡ u" := (conv t u) (at level 70, no associativity).

Lemma conv_refl : forall t, t ≡ t.
Proof. intros t. apply rst_refl. Qed.

Lemma conv_sym : forall t u, t ≡ u -> u ≡ t.
Proof. intros t u H. now apply rst_sym. Qed.

Lemma conv_trans : forall t u v, t ≡ u -> u ≡ v -> t ≡ v.
Proof. intros t u v H1 H2. eapply rst_trans; eassumption. Qed.

Lemma red_conv : forall t u, t ⇝* u -> t ≡ u.
Proof.
  intros t u H. induction H.
  - now apply rst_step.
  - apply rst_refl.
  - eapply rst_trans; eassumption.
Qed.

(** ** Normal forms

    A term without a one-step reduct. *)

Definition normal (t : term) : Prop := forall u, ~ (t ⇝ u).
