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

(** ** Congruence of reduction and conversion *)

(** One-step congruence in a position lifts to multi-step reduction. *)
Lemma red_ctx : forall (C : term -> term),
    (forall a b, a ⇝ b -> C a ⇝ C b) -> forall a b, a ⇝* b -> C a ⇝* C b.
Proof.
  intros C HC a b H. induction H.
  - apply rt_step, HC, H.
  - apply rt_refl.
  - eapply rt_trans; eassumption.
Qed.

Lemma conv_app_arg : forall f a b, a ≡ b -> App f a ≡ App f b.
Proof.
  intros f a b H. induction H.
  - apply rst_step, R_AppArg, H.
  - apply rst_refl.
  - now apply rst_sym.
  - eapply rst_trans; eassumption.
Qed.

(** ** Erasure of annotations

    [erase_ann t] removes every annotation [(u : A)], keeping [u].  Since
    erasing an annotation is a reduction step, every term reduces to its
    erasure: terms with equal erasures are convertible.  The erasure of a
    term is its domain-free version, as in Geuvers–Verkoelen §4.2. *)

Fixpoint erase_ann (t : term) : term :=
  match t with
  | Srt s => Srt s
  | Var n => Var n
  | Pi A B => Pi (erase_ann A) (erase_ann B)
  | Lam b => Lam (erase_ann b)
  | App f a => App (erase_ann f) (erase_ann a)
  | Ann u _ => erase_ann u
  | Void => Void
  | ElimVoid C e => ElimVoid (erase_ann C) (erase_ann e)
  | Unit => Unit
  | Tt => Tt
  | ElimUnit C c u => ElimUnit (erase_ann C) (erase_ann c) (erase_ann u)
  | Bool => Bool
  | BTrue => BTrue
  | BFalse => BFalse
  | ElimBool C t f b =>
      ElimBool (erase_ann C) (erase_ann t) (erase_ann f) (erase_ann b)
  end.

(** Multi-step congruences, one per former with subterms. *)

Ltac red_cong C H :=
  eapply rt_trans;
  [ apply (red_ctx C); [intros ? ? ?; constructor; assumption | exact H] | cbv beta ].

Lemma red_pi : forall A A' B B', A ⇝* A' -> B ⇝* B' -> Pi A B ⇝* Pi A' B'.
Proof.
  intros A A' B B' HA HB.
  red_cong (fun a => Pi a B) HA. red_cong (fun b => Pi A' b) HB. apply rt_refl.
Qed.

Lemma red_lam : forall b b', b ⇝* b' -> Lam b ⇝* Lam b'.
Proof. intros b b' H. red_cong Lam H. apply rt_refl. Qed.

Lemma red_app : forall f f' a a', f ⇝* f' -> a ⇝* a' -> App f a ⇝* App f' a'.
Proof.
  intros f f' a a' Hf Ha.
  red_cong (fun x => App x a) Hf. red_cong (fun x => App f' x) Ha. apply rt_refl.
Qed.

Lemma red_elim_void : forall C C' e e', C ⇝* C' -> e ⇝* e' -> ElimVoid C e ⇝* ElimVoid C' e'.
Proof.
  intros C C' e e' HC He.
  red_cong (fun x => ElimVoid x e) HC. red_cong (fun x => ElimVoid C' x) He. apply rt_refl.
Qed.

Lemma red_elim_unit : forall C C' c c' u u',
    C ⇝* C' -> c ⇝* c' -> u ⇝* u' -> ElimUnit C c u ⇝* ElimUnit C' c' u'.
Proof.
  intros C C' c c' u u' HC Hc Hu.
  red_cong (fun x => ElimUnit x c u) HC. red_cong (fun x => ElimUnit C' x u) Hc.
  red_cong (fun x => ElimUnit C' c' x) Hu. apply rt_refl.
Qed.

Lemma red_elim_bool : forall C C' t t' f f' b b',
    C ⇝* C' -> t ⇝* t' -> f ⇝* f' -> b ⇝* b' -> ElimBool C t f b ⇝* ElimBool C' t' f' b'.
Proof.
  intros C C' t t' f f' b b' HC Ht Hf Hb.
  red_cong (fun x => ElimBool x t f b) HC. red_cong (fun x => ElimBool C' x f b) Ht.
  red_cong (fun x => ElimBool C' t' x b) Hf. red_cong (fun x => ElimBool C' t' f' x) Hb.
  apply rt_refl.
Qed.

Lemma red_erase : forall t, t ⇝* erase_ann t.
Proof.
  induction t; cbn [erase_ann]; try apply rt_refl.
  all: first
    [ eapply rt_trans; [apply rt_step, R_Ann | assumption]
    | auto using red_pi, red_lam, red_app, red_elim_void, red_elim_unit, red_elim_bool ].
Qed.

Lemma erase_conv : forall t u, erase_ann t = erase_ann u -> t ≡ u.
Proof.
  intros t u H. apply conv_trans with (erase_ann t).
  - apply red_conv, red_erase.
  - rewrite H. apply conv_sym, red_conv, red_erase.
Qed.

(** ** Normal forms

    A term without a one-step reduct. *)

Definition normal (t : term) : Prop := forall u, ~ (t ⇝ u).
