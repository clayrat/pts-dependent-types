(** * Correctness of substitution

    The laws of parallel renaming and substitution on de Bruijn terms:
    extensionality, the identity, the four fusion laws, and their
    consequences for single substitution — [subst1 (lift 1 t) u = t], and
    [subst sb (subst1 b u) = subst1 (subst (up_sub sb) b) (subst sb u)].
    With them, one-step reduction, multi-step reduction and conversion are
    stable under substitution and renaming, and reducing the argument of a
    substitution reduces the result.

    These are the syntactic half of the correctness of substitution.  The
    typing half — weakening and the substitution lemma of the declarative
    rules — is stated in Contracts.v as an open obligation. *)

From Stdlib Require Import Relations Arith Lia.
From DepTypes.PTS Require Import Syntax Reduction.

Implicit Types (r : nat -> nat) (sb : nat -> term) (t u b : term).

(** ** Extensionality *)

Lemma up_ren_ext : forall r r', (forall n, r n = r' n) -> forall n, up_ren r n = up_ren r' n.
Proof. intros r r' H [|n]; cbn; congruence. Qed.

Lemma rename_ext : forall t r r', (forall n, r n = r' n) -> rename r t = rename r' t.
Proof.
  induction t; intros r r' H; cbn; f_equal; eauto using up_ren_ext; reflexivity.
Qed.

Lemma up_sub_ext : forall sb sb', (forall n, sb n = sb' n) -> forall n, up_sub sb n = up_sub sb' n.
Proof. intros sb sb' H [|n]; cbn; [reflexivity | now rewrite H]. Qed.

Lemma subst_ext : forall t sb sb', (forall n, sb n = sb' n) -> subst sb t = subst sb' t.
Proof.
  induction t; intros sb sb' H; cbn; f_equal; eauto using up_sub_ext; reflexivity.
Qed.

(** ** Identity and fusion *)

Lemma subst_var : forall t, subst Var t = t.
Proof.
  induction t; cbn; f_equal; try assumption; try reflexivity.
  all: match goal with
       | |- subst ?sb ?t = ?t => rewrite (subst_ext t sb Var); [assumption | intros [|n]; reflexivity]
       end.
Qed.

Lemma rename_rename : forall t r r', rename r (rename r' t) = rename (fun n => r (r' n)) t.
Proof.
  induction t; intros r r'; cbn; f_equal; try apply IHt1; try apply IHt2; try apply IHt3;
    try apply IHt4; try apply IHt; try reflexivity.
  all: rewrite ?IHt2, ?IHt; apply rename_ext; intros [|n]; reflexivity.
Qed.

Lemma rename_subst : forall t r sb,
  rename r (subst sb t) = subst (fun n => rename r (sb n)) t.
Proof.
  induction t; intros r sb; cbn; f_equal; try apply IHt1; try apply IHt2; try apply IHt3;
    try apply IHt4; try apply IHt; try reflexivity.
  all: rewrite ?IHt2, ?IHt; apply subst_ext; intros [|n]; [reflexivity | ].
  all: cbn; unfold lift; rewrite !rename_rename; apply rename_ext; reflexivity.
Qed.

Lemma subst_rename : forall t sb r,
  subst sb (rename r t) = subst (fun n => sb (r n)) t.
Proof.
  induction t; intros sb r; cbn; f_equal; try apply IHt1; try apply IHt2; try apply IHt3;
    try apply IHt4; try apply IHt; try reflexivity.
  all: rewrite ?IHt2, ?IHt; apply subst_ext; intros [|n]; reflexivity.
Qed.

Lemma subst_subst : forall t sb sb',
  subst sb (subst sb' t) = subst (fun n => subst sb (sb' n)) t.
Proof.
  induction t; intros sb sb'; cbn; f_equal; try apply IHt1; try apply IHt2; try apply IHt3;
    try apply IHt4; try apply IHt; try reflexivity.
  all: rewrite ?IHt2, ?IHt; apply subst_ext; intros [|n]; [reflexivity | ].
  all: cbn; unfold lift; rewrite subst_rename, rename_subst; apply subst_ext; reflexivity.
Qed.

(** A renaming is a substitution by variables. *)
Lemma rename_as_subst : forall t r, rename r t = subst (fun n => Var (r n)) t.
Proof.
  intros t r. rewrite <- (subst_var (rename r t)), subst_rename. reflexivity.
Qed.

(** ** Single substitution *)

Theorem subst1_lift : forall t u, subst1 (lift 1 t) u = t.
Proof.
  intros t u. unfold subst1, lift. rewrite subst_rename.
  rewrite <- (subst_var t) at 2. apply subst_ext. reflexivity.
Qed.

Theorem subst_subst1 : forall sb b u,
  subst sb (subst1 b u) = subst1 (subst (up_sub sb) b) (subst sb u).
Proof.
  intros sb b u. unfold subst1. rewrite !subst_subst. apply subst_ext. intros [|n]; [reflexivity | ].
  cbn. unfold lift. rewrite subst_rename. rewrite <- (subst_var (sb n)) at 1.
  apply subst_ext. reflexivity.
Qed.

Theorem rename_subst1 : forall r b u,
  rename r (subst1 b u) = subst1 (rename (up_ren r) b) (rename r u).
Proof.
  intros r b u. unfold subst1. rewrite rename_subst, subst_rename.
  apply subst_ext. intros [|n]; reflexivity.
Qed.

(** ** Reduction and conversion under substitution *)

Theorem red1_subst : forall t u, t ⇝ u -> forall sb, subst sb t ⇝ subst sb u.
Proof.
  intros t u H. induction H; intros sb; cbn; try (constructor; auto).
  rewrite subst_subst1. constructor.
Qed.

Corollary red1_rename : forall t u r, t ⇝ u -> rename r t ⇝ rename r u.
Proof. intros t u r H. rewrite !rename_as_subst. now apply red1_subst. Qed.

Corollary red_subst : forall sb t u, t ⇝* u -> subst sb t ⇝* subst sb u.
Proof.
  intros sb t u H. induction H.
  - apply rt_step, red1_subst, H.
  - apply rt_refl.
  - eapply rt_trans; eassumption.
Qed.

Corollary conv_subst : forall sb t u, t ≡ u -> subst sb t ≡ subst sb u.
Proof.
  intros sb t u H. induction H.
  - apply rst_step, red1_subst, H.
  - apply rst_refl.
  - now apply rst_sym.
  - eapply rst_trans; eassumption.
Qed.

Corollary conv_rename : forall r t u, t ≡ u -> rename r t ≡ rename r u.
Proof. intros r t u H. rewrite !rename_as_subst. now apply conv_subst. Qed.

Lemma red_ann : forall t t' A A', t ⇝* t' -> A ⇝* A' -> Ann t A ⇝* Ann t' A'.
Proof.
  intros t t' A A' Ht HA.
  eapply rt_trans; [apply (red_ctx (fun x => Ann x A)); [intros; constructor; assumption | exact Ht] | ].
  apply (red_ctx (fun x => Ann t' x)); [intros; constructor; assumption | exact HA].
Qed.

(** Reducing the substituted terms reduces the result. *)
Lemma red_rename : forall r t u, t ⇝* u -> rename r t ⇝* rename r u.
Proof.
  intros r t u H. induction H.
  - apply rt_step, red1_rename, H.
  - apply rt_refl.
  - eapply rt_trans; eassumption.
Qed.

Theorem red_subst_pointwise : forall t sb sb', (forall n, sb n ⇝* sb' n) ->
  subst sb t ⇝* subst sb' t.
Proof.
  induction t; intros sb sb' H; cbn; try apply rt_refl; try apply H.
  all: assert (Hup : forall n, up_sub sb n ⇝* up_sub sb' n)
         by (intros [|n]; cbn; [apply rt_refl | apply red_rename, H]).
  all: try (apply red_elim_bool; eauto).
  all: eauto using red_pi, red_lam, red_app, red_ann, red_elim_void, red_elim_unit, rt_refl.
Qed.

Corollary red_subst1_arg : forall b u u', u ⇝* u' -> subst1 b u ⇝* subst1 b u'.
Proof.
  intros b u u' H. apply red_subst_pointwise. intros [|n]; [exact H | apply rt_refl].
Qed.
