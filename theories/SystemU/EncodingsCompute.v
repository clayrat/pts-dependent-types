(** * The encodings compute on every numeral

    For every [k], by reduction ([⇝*], any strategy):
    - [succ cₖ ⇝* cₖ₊₁];
    - [pred cₖ₊₁ ⇝* cₖ] and [pred c₀ ⇝* c₀];
    - [is_zero c₀ ≡ true] and [is_zero cₖ₊₁ ≡ false],
    where [cₖ] on the left is the annotated numeral of a PCF literal and on
    the right its normal form [λX f x. fᵏ x].  This is [encodings_compute]
    of Contracts.v.

    The proofs follow the terms.  A numeral applied to [T F X] unfolds to
    [Fᵏ X] ([numeral_iterates]).  [succ] applies the numeral to its own
    [X f x].  [pred] iterates [shift] from the pair [(0, 0)]; by induction
    the [k]-th iterate reduces to the normal pair [(cₖ₋₁, cₖ)].  The strict
    test applies each inner boolean to [false false], and both of its
    branches give [false].

    Each compound encoding is described by its form in terms of the
    [church] terms of its parts, checked by computation; substitutions in
    β-steps leave closed parts and closed arguments alone ([subst_closed],
    [lift_closed]). *)

From Stdlib Require Import String List Relations Bool Arith Lia.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Reduction.
From DepTypes.SystemU Require Import Looping Encodings.

Open Scope string_scope.
Open Scope nterm_scope.

(** ** Forms of the encodings *)

Lemma church_czero : church czero = Ann (church_nf 0) (church CNat).
Proof. reflexivity. Qed.

Lemma church_ctrue : church ctrue = Ann (Lam (Lam (Lam (Var 1)))) (church CBool).
Proof. reflexivity. Qed.

Lemma church_cfalse : church cfalse = Ann (Lam (Lam (Lam (Var 0)))) (church CBool).
Proof. reflexivity. Qed.

Lemma church_csucc : church csucc =
  Ann (Lam (Lam (Lam (Lam (App (Var 1) (App (App (App (Var 3) (Var 2)) (Var 1)) (Var 0)))))))
      (church (CNat ~> CNat)).
Proof. vm_compute. reflexivity. Qed.

Lemma church_cpair : church cpair =
  Ann (Lam (Lam (Lam (Lam (App (App (Var 0) (Var 3)) (Var 2))))))
      (church (CNat ~> CNat ~> CPair)).
Proof. vm_compute. reflexivity. Qed.

Lemma church_cfst : church cfst =
  Ann (Lam (App (App (Var 0) (church CNat)) (Lam (Lam (Var 1))))) (church (CPair ~> CNat)).
Proof. vm_compute. reflexivity. Qed.

Lemma church_csnd : church csnd =
  Ann (Lam (App (App (Var 0) (church CNat)) (Lam (Lam (Var 0))))) (church (CPair ~> CNat)).
Proof. vm_compute. reflexivity. Qed.

Lemma church_cshift : church cshift =
  Ann (Lam (App (App (church cpair) (App (church csnd) (Var 0)))
                (App (church csucc) (App (church csnd) (Var 0)))))
      (church (CPair ~> CPair)).
Proof. vm_compute. reflexivity. Qed.

Definition pair_init : term := App (App (church cpair) (church czero)) (church czero).

Lemma church_cpred : church cpred =
  Ann (Lam (App (church cfst)
                (App (App (App (Var 0) (church CPair)) (church cshift)) pair_init)))
      (church (CNat ~> CNat)).
Proof. vm_compute. reflexivity. Qed.

(** The step of the strict test. *)
Definition strict_step : term :=
  Lam (App (App (App (Var 0) (church CBool)) (church cfalse)) (church cfalse)).

Lemma church_is_zero : church is_zero =
  Ann (Lam (App (App (App (Var 0) (church CBool)) strict_step) (church ctrue)))
      (church (CNat ~> CBool)).
Proof. vm_compute. reflexivity. Qed.

(** ** Closed terms *)

Ltac closed_by_computation := vm_compute; reflexivity.

Lemma closed_app : forall a b, closed a = true -> closed b = true -> closed (App a b) = true.
Proof. intros a b Ha Hb. unfold closed in *. cbn. now rewrite Ha, Hb. Qed.

Lemma closed_iterv : forall k, closed_above 2 (iterv k) = true.
Proof. induction k as [|k IH]; [reflexivity | ]. cbn. exact IH. Qed.

Lemma closed_church_nf : forall k, closed (church_nf k) = true.
Proof. intros k. unfold closed, church_nf. cbn. apply (closed_above_mono _ 2); [apply closed_iterv | lia]. Qed.

Lemma closed_numeral : forall k, closed (church (numeral k)) = true.
Proof.
  intros k. rewrite church_numeral. unfold closed. cbn.
  rewrite (closed_above_mono _ 2 3 (closed_iterv k)) by lia. reflexivity.
Qed.

(** ** One β-step through an annotation *)

Lemma beta_ann : forall b T u, App (Ann (Lam b) T) u ⇝* subst1 b u.
Proof. intros b T u. eapply rt_trans; [apply rt_step, R_AppFun, R_Ann | apply rt_step, R_Beta]. Qed.

Lemma beta : forall b u, App (Lam b) u ⇝* subst1 b u.
Proof. intros b u. apply rt_step, R_Beta. Qed.

Lemma ann_erase : forall t A, Ann t A ⇝* t.
Proof. intros t A. apply rt_step, R_Ann. Qed.

Lemma subst_iter : forall sb k a b,
  subst sb (Nat.iter k (App a) b) = Nat.iter k (App (subst sb a)) (subst sb b).
Proof.
  intros sb k a b. induction k as [|k IH]; [reflexivity | ].
  change (Nat.iter (S k) (App a) b) with (App a (Nat.iter k (App a) b)).
  cbn [subst]. rewrite IH. reflexivity.
Qed.

(** ** A numeral applied to [T F X] *)

Theorem numeral_iterates : forall k T F X,
  App (App (App (church_nf k) T) F) X ⇝* Nat.iter k (App (subst1 (lift 1 F) X)) X.
Proof.
  intros k T F X. unfold church_nf.
  eapply rt_trans; [apply red_app; [apply red_app; [apply beta | apply rt_refl] | apply rt_refl] | ].
  rewrite (subst1_closed (Lam (Lam (iterv k)))) by
    (unfold closed; cbn; apply closed_iterv).
  eapply rt_trans; [apply red_app; [apply beta | apply rt_refl] | ].
  unfold subst1 at 1. cbn [subst]. unfold iterv. rewrite subst_iter. cbn [subst up_sub scons].
  eapply rt_trans; [apply beta | ].
  unfold subst1. rewrite subst_iter. apply rt_refl.
Qed.

Corollary numeral_iterates_closed : forall k T F X, closed F = true ->
  App (App (App (church_nf k) T) F) X ⇝* Nat.iter k (App F) X.
Proof.
  intros k T F X HF. rewrite <- (subst1_closed F X HF) at 2.
  rewrite <- (lift_closed 1 F HF) at 2. apply numeral_iterates.
Qed.

(** ** Substitution into the forms

    After a β-step, [clean] removes the substitutions and lifts left on
    closed arguments and on the closed [church] parts. *)

Ltac clean_with H :=
  repeat first
    [ rewrite (subst_closed _ _ H)
    | rewrite (rename_closed_above _ 0 _ H) by (intros; lia) ].

Ltac clean_church :=
  repeat match goal with
  | |- context [subst ?sb (church ?c)] =>
      rewrite (subst_closed sb (church c)) by closed_by_computation
  end.

Ltac simpl_subst := unfold subst1; cbn [subst up_sub scons lift rename up_ren Nat.add]; clean_church.

Lemma closed_ttnf : closed (Lam (Lam (Lam (Var 1)))) = true. Proof. reflexivity. Qed.
Lemma closed_ffnf : closed (Lam (Lam (Lam (Var 0)))) = true. Proof. reflexivity. Qed.

(** ** succ *)

Theorem succ_reduces : forall M j, closed M = true -> M ⇝* church_nf j ->
  App (church csucc) M ⇝* church_nf (S j).
Proof.
  intros M j HM HMj. rewrite church_csucc.
  eapply rt_trans; [apply beta_ann | ]. simpl_subst. clean_with HM.
  change (church_nf (S j)) with (Lam (Lam (Lam (App (Var 1) (iterv j))))).
  apply red_lam, red_lam, red_lam, red_app; [apply rt_refl | ].
  eapply rt_trans.
  { apply red_app; [apply red_app; [apply red_app; [exact HMj | apply rt_refl] | apply rt_refl] | apply rt_refl]. }
  apply numeral_iterates.
Qed.

(** ** Pairs *)

Definition pairnf (a b : term) : term := Lam (Lam (App (App (Var 0) a) b)).

Lemma closed_pairnf : forall a b, closed a = true -> closed b = true -> closed (pairnf a b) = true.
Proof.
  intros a b Ha Hb. unfold closed, pairnf in *. cbn.
  rewrite (closed_above_mono a 0 2 Ha), (closed_above_mono b 0 2 Hb) by lia. reflexivity.
Qed.

Lemma pair_reduces : forall a b, closed a = true -> closed b = true ->
  App (App (church cpair) a) b ⇝* pairnf a b.
Proof.
  intros a b Ha Hb. rewrite church_cpair.
  eapply rt_trans; [apply red_app; [apply beta_ann | apply rt_refl] | ]. simpl_subst. clean_with Ha.
  eapply rt_trans; [apply beta | ]. simpl_subst. clean_with Ha. clean_with Hb. apply rt_refl.
Qed.

Lemma fst_reduces : forall a b, closed a = true -> closed b = true ->
  App (church cfst) (pairnf a b) ⇝* a.
Proof.
  intros a b Ha Hb. rewrite church_cfst.
  eapply rt_trans; [apply beta_ann | ]. simpl_subst.
  unfold pairnf at 1.
  eapply rt_trans; [apply red_app; [apply beta | apply rt_refl] | ]. simpl_subst.
  clean_with Ha. clean_with Hb.
  eapply rt_trans; [apply beta | ]. simpl_subst. clean_with Ha. clean_with Hb.
  eapply rt_trans; [apply red_app; [apply beta | apply rt_refl] | ]. simpl_subst. clean_with Ha.
  eapply rt_trans; [apply beta | ]. simpl_subst. clean_with Ha. apply rt_refl.
Qed.

Lemma snd_reduces : forall a b, closed a = true -> closed b = true ->
  App (church csnd) (pairnf a b) ⇝* b.
Proof.
  intros a b Ha Hb. rewrite church_csnd.
  eapply rt_trans; [apply beta_ann | ]. simpl_subst.
  unfold pairnf at 1.
  eapply rt_trans; [apply red_app; [apply beta | apply rt_refl] | ]. simpl_subst.
  clean_with Ha. clean_with Hb.
  eapply rt_trans; [apply beta | ]. simpl_subst. clean_with Ha. clean_with Hb.
  eapply rt_trans; [apply red_app; [apply beta | apply rt_refl] | ]. simpl_subst.
  eapply rt_trans; [apply beta | ]. simpl_subst. apply rt_refl.
Qed.

(** ** pred: iterating shift from (0, 0) *)

Lemma shift_reduces : forall P i j, closed P = true -> P ⇝* pairnf (church_nf i) (church_nf j) ->
  App (church cshift) P ⇝* pairnf (church_nf j) (church_nf (S j)).
Proof.
  intros P i j HP HPij. rewrite church_cshift.
  eapply rt_trans; [apply beta_ann | ]. simpl_subst.
  assert (Hs : App (church csnd) P ⇝* church_nf j).
  { eapply rt_trans; [apply red_app; [apply rt_refl | exact HPij] | ].
    apply snd_reduces; apply closed_church_nf. }
  assert (HsP : closed (App (church csnd) P) = true)
    by (apply closed_app; [closed_by_computation | exact HP]).
  eapply rt_trans.
  { apply red_app; [apply red_app; [apply rt_refl | exact Hs] | ].
    apply (succ_reduces _ j HsP Hs). }
  apply pair_reduces; apply closed_church_nf.
Qed.

Lemma closed_church_czero : closed (church czero) = true.
Proof. reflexivity. Qed.

Lemma closed_iter_shift : forall k, closed (Nat.iter k (App (church cshift)) pair_init) = true.
Proof.
  induction k as [|k IH]; [closed_by_computation | ].
  change (closed (App (church cshift) (Nat.iter k (App (church cshift)) pair_init)) = true).
  apply closed_app; [closed_by_computation | exact IH].
Qed.

Lemma iterate_shift : forall k,
  Nat.iter k (App (church cshift)) pair_init ⇝* pairnf (church_nf (Nat.pred k)) (church_nf k).
Proof.
  induction k as [|k IH].
  - unfold pair_init. rewrite church_czero.
    eapply rt_trans; [apply red_app; [apply red_app; [apply rt_refl | apply ann_erase] | apply ann_erase] | ].
    apply pair_reduces; apply closed_church_nf.
  - change (Nat.iter (S k) (App (church cshift)) pair_init)
      with (App (church cshift) (Nat.iter k (App (church cshift)) pair_init)).
    exact (shift_reduces _ _ _ (closed_iter_shift k) IH).
Qed.

Theorem pred_reduces : forall N k, closed N = true -> N ⇝* church_nf k ->
  App (church cpred) N ⇝* church_nf (Nat.pred k).
Proof.
  intros N k HN HNk. rewrite church_cpred.
  eapply rt_trans; [apply beta_ann | ]. simpl_subst. clean_with HN.
  rewrite (subst_closed _ pair_init) by closed_by_computation.
  eapply rt_trans.
  { apply red_app; [apply rt_refl | ].
    eapply rt_trans.
    { apply red_app; [apply red_app; [apply red_app; [exact HNk | apply rt_refl] | apply rt_refl]
                     | apply rt_refl]. }
    eapply rt_trans; [apply numeral_iterates_closed; closed_by_computation | ].
    apply iterate_shift. }
  apply fst_reduces; apply closed_church_nf.
Qed.

(** ** The strict test *)

Definition ttnf : term := Lam (Lam (Lam (Var 1))).
Definition ffnf : term := Lam (Lam (Lam (Var 0))).

Lemma select_true : forall T a b, closed a = true -> closed b = true ->
  App (App (App ttnf T) a) b ⇝* a.
Proof.
  intros T a b Ha Hb. unfold ttnf.
  eapply rt_trans; [apply red_app; [apply red_app; [apply beta | apply rt_refl] | apply rt_refl] | ].
  simpl_subst.
  eapply rt_trans; [apply red_app; [apply beta | apply rt_refl] | ]. simpl_subst. clean_with Ha.
  eapply rt_trans; [apply beta | ]. simpl_subst. clean_with Ha. apply rt_refl.
Qed.

Lemma select_false : forall T a b, App (App (App ffnf T) a) b ⇝* b.
Proof.
  intros T a b. unfold ffnf.
  eapply rt_trans; [apply red_app; [apply red_app; [apply beta | apply rt_refl] | apply rt_refl] | ].
  simpl_subst.
  eapply rt_trans; [apply red_app; [apply beta | apply rt_refl] | ]. simpl_subst.
  eapply rt_trans; [apply beta | ]. simpl_subst. apply rt_refl.
Qed.

Lemma closed_iter_step : forall k, closed (Nat.iter k (App strict_step) (church ctrue)) = true.
Proof.
  induction k as [|k IH]; [closed_by_computation | ].
  change (closed (App strict_step (Nat.iter k (App strict_step) (church ctrue))) = true).
  apply closed_app; [closed_by_computation | exact IH].
Qed.

(** The [k]-th iterate of the strict step from [true]: [true] for [k = 0],
    [false] after. *)
Lemma iterate_step : forall k,
  Nat.iter k (App strict_step) (church ctrue) ⇝* match k with 0 => ttnf | S _ => ffnf end.
Proof.
  induction k as [|k IH].
  - rewrite church_ctrue. apply ann_erase.
  - change (Nat.iter (S k) (App strict_step) (church ctrue))
      with (App strict_step (Nat.iter k (App strict_step) (church ctrue))).
    unfold strict_step at 1. eapply rt_trans; [apply beta | ]. simpl_subst.
    eapply rt_trans.
    { apply red_app; [apply red_app; [apply red_app; [exact IH | apply rt_refl] | apply rt_refl]
                     | apply rt_refl]. }
    apply rt_trans with (church cfalse).
    + destruct k as [|k]; [apply select_true; closed_by_computation | apply select_false].
    + rewrite church_cfalse. apply ann_erase.
Qed.

Theorem is_zero_reduces : forall N k, closed N = true -> N ⇝* church_nf k ->
  App (church is_zero) N ⇝* match k with 0 => ttnf | S _ => ffnf end.
Proof.
  intros N k HN HNk. rewrite church_is_zero.
  eapply rt_trans; [apply beta_ann | ]. simpl_subst. clean_with HN.
  rewrite (subst_closed _ strict_step) by closed_by_computation.
  eapply rt_trans.
  { apply red_app; [apply red_app; [apply red_app; [exact HNk | apply rt_refl] | apply rt_refl]
                   | apply rt_refl]. }
  eapply rt_trans; [apply numeral_iterates_closed; closed_by_computation | ].
  apply iterate_step.
Qed.

(** ** The contract *)

Lemma numeral_reduces : forall k, church (numeral k) ⇝* church_nf k.
Proof. intros k. rewrite church_numeral. apply ann_erase. Qed.

Theorem encodings_compute_proved : forall k,
  App (church csucc) (church (numeral k)) ⇝* church_nf (S k) /\
  App (church cpred) (church (numeral (S k))) ⇝* church_nf k /\
  App (church cpred) (church czero) ⇝* church_nf 0 /\
  App (church is_zero) (church (numeral 0)) ≡ church ctrue /\
  App (church is_zero) (church (numeral (S k))) ≡ church cfalse.
Proof.
  intros k. repeat split.
  - apply succ_reduces; [apply closed_numeral | apply numeral_reduces].
  - apply (pred_reduces _ (S k)); [apply closed_numeral | apply numeral_reduces].
  - apply (pred_reduces _ 0); [reflexivity | rewrite church_czero; apply ann_erase].
  - apply conv_trans with ttnf.
    + apply red_conv, (is_zero_reduces _ 0); [apply closed_numeral | apply numeral_reduces].
    + apply conv_sym, red_conv. rewrite church_ctrue. apply ann_erase.
  - apply conv_trans with ffnf.
    + apply red_conv, (is_zero_reduces _ (S k)); [apply closed_numeral | apply numeral_reduces].
    + apply conv_sym, red_conv. rewrite church_cfalse. apply ann_erase.
Qed.
