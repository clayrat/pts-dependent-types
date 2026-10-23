(** * Correctness of substitution

    The laws of parallel renaming and substitution on de Bruijn terms:
    extensionality, the identity, the four fusion laws, and their
    consequences for single substitution — [subst1 (lift 1 t) u = t], and
    [subst sb (subst1 b u) = subst1 (subst (up_sub sb) b) (subst sb u)].
    With them, one-step reduction, multi-step reduction and conversion are
    stable under substitution and renaming, and reducing the argument of a
    substitution reduces the result.  For the contractions of a signature
    this rests on its invariant: a δ-body is closed, and ι commutes with
    substitution ([iota_subst]) because the indices of a recursive field
    mention only their telescope.

    These are the syntactic half of the correctness of substitution.  The
    typing half — weakening and the substitution lemma of the declarative
    rules — is stated in Contracts.v as an open obligation. *)

From Stdlib Require Import Relations Arith Lia List Bool.
From Stdlib Require String.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Signature Reduction.

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

(** ** Substitution on closed parts, under binders and on spines *)

Lemma subst_ext_closed_above : forall t k sb sb',
  closed_above k t = true -> (forall i, i < k -> sb i = sb' i) -> subst sb t = subst sb' t.
Proof.
  induction t; intros k sb sb' Hc Hs; cbn in *;
    repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [? ?] end;
    try reflexivity.
  all: try (apply Hs; apply Nat.ltb_lt; assumption).
  all: f_equal;
    first [ eapply IHt1; eassumption | eapply IHt2; eassumption | eapply IHt3; eassumption
          | eapply IHt4; eassumption | eapply IHt; eassumption
          | idtac ].
  all: match goal with
       | IH : forall k sb sb', closed_above k ?b = true -> _ -> subst sb ?b = subst sb' ?b,
         H : closed_above (S ?k) ?b = true |- subst (up_sub ?s) ?b = subst (up_sub ?s') ?b =>
           apply (IH (S k)); [exact H | intros [|i] Hi; cbn; [reflexivity | ]]
       end.
  all: rewrite Hs by lia; reflexivity.
Qed.

(** [upn m sb]: [sb] under [m] binders. *)
Fixpoint upn (m : nat) (sb : nat -> term) : nat -> term :=
  match m with
  | 0 => sb
  | S m' => up_sub (upn m' sb)
  end.

Lemma upn_lt : forall m sb n, n < m -> upn m sb n = Var n.
Proof.
  induction m as [|m IH]; intros sb n H; [lia | ].
  destruct n as [|n]; cbn; [reflexivity | ]. rewrite IH by lia. reflexivity.
Qed.

Lemma lift_lift : forall m t, lift 1 (lift m t) = lift (S m) t.
Proof. intros m t. unfold lift. rewrite rename_rename. reflexivity. Qed.

Lemma lift_zero : forall t, lift 0 t = t.
Proof. intros t. unfold lift. rewrite rename_as_subst. apply subst_var. Qed.

Lemma upn_ge : forall m sb n, upn m sb (m + n) = lift m (sb n).
Proof.
  induction m as [|m IH]; intros sb n; cbn; [now rewrite lift_zero | ].
  rewrite IH. apply lift_lift.
Qed.

Lemma subst_upn_lift : forall m sb t, subst (upn m sb) (lift m t) = lift m (subst sb t).
Proof.
  intros m sb t. unfold lift at 1. rewrite subst_rename.
  unfold lift. rewrite rename_subst. apply subst_ext. intros n. apply upn_ge.
Qed.

Lemma up_sub_upn : forall m sb n, upn m (up_sub sb) n = upn (S m) sb n.
Proof.
  induction m as [|m IH]; intros sb n; [reflexivity | ].
  cbn [upn]. apply up_sub_ext. apply IH.
Qed.

Lemma subst_lams : forall m sb b, subst sb (lams m b) = lams m (subst (upn m sb) b).
Proof.
  induction m as [|m IH]; intros sb b; [reflexivity | ].
  cbn [lams subst]. rewrite IH. f_equal. f_equal. apply subst_ext. apply up_sub_upn.
Qed.

Lemma subst_apps : forall sb us h, subst sb (apps h us) = apps (subst sb h) (map (subst sb) us).
Proof.
  intros sb us. induction us as [|u us IH]; intros h; [reflexivity | ].
  cbn [apps fold_left map]. unfold apps in IH. rewrite IH. reflexivity.
Qed.

Lemma subst_vars_upn : forall m sb base n, base + n <= m ->
  map (subst (upn m sb)) (vars base n) = vars base n.
Proof.
  intros m sb base n. induction n as [|n IH]; intros H; [reflexivity | ].
  cbn [vars map subst]. rewrite upn_lt by lia. rewrite IH by lia. reflexivity.
Qed.

(** The spine of a constant keeps its head under substitution. *)
Lemma subst_spine_const : forall t c sb, spine_head t = Const c ->
  spine_head (subst sb t) = Const c /\ spine_args (subst sb t) = map (subst sb) (spine_args t).
Proof.
  induction t; intros c sb H; cbn in H; try discriminate H.
  - destruct (IHt1 c sb H) as [Hh Ha]. cbn. split; [exact Hh | rewrite Ha, map_app; reflexivity].
  - injection H as ->. split; reflexivity.
Qed.

Lemma last_map_nonempty : forall (f : term -> term) l d d', l <> [] ->
  last (map f l) d' = f (last l d).
Proof.
  intros f l d d' H. induction l as [|a l IH]; [contradiction | ].
  destruct l as [|b l]; [reflexivity | ].
  change (last (map f (b :: l)) d' = f (last (b :: l) d)). apply IH. discriminate.
Qed.

(** ** ι commutes with substitution *)

Lemma hyp_subst : forall D j sb pre env Bs vs a,
  field_closed (length env) (FRec Bs vs) = true ->
  subst sb (hyp D j pre env Bs vs a) =
  hyp D j (map (subst sb) pre) (map (subst sb) env) Bs vs (subst sb a).
Proof.
  intros D j sb pre env Bs vs a Hc. cbn [field_closed] in Hc.
  apply andb_prop in Hc as [_ Hc]. rewrite forallb_forall in Hc.
  unfold hyp. rewrite subst_lams, subst_apps. cbn [subst]. f_equal. f_equal.
  rewrite !map_app. f_equal; [ | f_equal].
  - rewrite !map_map. apply map_ext. intros t. apply subst_upn_lift.
  - rewrite !map_map. apply map_ext_in. intros v Hv. rewrite subst_subst.
    apply (subst_ext_closed_above v (length env + length Bs)); [exact (Hc v Hv) | ].
    intros n Hn. unfold inst. destruct (Nat.ltb n (length Bs)) eqn:E.
    + cbn [subst]. apply Nat.ltb_lt in E. apply upn_lt, E.
    + apply Nat.ltb_ge in E. rewrite subst_upn_lift. f_equal.
      rewrite (nth_indep (map (subst sb) env) (Var 0) (subst sb (Var 0)))
        by (rewrite length_map; lia).
      rewrite map_nth. reflexivity.
  - cbn [map]. f_equal. rewrite subst_apps. f_equal; [apply subst_upn_lift | ].
    apply subst_vars_upn. lia.
Qed.

Lemma iota_args_subst : forall D j sb fs pre env xs,
  fields_closed (length env) fs = true ->
  map (subst sb) (iota_args D j pre env fs xs) =
  iota_args D j (map (subst sb) pre) (map (subst sb) env) fs (map (subst sb) xs).
Proof.
  intros D j sb fs. induction fs as [|fd fs IH]; intros pre env xs Hc; [reflexivity | ].
  destruct xs as [|a xs]; [destruct fd; reflexivity | ].
  cbn [fields_closed] in Hc. apply andb_prop in Hc as [Hf Hc].
  destruct fd as [A | Bs vs]; cbn [iota_args map].
  - f_equal. exact (IH pre (a :: env) xs Hc).
  - f_equal. f_equal; [exact (hyp_subst D j sb pre env Bs vs a Hf) | exact (IH pre (a :: env) xs Hc)].
Qed.

Lemma elim_view_subst : forall sg t sb (e : String.string * nat * ind_desc),
  elim_view sg t = Some e -> elim_view sg (subst sb t) = Some e.
Proof.
  intros sg t sb e H. unfold elim_view in *.
  destruct (spine_head t) eqn:Eh; try discriminate H. destruct g; try discriminate H.
  destruct (subst_spine_const t _ sb Eh) as [-> ->]. rewrite length_map. exact H.
Qed.

Theorem iota_subst : forall sg t u sb, iota sg t = Some u -> iota sg (subst sb t) = Some (subst sb u).
Proof.
  intros sg t u sb H. unfold iota in *.
  destruct (elim_view sg t) as [[[D j] d]|] eqn:Ev; [ | discriminate H].
  rewrite (elim_view_subst _ _ sb _ Ev).
  destruct (elim_view_spec _ _ _ _ _ Ev) as (Eh & Hlen & Hd).
  destruct (subst_spine_const t _ sb Eh) as [_ ->].
  assert (Hne : spine_args t <> []) by (intros E; rewrite E in Hlen; unfold elim_arity in Hlen; cbn in Hlen; lia).
  rewrite (last_map_nonempty _ _ (Var 0) _ Hne).
  destruct (spine_head (last (spine_args t) (Var 0))) eqn:Ex; try discriminate H.
  destruct g; try discriminate H.
  destruct (subst_spine_const _ _ sb Ex) as [-> ->].
  destruct (String.eqb s D); [ | discriminate H].
  destruct (find_ctor (ind_ctors d) s0) as [[i cd]|] eqn:Ec; [ | discriminate H].
  rewrite length_map.
  destruct (Nat.eqb _ _); [ | discriminate H].
  rewrite skipn_map, firstn_map, nth_error_map.
  destruct (nth_error _ i) as [m|]; [ | discriminate H].
  injection H as <-. cbn [option_map]. f_equal.
  rewrite subst_apps, firstn_map, firstn_map, <- map_rev, skipn_map. f_equal.
  rewrite iota_args_subst; [reflexivity | ].
  unfold ind_closed in Hd. apply andb_prop in Hd as [_ Hcs].
  pose proof (find_ctor_closed _ _ _ _ _ Hcs Ec) as Hcd.
  apply andb_prop in Hcd as [Hf _].
  rewrite length_rev, firstn_length_le; [exact Hf | ].
  rewrite Hlen. unfold elim_arity. lia.
Qed.

(** ** Reduction and conversion under substitution *)

Section Red.
Variable sg : signature.
Local Notation "t ⇝ u" := (red1 sg t u).
Local Notation "t ⇝* u" := (red sg t u).
Local Notation "t ≡ u" := (conv sg t u).

Theorem red1_subst : forall t u, t ⇝ u -> forall sb, subst sb t ⇝ subst sb u.
Proof.
  intros t u H. induction H; intros sb; cbn.
  all: lazymatch goal with
       | H : iota _ _ = Some _ |- _ => apply R_Iota, iota_subst, H
       | H : sig_delta _ _ = Some ?b |- _ =>
           rewrite (subst_closed sb b (sig_delta_closed _ _ _ H)); apply R_Delta, H
       | |- red1 _ (App (Lam _) _) _ => rewrite subst_subst1; apply R_Beta
       | _ => constructor; auto
       end.
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
  all: eauto using red_pi, red_lam, red_app, red_ann, red_elim_void, red_elim_unit, rt_refl,
         red_sigma, red_pair, red_fst, red_snd.
Qed.

Corollary red_subst1_arg : forall b u u', u ⇝* u' -> subst1 b u ⇝* subst1 b u'.
Proof.
  intros b u u' H. apply red_subst_pointwise. intros [|n]; [exact H | apply rt_refl].
Qed.
End Red.

(** The lemmas take their signature implicitly: it is fixed by their
    statements. *)
Arguments red1_subst {sg}.
Arguments red1_rename {sg}.
Arguments red_subst {sg}.
Arguments conv_subst {sg}.
Arguments conv_rename {sg}.
Arguments red_ann {sg}.
Arguments red_rename {sg}.
Arguments red_subst_pointwise {sg}.
Arguments red_subst1_arg {sg}.
