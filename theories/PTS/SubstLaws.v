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
    mention only their telescope.  ι of [match] and the unfolding of
    [fix] commute with substitution without any invariant
    ([case_iota_subst], [fix_unfold_subst]).

    These are the syntactic half of the correctness of substitution.  The
    typing half — weakening and the substitution lemma of the declarative
    rules — is stated in PTS/Contracts.v as an open obligation. *)

From Stdlib Require Import Relations Arith Lia List Bool.
From Stdlib Require String.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Telescope Signature Reduction.

Implicit Types (r : nat -> nat) (sb : nat -> term) (t u b : term).

(** ** Extensionality *)

Lemma up_ren_ext : forall r r', (forall n, r n = r' n) -> forall n, up_ren r n = up_ren r' n.
Proof. intros r r' H [|n]; cbn; congruence. Qed.

Lemma rename_ext : forall t r r', (forall n, r n = r' n) -> rename r t = rename r' t.
Proof.
  induction t using term_ind'; intros r r' H; cbn; f_equal; eauto using up_ren_ext; try reflexivity.
  on_branches. exact H.
Qed.

Lemma up_sub_ext : forall sb sb', (forall n, sb n = sb' n) -> forall n, up_sub sb n = up_sub sb' n.
Proof. intros sb sb' H [|n]; cbn; [reflexivity | now rewrite H]. Qed.

Lemma subst_ext : forall t sb sb', (forall n, sb n = sb' n) -> subst sb t = subst sb' t.
Proof.
  induction t using term_ind'; intros sb sb' H; cbn; f_equal; eauto using up_sub_ext; try reflexivity.
  on_branches. exact H.
Qed.

(** ** Identity and fusion *)

Lemma subst_var : forall t, subst Var t = t.
Proof.
  induction t using term_ind'; cbn; f_equal; try assumption; try reflexivity.
  all: try on_branches.
  all: match goal with
       | |- subst ?sb ?t = ?t => rewrite (subst_ext t sb Var); [assumption | intros [|m]; reflexivity]
       end.
Qed.

Lemma rename_rename : forall t r r', rename r (rename r' t) = rename (fun n => r (r' n)) t.
Proof.
  induction t using term_ind'; intros r r'; cbn; f_equal; try apply IHt1; try apply IHt2; try apply IHt3;
    try apply IHt4; try apply IHt; try reflexivity.
  all: try on_branches.
  all: rewrite ?IHt2, ?IHt; apply rename_ext; intros [|m]; reflexivity.
Qed.

Lemma rename_subst : forall t r sb,
  rename r (subst sb t) = subst (fun n => rename r (sb n)) t.
Proof.
  induction t using term_ind'; intros r sb; cbn; f_equal; try apply IHt1; try apply IHt2; try apply IHt3;
    try apply IHt4; try apply IHt; try reflexivity.
  all: try on_branches.
  all: rewrite ?IHt2, ?IHt; apply subst_ext; intros [|m]; [reflexivity | ].
  all: cbn; unfold lift; rewrite !rename_rename; apply rename_ext; reflexivity.
Qed.

Lemma subst_rename : forall t sb r,
  subst sb (rename r t) = subst (fun n => sb (r n)) t.
Proof.
  induction t using term_ind'; intros sb r; cbn; f_equal; try apply IHt1; try apply IHt2; try apply IHt3;
    try apply IHt4; try apply IHt; try reflexivity.
  all: try on_branches.
  all: rewrite ?IHt2, ?IHt; apply subst_ext; intros [|m]; reflexivity.
Qed.

Lemma subst_subst : forall t sb sb',
  subst sb (subst sb' t) = subst (fun n => subst sb (sb' n)) t.
Proof.
  induction t using term_ind'; intros sb sb'; cbn; f_equal; try apply IHt1; try apply IHt2; try apply IHt3;
    try apply IHt4; try apply IHt; try reflexivity.
  all: try on_branches.
  all: rewrite ?IHt2, ?IHt; apply subst_ext; intros [|m]; [reflexivity | ].
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
  induction t using term_ind'; intros k sb sb' Hc Hs; cbn in *;
    repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [? ?] end;
    try reflexivity.
  all: try (apply Hs; apply Nat.ltb_lt; assumption).
  all: f_equal;
    first [ eapply IHt1; eassumption | eapply IHt2; eassumption | eapply IHt3; eassumption
          | eapply IHt4; eassumption | eapply IHt; eassumption
          | idtac ].
  all: try (on_branches; assumption).
  all: match goal with
       | IH : forall k sb sb', closed_above k ?b = true -> _ -> subst sb ?b = subst sb' ?b,
         H : closed_above (S ?k) ?b = true |- subst (up_sub ?s) ?b = subst (up_sub ?s') ?b =>
           apply (IH (S k)); [exact H | intros [|i] Hi; cbn; [reflexivity | ]]
       end.
  all: rewrite Hs by lia; reflexivity.
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

(** The environments of PTS.Telescope compute [upn] and [subst_tele]. *)
Lemma inst_upn : forall m env n, inst m env n = upn m (fun i => nth i env (Var 0)) n.
Proof.
  intros m env n. unfold inst. destruct (Nat.ltb n m) eqn:E.
  - apply Nat.ltb_lt in E. rewrite upn_lt by exact E. reflexivity.
  - apply Nat.ltb_ge in E.
    replace (upn m _ n) with (upn m (fun i => nth i env (Var 0)) (m + (n - m))) by (f_equal; lia).
    rewrite upn_ge. reflexivity.
Qed.

Lemma inst_tele_subst : forall env m Ts,
  inst_tele_env env m Ts = subst_tele (upn m (fun i => nth i env (Var 0))) Ts.
Proof.
  intros env m Ts. revert m. induction Ts as [|T Ts IH]; intros m; [reflexivity | ].
  cbn [inst_tele_env subst_tele]. unfold inst_env. f_equal.
  - apply subst_ext. intros n. apply inst_upn.
  - rewrite IH. reflexivity.
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

(** A spine whose head is not a variable keeps its shape under
    substitution: its head and its arguments are substituted. *)
Lemma subst_spine : forall t sb, (forall n, spine_head t <> Var n) ->
  spine_head (subst sb t) = subst sb (spine_head t) /\ spine_args (subst sb t) = map (subst sb) (spine_args t).
Proof.
  induction t; intros sb H; try (exfalso; apply (H n); reflexivity).
  all: try (split; reflexivity).
  cbn [subst spine_head] in *. rewrite !spine_args_App, map_app.
  destruct (IHt1 sb H) as [-> ->]. split; reflexivity.
Qed.

Lemma subst_spine_fix : forall t A k b sb, spine_head t = Fix A k b ->
  spine_head (subst sb t) = Fix (subst sb A) k (subst (up_sub sb) b) /\
  spine_args (subst sb t) = map (subst sb) (spine_args t).
Proof.
  intros t A k b sb E. destruct (subst_spine t sb) as [Hh Ha]; [intros n; rewrite E; discriminate | ].
  rewrite Hh, E. split; [reflexivity | exact Ha].
Qed.

Lemma subst_spine_const : forall t c sb, spine_head t = Const c ->
  spine_head (subst sb t) = Const c /\ spine_args (subst sb t) = map (subst sb) (spine_args t).
Proof.
  intros t c sb E. destruct (subst_spine t sb) as [Hh Ha]; [intros n; rewrite E; discriminate | ].
  rewrite Hh, E. split; [reflexivity | exact Ha].
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

Lemma elim_view_subst : forall sg t sb (e : String.string * sort * ind_desc),
  elim_view sg t = Some e -> elim_view sg (subst sb t) = Some e.
Proof.
  intros sg t sb e H. unfold elim_view in *.
  destruct (spine_head t) eqn:Eh; try discriminate H. destruct g; try discriminate H.
  destruct (subst_spine_const t _ sb Eh) as [-> ->]. rewrite length_map. exact H.
Qed.

(** A constructor spine stays one under substitution, with its fields
    substituted. *)
Lemma ctor_view_subst : forall D d x i cd xs sb, ctor_view D d x = Some (i, cd, xs) ->
  ctor_view D d (subst sb x) = Some (i, cd, map (subst sb) xs).
Proof.
  intros D d x i cd xs sb H. unfold ctor_view in *. cbv zeta in *.
  destruct (spine_head x) eqn:Eh; try discriminate H. destruct g as [ | D' c | | ]; try discriminate H.
  destruct (subst_spine_const x _ sb Eh) as [-> ->].
  destruct (String.eqb D' D); [ | discriminate H].
  destruct (find_ctor (ind_ctors d) c) as [[i' cd']|]; [ | discriminate H].
  rewrite length_map. destruct (Nat.eqb _ _); [ | discriminate H].
  injection H as <- <- <-. rewrite skipn_map. reflexivity.
Qed.

Theorem iota_subst : forall sg t u sb, iota sg t = Some u -> iota sg (subst sb t) = Some (subst sb u).
Proof.
  intros sg t u sb H. unfold iota, iota_at in *.
  destruct (elim_view sg t) as [[[D j] d]|] eqn:Ev; [ | discriminate H].
  rewrite (elim_view_subst _ _ sb _ Ev).
  destruct (elim_view_spec _ _ _ _ _ Ev) as (Eh & Hlen & Hd).
  destruct (subst_spine_const t _ sb Eh) as [_ ->].
  assert (Hne : spine_args t <> []) by (intros E; rewrite E in Hlen; unfold elim_arity in Hlen; cbn in Hlen; lia).
  rewrite (last_map_nonempty _ _ (Var 0) _ Hne).
  destruct (ctor_view D d (last (spine_args t) (Var 0))) as [[[i cd] xs]|] eqn:Ev'; [ | discriminate H].
  rewrite (ctor_view_subst _ _ _ _ _ _ sb Ev').
  rewrite skipn_map, firstn_map, nth_error_map.
  destruct (nth_error _ i) as [m|]; [ | discriminate H].
  injection H as <-. cbn [option_map]. f_equal.
  rewrite subst_apps, firstn_map, firstn_map, !rev'_rev, <- map_rev. f_equal.
  rewrite iota_args_subst; [reflexivity | ].
  destruct (ctor_view_spec _ _ _ _ _ _ Ev') as (c & ps & _ & Ec & _ & _).
  unfold ind_closed in Hd. apply andb_prop in Hd as [_ Hcs].
  pose proof (find_ctor_closed _ _ _ _ _ Hcs Ec) as Hcd.
  apply andb_prop in Hcd as [Hf _].
  rewrite length_rev, firstn_length_le; [exact Hf | ].
  rewrite Hlen. unfold elim_arity. lia.
Qed.

(** ** ι of match and the unfolding of fix commute with substitution *)

Theorem case_iota_subst : forall sg t u sb,
  case_iota sg t = Some u -> case_iota sg (subst sb t) = Some (subst sb u).
Proof.
  intros sg t u sb H. destruct (case_iota_case _ _ _ H) as (D & s & P & x & bs & ->).
  unfold case_iota in *. cbn [subst].
  destruct (sig_ind sg D) as [d|]; [ | discriminate H].
  destruct (ctor_view D d x) as [[[i cd] xs]|] eqn:Ev; [ | discriminate H].
  rewrite (ctor_view_subst _ _ _ _ _ _ sb Ev).
  rewrite nth_error_map. destruct (nth_error bs i) as [b|]; [ | discriminate H].
  cbn in H |- *. injection H as <-. f_equal. rewrite subst_apps. reflexivity.
Qed.

Theorem fix_unfold_subst : forall t u sb,
  fix_unfold t = Some u -> fix_unfold (subst sb t) = Some (subst sb u).
Proof.
  intros t u sb H. unfold fix_unfold, fix_at in *.
  destruct (fix_view t) as [[[A k] b]|] eqn:Ev; [ | discriminate H].
  destruct (fix_view_spec _ _ _ _ Ev) as [Eh Hl].
  destruct (subst_spine_fix t A k b sb Eh) as [Eh' Ea'].
  assert (Ev' : fix_view (subst sb t) = Some (subst sb A, k, subst (up_sub sb) b))
    by (unfold fix_view; rewrite Eh', Ea', length_map, Hl, Nat.eqb_refl; reflexivity).
  rewrite Ev', Ea'.
  assert (Hne : spine_args t <> []) by (intros E; rewrite E in Hl; discriminate Hl).
  rewrite (last_map_nonempty _ _ (Var 0) _ Hne).
  destruct (spine_head (last (spine_args t) (Var 0))) eqn:Ex; try discriminate H.
  destruct g; try discriminate H.
  destruct (subst_spine_const _ _ sb Ex) as [-> _].
  injection H as <-. f_equal. rewrite subst_apps, subst_subst1. reflexivity.
Qed.

(** The contraction of a spine at its last argument: ι of an instance,
    or the unfolding of a fix, whose spine no instance heads. *)
Theorem spine_iota_subst : forall sg t u sb,
  spine_iota sg t = Some u -> spine_iota sg (subst sb t) = Some (subst sb u).
Proof.
  intros sg t u sb H. unfold spine_iota in *.
  destruct (iota sg t) as [v|] eqn:E.
  - injection H as <-. rewrite (iota_subst _ _ _ sb E). reflexivity.
  - assert (Hv : fix_view t <> None) by (unfold fix_unfold in H; destruct (fix_view t); [discriminate | discriminate H]).
    destruct (fix_view t) as [[[A k] b]|] eqn:Ev; [ | contradiction].
    destruct (fix_view_spec _ _ _ _ Ev) as [Eh _].
    destruct (subst_spine_fix t A k b sb Eh) as [Eh' _].
    replace (iota sg (subst sb t)) with (@None term) by (unfold iota, elim_view; rewrite Eh'; reflexivity).
    exact (fix_unfold_subst _ _ sb H).
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
       | H : spine_iota _ _ = Some _ |- _ => apply R_Spine, spine_iota_subst, H
       | H : case_iota _ _ = Some _ |- _ => apply R_Case, case_iota_subst, H
       | |- red1 _ (Case _ _ _ _ (map _ (_ ++ _ :: _))) _ =>
           rewrite !map_app; cbn [map]; apply R_CaseBr; auto
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
  induction t using term_ind'; intros sb sb' H; cbn; try apply rt_refl; try apply H.
  all: assert (Hup : forall n, up_sub sb n ⇝* up_sub sb' n)
         by (intros [|m]; cbn; [apply rt_refl | apply red_rename, H]).
  all: try (apply red_elim_bool; eauto).
  all: try (apply red_case; [eauto | eauto | ]; apply red_list_map;
            eapply Forall_impl; [ | exact IHl]; intros b Hb; apply Hb, H).
  all: eauto using red_pi, red_lam, red_app, red_ann, red_elim_void, red_elim_unit, rt_refl,
         red_sigma, red_pair, red_fst, red_snd, red_fix.
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
