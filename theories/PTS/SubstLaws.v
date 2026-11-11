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
    rules — is PTS.TypingSubst. *)

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

(** ** Renamings, lifts and spines *)

Lemma rename_id : forall t, rename (fun n => n) t = t.
Proof. intros t. rewrite rename_as_subst. apply subst_var. Qed.

Lemma subst_shift_back : forall t, subst1 (rename (up_ren (Nat.add 1)) t) (Var 0) = t.
Proof.
  intros t. unfold subst1. rewrite subst_rename. rewrite <- (subst_var t) at 2.
  apply subst_ext. intros [|n]; reflexivity.
Qed.

Lemma rename_closed : forall r A, closed A = true -> rename r A = A.
Proof. intros r A H. apply (rename_closed_above A 0); [exact H | intros i Hi; lia]. Qed.

Lemma rename_up_lift1 : forall r A, rename (up_ren r) (lift 1 A) = lift 1 (rename r A).
Proof. intros r A. unfold lift. rewrite !rename_rename. apply rename_ext. intros n. reflexivity. Qed.

Lemma subst_up_lift1 : forall sb A, subst (up_sub sb) (lift 1 A) = lift 1 (subst sb A).
Proof. intros sb A. exact (subst_upn_lift 1 sb A). Qed.

Lemma rename_apps : forall r us h, rename r (apps h us) = apps (rename r h) (map (rename r) us).
Proof.
  intros r us. induction us as [|u us IH]; intros h; [reflexivity | ].
  cbn [apps fold_left map]. unfold apps in IH. rewrite IH. reflexivity.
Qed.

Lemma map_rename_as_subst : forall r ts, map (rename r) ts = map (subst (fun n => Var (r n))) ts.
Proof. intros r ts. apply map_ext. intros t. apply rename_as_subst. Qed.

(** A renaming under a binder is a substitution under it. *)
Lemma rename_up_as_subst : forall r b, rename (up_ren r) b = subst (up_sub (fun n => Var (r n))) b.
Proof. intros r b. rewrite rename_as_subst. apply subst_ext. intros [|n]; reflexivity. Qed.

Lemma free_in_rename : forall t r j, free_in j (rename r t) = true -> exists i, r i = j.
Proof.
  induction t using term_ind'; intros r j H; cbn [rename free_in] in H;
    repeat match goal with H : _ || _ = true |- _ => apply orb_true_iff in H as [H | H] end;
    try discriminate H.
  (* the variable *)
  all: try (exists n; apply Nat.eqb_eq, H).
  (* a subterm outside a binder *)
  all: try solve [eauto].
  (* a subterm under a binder *)
  all: try match goal with
           | IH : forall r j, free_in j (rename r ?b) = true -> _,
             H : free_in (S ?j) (rename (up_ren ?r) ?b) = true |- _ =>
               destruct (IH _ _ H) as [[|i] Hi]; [discriminate Hi | exists i; injection Hi; auto]
           end.
  (* a branch *)
  apply existsb_exists in H as (x & Hx & H). apply in_map_iff in Hx as (b & <- & Hb).
  rewrite Forall_forall in IHl. exact (IHl b Hb r j H).
Qed.

Lemma free_in_lift : forall t m j, free_in j (lift m t) = true -> m <= j.
Proof. intros t m j H. destruct (free_in_rename t (Nat.add m) j H) as [i <-]. lia. Qed.

Lemma spine_head_subst : forall t sb, spine_head (subst sb t) = spine_head (subst sb (spine_head t)).
Proof. induction t; intros sb; try reflexivity. cbn [subst spine_head]. apply IHt1. Qed.

Lemma spine_args_subst_var : forall t sb i, spine_head t = Var i -> sb i = Var i ->
  spine_args (subst sb t) = map (subst sb) (spine_args t).
Proof.
  induction t; intros sb i H Hs; cbn [spine_head] in H; try discriminate H.
  - injection H as ->. cbn [subst]. rewrite Hs. reflexivity.
  - cbn [subst]. rewrite !spine_args_App, map_app, (IHt1 sb i H Hs). reflexivity.
Qed.

Lemma subst_lam_cases : forall sb t c, subst sb t = Lam c ->
  (exists b, t = Lam b) \/ (exists i, t = Var i /\ sb i = Lam c).
Proof. intros sb t c H. destruct t; cbn [subst] in H; try discriminate H; eauto. Qed.

Lemma lookup_cons_0 : forall A G, lookup (A :: G) 0 = Some (lift 1 A).
Proof. reflexivity. Qed.

Lemma lookup_cons_S : forall A G n, lookup (A :: G) (S n) = option_map (lift 1) (lookup G n).
Proof.
  intros A G n. unfold lookup. cbn [nth_error].
  destruct (nth_error G n); cbn [option_map]; [rewrite lift_lift | ]; reflexivity.
Qed.

(** ** Telescopes substituted at once *)

Lemma subst_pis : forall Ts B sb,
  subst sb (pis Ts B) = pis (subst_tele sb Ts) (subst (upn (length Ts) sb) B).
Proof.
  induction Ts as [|T Ts IH]; intros B sb; [reflexivity | ].
  cbn [pis subst subst_tele length]. rewrite IH. f_equal. f_equal.
  apply subst_ext. intros n. apply up_sub_upn.
Qed.

Lemma subst_tsub_nil : forall t, subst (tsub []) t = t.
Proof. intros t. rewrite <- (subst_var t) at 2. apply subst_ext. exact tsub_nil. Qed.

Lemma subst_tsub_lift : forall args t, subst (tsub args) (lift (length args) t) = t.
Proof.
  intros args t. unfold lift. rewrite subst_rename. rewrite <- (subst_var t) at 2. apply subst_ext.
  intros i. unfold tsub. rewrite nth_overflow by (rewrite length_rev; lia). f_equal. lia.
Qed.

Lemma map_tsub_lift : forall args l, map (subst (tsub args)) (map (lift (length args)) l) = l.
Proof.
  intros args l. rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext. intros t. apply subst_tsub_lift.
Qed.

(** Substituting the first argument, then the others. *)
Lemma tsub_cons : forall a args i,
  subst (tsub args) (upn (length args) (scons a Var) i) = tsub (a :: args) i.
Proof.
  intros a args i. destruct (Nat.lt_ge_cases i (length args)) as [H | H].
  - rewrite upn_lt by exact H. cbn [subst]. symmetry. apply tsub_lt, H.
  - replace i with (length args + (i - length args)) by lia. rewrite upn_ge.
    destruct (i - length args) as [|j] eqn:E.
    + cbn [scons]. rewrite Nat.add_0_r, subst_tsub_lift. unfold tsub. cbn [rev].
      rewrite app_nth2 by (rewrite length_rev; lia). rewrite length_rev, Nat.sub_diag. reflexivity.
    + cbn [scons]. unfold lift. cbn [rename subst]. unfold tsub.
      rewrite !nth_overflow by (cbn [rev]; rewrite ?length_app, length_rev; cbn [length]; lia).
      cbn [length]. f_equal. lia.
Qed.

Lemma subst_tsub_cons : forall a args n R, n = length args ->
  subst (tsub args) (subst (upn n (scons a Var)) R) = subst (tsub (a :: args)) R.
Proof. intros a args n R ->. rewrite subst_subst. apply subst_ext. apply tsub_cons. Qed.

(** Substituting the last argument after the others. *)
Lemma tsub_snoc : forall a args i,
  subst (scons a Var) (up_sub (tsub args) i) = tsub (args ++ [a]) i.
Proof.
  intros a args [|i].
  - cbn [up_sub subst scons]. unfold tsub. rewrite rev_app_distr. reflexivity.
  - cbn [up_sub]. change (subst (scons a Var) (lift 1 (tsub args i))) with (subst1 (lift 1 (tsub args i)) a).
    rewrite subst1_lift. unfold tsub. rewrite rev_app_distr, length_app. cbn [rev app nth length].
    replace (S i - (length args + 1)) with (i - length args) by lia. reflexivity.
Qed.

Lemma subst_tsub_snoc : forall a args R,
  subst (tsub (args ++ [a])) R = subst1 (subst (up_sub (tsub args)) R) a.
Proof.
  intros a args R. unfold subst1. rewrite subst_subst. apply subst_ext. intros i. symmetry. apply tsub_snoc.
Qed.

(** The variables of a telescope, the arguments substituted: the
    arguments. *)
Lemma map_tsub_vars : forall l m, map (subst (tsub (l ++ m))) (vars (length m) (length l)) = l.
Proof.
  induction l as [|a l IH]; intros m; [reflexivity | ].
  cbn [length vars map app]. f_equal.
  - cbn [subst]. unfold tsub. cbn [rev].
    rewrite app_nth2 by (rewrite length_rev, length_app; lia).
    rewrite length_rev, length_app. replace (length m + length l - (length l + length m)) with 0 by lia.
    reflexivity.
  - transitivity (map (subst (tsub (l ++ m))) (vars (length m) (length l))); [ | apply IH].
    apply map_ext_in. intros t Ht. destruct (vars_in _ _ _ Ht) as (i & -> & Hi).
    cbn [subst]. apply tsub_lt. rewrite length_app. lia.
Qed.

Lemma map_tsub_vars0 : forall l, map (subst (tsub l)) (vars 0 (length l)) = l.
Proof. intros l. pose proof (map_tsub_vars l []) as E. rewrite app_nil_r in E. exact E. Qed.

(** The arguments of a telescope, then those of an inner one. *)
Lemma tsub_app : forall ps xs i, subst (tsub xs) (upn (length xs) (tsub ps) i) = tsub (ps ++ xs) i.
Proof.
  intros ps xs i. destruct (Nat.lt_ge_cases i (length xs)) as [H | H].
  - rewrite upn_lt by exact H. cbn [subst]. unfold tsub. rewrite rev_app_distr.
    rewrite app_nth1 by (rewrite length_rev; exact H). apply nth_indep. rewrite length_rev. exact H.
  - replace i with (length xs + (i - length xs)) by lia. rewrite upn_ge, subst_tsub_lift.
    unfold tsub. rewrite rev_app_distr, app_nth2 by (rewrite length_rev; lia).
    rewrite length_rev, length_app. replace (length xs + (i - length xs) - length xs) with (i - length xs) by lia.
    destruct (Nat.lt_ge_cases (i - length xs) (length ps)) as [H' | H'].
    + apply nth_indep. rewrite length_rev. exact H'.
    + rewrite !nth_overflow by (rewrite length_rev; exact H'). f_equal. lia.
Qed.

Lemma subst_tele_ext : forall Ts sb sb', (forall n, sb n = sb' n) -> subst_tele sb Ts = subst_tele sb' Ts.
Proof.
  induction Ts as [|T Ts IH]; intros sb sb' H; cbn [subst_tele]; [reflexivity | ].
  f_equal; [apply subst_ext, H | apply IH, up_sub_ext, H].
Qed.

Lemma subst_tele_app : forall Ts1 Ts2 sb,
  subst_tele sb (Ts1 ++ Ts2) = subst_tele sb Ts1 ++ subst_tele (upn (length Ts1) sb) Ts2.
Proof.
  induction Ts1 as [|T Ts1 IH]; intros Ts2 sb; cbn [app subst_tele length]; [reflexivity | ].
  f_equal. rewrite IH. f_equal. apply subst_tele_ext. intros n. apply up_sub_upn.
Qed.

Lemma subst_tele_subst_tele : forall Ts sb sb',
  subst_tele sb (subst_tele sb' Ts) = subst_tele (fun n => subst sb (sb' n)) Ts.
Proof.
  induction Ts as [|T Ts IH]; intros sb sb'; cbn [subst_tele]; [reflexivity | ].
  f_equal; [apply subst_subst | ]. rewrite IH. apply subst_tele_ext.
  intros [|n]; cbn [up_sub subst]; [reflexivity | apply subst_up_lift1].
Qed.

Lemma subst_tele_var : forall Ts sb, (forall n, sb n = Var n) -> subst_tele sb Ts = Ts.
Proof.
  induction Ts as [|T Ts IH]; intros sb H; cbn [subst_tele]; [reflexivity | ].
  f_equal; [rewrite (subst_ext T sb Var H); apply subst_var | apply IH].
  intros [|n]; cbn [up_sub]; [reflexivity | rewrite H; reflexivity].
Qed.

Lemma upn_ext_lt : forall m k f g, (forall i, i < k -> f i = g i) ->
  forall n, n < m + k -> upn m f n = upn m g n.
Proof.
  intros m k f g H n Hn. destruct (Nat.lt_ge_cases n m) as [Hm | Hm].
  - rewrite !upn_lt by exact Hm. reflexivity.
  - replace n with (m + (n - m)) by lia. rewrite !upn_ge. f_equal. apply H. lia.
Qed.

(** The telescopes of a declaration, the parameters substituted, as
    telescopes substituted at once. *)
Lemma inst_env_tsub : forall ps m T, closed_above (m + length ps) T = true ->
  inst_env (params_env ps) m T = subst (upn m (tsub ps)) T.
Proof.
  intros ps m T HT. unfold inst_env. apply (subst_ext_closed_above T (m + length ps)); [exact HT | ].
  intros i Hi. rewrite inst_upn. apply (upn_ext_lt m (length ps)); [ | exact Hi].
  intros j Hj. unfold tsub. rewrite params_env_rev. apply nth_indep. rewrite length_rev. exact Hj.
Qed.

Lemma inst_tele_tsub : forall Ts ps m, tele_closed (m + length ps) Ts = true ->
  inst_tele_env (params_env ps) m Ts = subst_tele (upn m (tsub ps)) Ts.
Proof.
  induction Ts as [|T Ts IH]; intros ps m H; [reflexivity | ].
  cbn [tele_closed] in H. apply andb_prop in H as [HT H].
  cbn [inst_tele_env subst_tele]. f_equal; [exact (inst_env_tsub ps m T HT) | ].
  exact (IH ps (S m) H).
Qed.

(** ** Substitution in the types of a match *)

(** A term under the parameters and [m] binders, the parameters
    substituted: a substitution outside goes into the parameters. *)
Lemma subst_inst_env : forall env m T sb, closed_above (m + length env) T = true ->
  subst (upn m sb) (inst_env env m T) = inst_env (map (subst sb) env) m T.
Proof.
  intros env m T sb Hc. unfold inst_env. rewrite subst_subst.
  apply (subst_ext_closed_above T (m + length env)); [exact Hc | ].
  intros n Hn. unfold inst. destruct (Nat.ltb n m) eqn:E.
  - cbn [subst]. apply upn_lt. apply Nat.ltb_lt, E.
  - apply Nat.ltb_ge in E. rewrite subst_upn_lift. f_equal.
    rewrite (nth_indep (map (subst sb) env) (Var 0) (subst sb (Var 0))) by (rewrite length_map; lia).
    rewrite map_nth. reflexivity.
Qed.

Lemma subst_inst_tele_env : forall Ts env m sb, tele_closed (m + length env) Ts = true ->
  subst_tele (upn m sb) (inst_tele_env env m Ts) = inst_tele_env (map (subst sb) env) m Ts.
Proof.
  induction Ts as [|T Ts IH]; intros env m sb H; [reflexivity | ].
  cbn [tele_closed] in H. apply andb_prop in H as [HT H].
  cbn [inst_tele_env subst_tele]. f_equal; [exact (subst_inst_env env m T sb HT) | ].
  exact (IH env (S m) sb H).
Qed.

Lemma subst_case_motive_type : forall d ps s sb,
  tele_closed (length ps) (ind_indices d) = true ->
  subst sb (case_motive_type d ps s) = case_motive_type d (map (subst sb) ps) s.
Proof.
  intros d ps s sb Hc. unfold case_motive_type, inst_tele. cbv zeta.
  rewrite subst_pis, inst_tele_env_length. f_equal.
  - rewrite params_env_map. apply (subst_inst_tele_env _ _ 0 sb).
    rewrite params_env_length. exact Hc.
  - cbn [subst]. rewrite subst_apps, map_app, !map_map. cbn [subst]. do 3 f_equal.
    + apply map_ext. intros t. apply subst_upn_lift.
    + apply subst_vars_upn. lia.
Qed.

Lemma subst_case_branch_type : forall d ps P c sb,
  length ps = length (ind_params d) -> ctor_closed (length (ind_params d)) c = true ->
  subst sb (case_branch_type d ps P c) = case_branch_type d (map (subst sb) ps) (subst sb P) c.
Proof.
  intros d ps P c sb Hl Hc. unfold ctor_closed in Hc. apply andb_prop in Hc as [Hf Hi].
  unfold case_branch_type. cbv zeta.
  rewrite subst_pis, inst_tele_env_length, field_types_length. f_equal.
  - rewrite params_env_map. apply (subst_inst_tele_env _ _ 0 sb).
    rewrite params_env_length, Hl. cbn [Nat.add].
    pose proof (field_types_closed (ind_name d) (length (ind_params d)) (ctor_fields c) 0) as H.
    rewrite Nat.add_0_r in H. exact (H Hf).
  - rewrite subst_apps, subst_upn_lift, map_app, !map_map. f_equal. f_equal.
    + apply map_ext_in. intros v Hv. rewrite params_env_map. apply subst_inst_env.
      rewrite params_env_length, Hl, Nat.add_comm. rewrite forallb_forall in Hi. exact (Hi v Hv).
    + cbn [map]. f_equal. rewrite subst_apps, map_app, !map_map. cbn [subst]. do 2 f_equal.
      * apply map_ext. intros t. apply subst_upn_lift.
      * apply subst_vars_upn. lia.
Qed.

Lemma rename_case_motive_type : forall d ps s r,
  tele_closed (length ps) (ind_indices d) = true ->
  rename r (case_motive_type d ps s) = case_motive_type d (map (rename r) ps) s.
Proof.
  intros d ps s r H. rewrite rename_as_subst, subst_case_motive_type by exact H.
  rewrite map_rename_as_subst. reflexivity.
Qed.

Lemma rename_case_branch_type : forall d ps P c r,
  length ps = length (ind_params d) -> ctor_closed (length (ind_params d)) c = true ->
  rename r (case_branch_type d ps P c) = case_branch_type d (map (rename r) ps) (rename r P) c.
Proof.
  intros d ps P c r Hl Hc. rewrite rename_as_subst, subst_case_branch_type by assumption.
  rewrite map_rename_as_subst, (rename_as_subst P). reflexivity.
Qed.

(** ** The structural argument, reduction and conversion under substitution *)

Lemma struct_arg_subst : forall sg A k D sb, struct_arg sg A k D -> struct_arg sg (subst sb A) k D.
Proof.
  intros sg A k D sb H. revert sb.
  induction H as [A T B D us HA HT | A T B k D HA H IH]; intros sb.
  - pose proof (red_subst sb _ _ HT) as HT'. rewrite subst_apps in HT'.
    exact (SA_Here sg (subst sb A) (subst sb T) (subst (up_sub sb) B) D _ (red_subst sb _ _ HA) HT').
  - exact (SA_Next sg (subst sb A) (subst sb T) (subst (up_sub sb) B) k D (red_subst sb _ _ HA) (IH (up_sub sb))).
Qed.

Lemma struct_arg_rename : forall sg A k D r, struct_arg sg A k D -> struct_arg sg (rename r A) k D.
Proof. intros sg A k D r H. rewrite rename_as_subst. apply struct_arg_subst, H. Qed.

Lemma red_upn : forall sg sb sb', (forall n, red sg (sb n) (sb' n)) ->
  forall m n, red sg (upn m sb n) (upn m sb' n).
Proof.
  intros sg sb sb' H m. induction m as [|m IH]; intros n; [apply H | ].
  destruct n as [|n]; cbn [upn up_sub]; [apply rt_refl | apply red_rename, IH].
Qed.

Lemma forall2_conv_lift : forall sg n l l', Forall2 (conv sg) l l' ->
  Forall2 (conv sg) (map (lift n) l) (map (lift n) l').
Proof. intros sg n l l' H. induction H; constructor; [unfold lift; apply conv_rename; assumption | assumption]. Qed.

Lemma forall2_conv_subst_tele : forall sg Ts Ts', Forall2 (conv sg) Ts Ts' ->
  forall sb, Forall2 (conv sg) (subst_tele sb Ts) (subst_tele sb Ts').
Proof.
  intros sg Ts Ts' H. induction H as [|T T' Ts Ts' HT _ IH]; intros sb; cbn [subst_tele]; constructor.
  - apply conv_subst, HT.
  - apply IH.
Qed.
