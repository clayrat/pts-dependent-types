(** * Confluence of reduction

    [red1] of PTS.Reduction is confluent, for every signature: two
    reducts of a term have a common reduct.  The proof is Takahashi's,
    by parallel reduction and complete development:
    - parallel reduction [t ⇉ u] contracts any set of the redexes of
      [t] at once, and reduces inside the subterms of a contracted
      redex too; it lies between one step and many
      ([red1_par], [par_red]);
    - it is stable under substitution ([par_subst]);
    - the complete development [rho t] contracts every redex of [t];
      every parallel reduct of [t] reduces to [rho t] in one parallel
      step (the triangle, [par_triangle]), so parallel reduction has
      the diamond property, its closure is confluent, and so is [red],
      which is the same closure.

    The redexes of the kernel do not overlap: β, the annotations, the ι
    of the primitives and of the projections, δ, the ι of an instance
    and the unfolding of a [fix] on a full spine whose last argument is a
    constructor spine, and the ι of a match on a constructor spine.  The
    contractions on spines need two facts beyond the usual ones.  A
    spine that is not full, or whose head has no arity, has no redex at
    any of its applications, so its parallel reducts are spines of the
    same length ([par_spine]); constructor spines in particular stay
    constructor spines.  And a contraction of a spine commutes with the
    parallel reduction of its head and arguments ([spine_iota_par],
    [case_iota_par]): the redex survives, and the contracted terms are
    in parallel reduction.  A redex is recognized on the term before its
    parts are reduced, so the development contracts only the redexes of
    the term, not those its reduction creates.

    Injectivity of Π and Σ follows: a Π reduces only to a Π
    ([red_pi_inv]), and convertible terms have a common reduct
    ([church_rosser]). *)

From Stdlib Require Import Relations List Arith Lia Bool.
From Stdlib Require String.
Import ListNotations.
From DepTypes.Common Require Import Lists.
From DepTypes.PTS Require Import Syntax Telescope Signature Reduction SubstLaws.

Reserved Notation "t ⇉ u" (at level 70, no associativity).

Section Par.
Variable sg : signature.
Local Notation "t ⇝ u" := (red1 sg t u).
Local Notation "t ⇝* u" := (red sg t u).

(** ** Parallel reduction *)

Inductive par : term -> term -> Prop :=
(** every former, its subterms in parallel *)
| P_Srt : forall s, Srt s ⇉ Srt s
| P_Var : forall n, Var n ⇉ Var n
| P_Pi : forall A A' B B', A ⇉ A' -> B ⇉ B' -> Pi A B ⇉ Pi A' B'
| P_Lam : forall b b', b ⇉ b' -> Lam b ⇉ Lam b'
| P_App : forall f f' a a', f ⇉ f' -> a ⇉ a' -> App f a ⇉ App f' a'
| P_Ann : forall t t' A A', t ⇉ t' -> A ⇉ A' -> Ann t A ⇉ Ann t' A'
| P_Void : Void ⇉ Void
| P_ElimVoid : forall C C' e e', C ⇉ C' -> e ⇉ e' -> ElimVoid C e ⇉ ElimVoid C' e'
| P_Unit : Unit ⇉ Unit
| P_Tt : Tt ⇉ Tt
| P_ElimUnit : forall C C' c c' u u', C ⇉ C' -> c ⇉ c' -> u ⇉ u' -> ElimUnit C c u ⇉ ElimUnit C' c' u'
| P_Bool : Bool ⇉ Bool
| P_True : BTrue ⇉ BTrue
| P_False : BFalse ⇉ BFalse
| P_ElimBool : forall C C' x x' y y' b b', C ⇉ C' -> x ⇉ x' -> y ⇉ y' -> b ⇉ b' ->
    ElimBool C x y b ⇉ ElimBool C' x' y' b'
| P_Sigma : forall A A' B B', A ⇉ A' -> B ⇉ B' -> Sigma A B ⇉ Sigma A' B'
| P_Pair : forall a a' b b', a ⇉ a' -> b ⇉ b' -> Pair a b ⇉ Pair a' b'
| P_Fst : forall p p', p ⇉ p' -> Fst p ⇉ Fst p'
| P_Snd : forall p p', p ⇉ p' -> Snd p ⇉ Snd p'
| P_Const : forall g, Const g ⇉ Const g
| P_Case : forall D s P P' x x' bs bs', P ⇉ P' -> x ⇉ x' -> pars bs bs' ->
    Case D s P x bs ⇉ Case D s P' x' bs'
| P_Fix : forall A A' k b b', A ⇉ A' -> b ⇉ b' -> Fix A k b ⇉ Fix A' k b'
(** the contractions, after their parts *)
| P_Beta : forall b b' a a', b ⇉ b' -> a ⇉ a' -> App (Lam b) a ⇉ subst1 b' a'
| P_AnnE : forall t t' A, t ⇉ t' -> Ann t A ⇉ t'
| P_UnitTt : forall C c c', c ⇉ c' -> ElimUnit C c Tt ⇉ c'
| P_BoolTrue : forall C x x' y, x ⇉ x' -> ElimBool C x y BTrue ⇉ x'
| P_BoolFalse : forall C x y y', y ⇉ y' -> ElimBool C x y BFalse ⇉ y'
| P_FstPair : forall a a' b, a ⇉ a' -> Fst (Pair a b) ⇉ a'
| P_SndPair : forall a b b', b ⇉ b' -> Snd (Pair a b) ⇉ b'
| P_Delta : forall g b, sig_delta sg g = Some b -> Const g ⇉ b
(** a redex of the term itself, contracted after its parts *)
| P_Spine : forall f f' a a' u, f ⇉ f' -> a ⇉ a' ->
    spine_iota sg (App f a) <> None -> spine_iota sg (App f' a') = Some u -> App f a ⇉ u
| P_CaseI : forall D s P P' x x' bs bs' u, P ⇉ P' -> x ⇉ x' -> pars bs bs' ->
    case_iota sg (Case D s P x bs) <> None -> case_iota sg (Case D s P' x' bs') = Some u ->
    Case D s P x bs ⇉ u
with pars : list term -> list term -> Prop :=
| PS_Nil : pars [] []
| PS_Cons : forall t t' ts ts', t ⇉ t' -> pars ts ts' -> pars (t :: ts) (t' :: ts')
where "t ⇉ u" := (par t u).

Scheme par_mut := Induction for par Sort Prop
  with pars_mut := Induction for pars Sort Prop.
Combined Scheme par_pars_mut from par_mut, pars_mut.

(** ** Lists in parallel *)

Lemma pars_length : forall l l', pars l l' -> length l' = length l.
Proof. intros l l' H. induction H; cbn; congruence. Qed.

Lemma pars_app : forall l1 l1' l2 l2', pars l1 l1' -> pars l2 l2' -> pars (l1 ++ l2) (l1' ++ l2').
Proof. intros l1 l1' l2 l2' H1 H2. induction H1; cbn; [exact H2 | constructor; assumption]. Qed.

Lemma pars_firstn : forall n l l', pars l l' -> pars (firstn n l) (firstn n l').
Proof.
  induction n as [|n IH]; intros l l' H; [constructor | ].
  destruct H; cbn; constructor; [assumption | apply IH; assumption].
Qed.

Lemma pars_skipn : forall n l l', pars l l' -> pars (skipn n l) (skipn n l').
Proof.
  induction n as [|n IH]; intros l l' H; [exact H | ].
  destruct H; cbn; [constructor | apply IH; assumption].
Qed.

Lemma pars_rev : forall l l', pars l l' -> pars (rev l) (rev l').
Proof. intros l l' H. induction H; cbn; [constructor | apply pars_app; [assumption | repeat constructor; assumption]]. Qed.

Lemma pars_nth_error : forall l l' i t, pars l l' -> nth_error l i = Some t ->
  exists t', nth_error l' i = Some t' /\ t ⇉ t'.
Proof.
  intros l l' i t H. revert i. induction H as [|u u' us us' Hu _ IH]; intros i Hi.
  - destruct i; discriminate Hi.
  - destruct i as [|i]; cbn in Hi |- *; [injection Hi as <-; eauto | exact (IH i Hi)].
Qed.

Lemma pars_last : forall l l' d, pars l l' -> d ⇉ d -> last l d ⇉ last l' d.
Proof.
  intros l l' d H Hd. induction H as [|u u' us us' Hu Hs IH]; [exact Hd | ].
  destruct Hs; [exact Hu | exact IH].
Qed.

Lemma pars_map : forall (f g : term -> term) l, Forall (fun t => f t ⇉ g t) l -> pars (map f l) (map g l).
Proof. intros f g l H. induction H; constructor; assumption. Qed.

(** ** Reflexivity, and between one step and many *)

Lemma par_refl : forall t, t ⇉ t.
Proof.
  induction t using term_ind'; try (constructor; assumption).
  constructor; try assumption. rewrite <- (map_id l). apply pars_map. exact IHl.
Qed.

Lemma pars_refl : forall l, pars l l.
Proof. induction l; constructor; [apply par_refl | assumption]. Qed.

Local Hint Constructors par pars : par.
Local Hint Resolve par_refl pars_refl : par.

Lemma red1_par : forall t u, t ⇝ u -> t ⇉ u.
Proof.
  intros t u H. induction H; try solve [eauto 3 with par].
  all: lazymatch goal with
       | |- Case _ _ _ _ (_ ++ _ :: _) ⇉ _ =>
           constructor; [apply par_refl | apply par_refl | ];
           apply pars_app; [apply pars_refl | constructor; [assumption | apply pars_refl]]
       | H : spine_iota _ _ = Some _ |- _ =>
           destruct (spine_iota_app _ _ _ H) as (f & a & ->);
           eapply P_Spine; [apply par_refl | apply par_refl | rewrite H; discriminate | exact H]
       | H : case_iota _ _ = Some _ |- _ =>
           destruct (case_iota_case _ _ _ H) as (D & s & P & x & bs & ->);
           eapply P_CaseI; [apply par_refl | apply par_refl | apply pars_refl | rewrite H; discriminate | exact H]
       end.
Qed.

Lemma par_red_pars :
  (forall t u, t ⇉ u -> t ⇝* u) /\ (forall l l', pars l l' -> Forall2 (red sg) l l').
Proof.
  apply par_pars_mut; intros; try apply rt_refl.
  all: first
    [ solve [auto using red_pi, red_lam, red_app, red_ann, red_elim_void, red_elim_unit,
               red_elim_bool, red_sigma, red_pair, red_fst, red_snd, red_fix]
    | solve [apply red_case; assumption]
    | solve [constructor; assumption]
    | solve [apply rt_step; constructor; assumption]
    | solve [eapply rt_trans; [apply red_app; [apply red_lam; eassumption | eassumption] | apply rt_step, R_Beta]]
    | solve [eapply rt_trans; [apply red_app; eassumption | apply rt_step, R_Spine; eassumption]]
    | solve [eapply rt_trans; [apply red_case; eassumption | apply rt_step, R_Case; eassumption]]
    | solve [eapply rt_trans; [apply rt_step; constructor | eassumption]] ].
Qed.

Lemma par_red : forall t u, t ⇉ u -> t ⇝* u.
Proof. exact (proj1 par_red_pars). Qed.

(** ** Renaming and substitution *)

Lemma spine_iota_rename : forall r t u, spine_iota sg t = Some u -> spine_iota sg (rename r t) = Some (rename r u).
Proof. intros r t u H. rewrite !rename_as_subst. exact (spine_iota_subst _ _ _ _ H). Qed.

Lemma case_iota_rename : forall r t u, case_iota sg t = Some u -> case_iota sg (rename r t) = Some (rename r u).
Proof. intros r t u H. rewrite !rename_as_subst. exact (case_iota_subst _ _ _ _ H). Qed.

Lemma delta_closed_subst : forall g b sb, sig_delta sg g = Some b -> subst sb b = b.
Proof. intros g b sb H. exact (subst_closed sb b (sig_delta_closed _ _ _ H)). Qed.

Lemma delta_closed_rename : forall g b r, sig_delta sg g = Some b -> rename r b = b.
Proof. intros g b r H. rewrite rename_as_subst. exact (delta_closed_subst g b _ H). Qed.

Lemma par_rename_pars :
  (forall t u, t ⇉ u -> forall r, rename r t ⇉ rename r u) /\
  (forall l l', pars l l' -> forall r, pars (map (rename r) l) (map (rename r) l')).
Proof.
  apply par_pars_mut; intros; cbn [rename map]; try (constructor; auto; fail).
  all: lazymatch goal with
       | |- App (Lam _) _ ⇉ rename _ (subst1 _ _) => rewrite rename_subst1; apply P_Beta; auto
       | e : sig_delta sg _ = Some _ |- _ => rewrite (delta_closed_rename _ _ r e); apply P_Delta; assumption
       | n : spine_iota sg (App ?f ?a) <> None, e : spine_iota sg (App ?f' ?a') = Some _ |- _ =>
           destruct (spine_iota sg (App f a)) as [v|] eqn:E; [ | contradiction];
           eapply P_Spine; [auto | auto | | ];
           [ change (App (rename r f) (rename r a)) with (rename r (App f a));
             rewrite (spine_iota_rename r _ _ E); discriminate
           | change (App (rename r f') (rename r a')) with (rename r (App f' a'));
             exact (spine_iota_rename r _ _ e) ]
       | n : case_iota sg (Case ?D ?s ?P ?x ?bs) <> None, e : case_iota sg (Case _ _ ?P' ?x' ?bs') = Some _ |- _ =>
           destruct (case_iota sg (Case D s P x bs)) as [v|] eqn:E; [ | contradiction];
           eapply P_CaseI; [auto | auto | auto | | ];
           [ change (Case D s (rename r P) (rename r x) (map (rename r) bs)) with (rename r (Case D s P x bs));
             rewrite (case_iota_rename r _ _ E); discriminate
           | change (Case D s (rename r P') (rename r x') (map (rename r) bs')) with (rename r (Case D s P' x' bs'));
             exact (case_iota_rename r _ _ e) ]
       end.
Qed.

Lemma par_rename : forall r t u, t ⇉ u -> rename r t ⇉ rename r u.
Proof. intros r t u H. exact (proj1 par_rename_pars t u H r). Qed.

Lemma par_lift : forall k t u, t ⇉ u -> lift k t ⇉ lift k u.
Proof. intros k t u H. exact (par_rename _ _ _ H). Qed.

Lemma par_up_sub : forall sb sb', (forall n, sb n ⇉ sb' n) -> forall n, up_sub sb n ⇉ up_sub sb' n.
Proof. intros sb sb' H [|n]; cbn; [apply par_refl | apply par_lift, H]. Qed.

Lemma par_subst_pars :
  (forall t u, t ⇉ u -> forall sb sb', (forall n, sb n ⇉ sb' n) -> subst sb t ⇉ subst sb' u) /\
  (forall l l', pars l l' -> forall sb sb', (forall n, sb n ⇉ sb' n) ->
     pars (map (subst sb) l) (map (subst sb') l')).
Proof.
  apply par_pars_mut; intros; cbn [subst map];
    try (constructor; auto using par_up_sub; fail); try solve [auto].
  all: lazymatch goal with
       | |- App (Lam _) _ ⇉ subst _ (subst1 _ _) => rewrite subst_subst1; apply P_Beta; auto using par_up_sub
       | e : sig_delta sg _ = Some _ |- _ => rewrite (delta_closed_subst _ _ sb' e); apply P_Delta; assumption
       | n : spine_iota sg (App ?f ?a) <> None, e : spine_iota sg (App ?f' ?a') = Some _ |- _ =>
           destruct (spine_iota sg (App f a)) as [v|] eqn:E; [ | contradiction];
           eapply P_Spine; [auto | auto | | ];
           [ change (App (subst sb f) (subst sb a)) with (subst sb (App f a));
             rewrite (spine_iota_subst _ _ _ sb E); discriminate
           | change (App (subst sb' f') (subst sb' a')) with (subst sb' (App f' a'));
             exact (spine_iota_subst _ _ _ sb' e) ]
       | n : case_iota sg (Case ?D ?s ?P ?x ?bs) <> None, e : case_iota sg (Case _ _ ?P' ?x' ?bs') = Some _ |- _ =>
           destruct (case_iota sg (Case D s P x bs)) as [v|] eqn:E; [ | contradiction];
           eapply P_CaseI; [auto | auto | auto | | ];
           [ change (Case D s (subst sb P) (subst sb x) (map (subst sb) bs)) with (subst sb (Case D s P x bs));
             rewrite (case_iota_subst _ _ _ sb E); discriminate
           | change (Case D s (subst sb' P') (subst sb' x') (map (subst sb') bs')) with (subst sb' (Case D s P' x' bs'));
             exact (case_iota_subst _ _ _ sb' e) ]
       end.
Qed.

Lemma par_subst : forall sb sb' t u, t ⇉ u -> (forall n, sb n ⇉ sb' n) -> subst sb t ⇉ subst sb' u.
Proof. intros sb sb' t u H Hs. exact (proj1 par_subst_pars t u H sb sb' Hs). Qed.

Lemma par_subst1 : forall b b' a a', b ⇉ b' -> a ⇉ a' -> subst1 b a ⇉ subst1 b' a'.
Proof.
  intros b b' a a' Hb Ha. apply par_subst; [exact Hb | ].
  intros [|n]; cbn; [exact Ha | apply par_refl].
Qed.

(** ** Spines *)

Lemma par_apps : forall l l' h h', h ⇉ h' -> pars l l' -> apps h l ⇉ apps h' l'.
Proof.
  intros l l' h h' Hh H. revert h h' Hh.
  induction H as [|t t' ts ts' Ht _ IH]; intros h h' Hh; [exact Hh | ].
  cbn [apps fold_left]. apply IH. constructor; assumption.
Qed.

Lemma par_lams : forall m b b', b ⇉ b' -> lams m b ⇉ lams m b'.
Proof. induction m as [|m IH]; intros b b' H; cbn; [exact H | constructor; apply IH, H]. Qed.

Lemma pars_map_rename : forall r l l', pars l l' -> pars (map (rename r) l) (map (rename r) l').
Proof. intros r l l' H. induction H; cbn; constructor; [apply par_rename | ]; assumption. Qed.

Lemma pars_nth : forall l l' i d, pars l l' -> d ⇉ d -> nth i l d ⇉ nth i l' d.
Proof.
  intros l l' i d H Hd. revert i. induction H as [|t t' ts ts' Ht _ IH]; intros i; [destruct i; exact Hd | ].
  destruct i; [exact Ht | apply IH].
Qed.

(** A spine with no redex at any of its applications: its head is no λ,
    and it is shorter than the arity of its head, if it has one. *)
Definition arity_below (t : term) : Prop :=
  match head_arity sg (spine_head t) with Some m => length (spine_args t) < m | None => True end.

Lemma par_spine : forall t t', t ⇉ t' -> (forall b, spine_head t <> Lam b) -> arity_below t ->
  exists h' args', t' = apps h' args' /\ spine_head t ⇉ h' /\ pars (spine_args t) args'.
Proof.
  induction t; intros t' H Hl Ha;
    try (exists t', []; split; [reflexivity | split; [exact H | constructor]]; fail).
  unfold arity_below in Ha. cbn [spine_head] in Hl, Ha. rewrite spine_args_App, length_app in Ha.
  inversion H; subst.
  - destruct (IHt1 f' H2 Hl) as (h' & args' & -> & Hh & Hs).
    { unfold arity_below. destruct (head_arity sg (spine_head t1)); [cbn in Ha; lia | exact I]. }
    exists h', (args' ++ [a']). split; [rewrite apps_snoc; reflexivity | ].
    split; [exact Hh | rewrite spine_args_App; apply pars_app; [exact Hs | repeat constructor; assumption]].
  - exfalso. exact (Hl b eq_refl).
  - exfalso. apply H4. rewrite spine_iota_head. cbn [spine_head]. rewrite spine_args_App, length_app.
    destruct (head_arity sg (spine_head t1)) as [m|]; [ | reflexivity].
    cbn [length] in Ha |- *. replace (Nat.eqb _ m) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.

(** A constructor spine reduces to a constructor spine of the same
    constructor. *)
Lemma par_ctor_spine : forall x x' D c, x ⇉ x' -> spine_head x = Const (Ctor D c) ->
  exists args', x' = apps (Const (Ctor D c)) args' /\ pars (spine_args x) args'.
Proof.
  intros x x' D c H Eh. destruct (par_spine x x' H) as (h' & args' & -> & Hh & Hs).
  - rewrite Eh. discriminate.
  - unfold arity_below. rewrite Eh. exact I.
  - rewrite Eh in Hh. inversion Hh; subst; [ | discriminate]. exists args'. split; [reflexivity | exact Hs].
Qed.

Lemma ctor_view_par : forall D d x x' i cd xs, ctor_view D d x = Some (i, cd, xs) -> x ⇉ x' ->
  exists xs', ctor_view D d x' = Some (i, cd, xs') /\ pars xs xs'.
Proof.
  intros D d x x' i cd xs E H.
  destruct (ctor_view_spec _ _ _ _ _ _ E) as (c & ps & -> & Ec & Hp & Hx).
  destruct (par_ctor_spine _ _ D c H) as (args' & -> & Hs).
  { rewrite spine_head_apps. reflexivity. }
  rewrite spine_args_apps in Hs. change (spine_args (Const (Ctor D c))) with (@nil term) in Hs.
  rewrite app_nil_l in Hs.
  pose proof (pars_length _ _ Hs) as Hl. rewrite length_app in Hl.
  exists (skipn (length ps) args'). split.
  - rewrite <- (firstn_skipn (length ps) args') at 1. apply ctor_view_apps; [exact Ec | | ].
    + rewrite length_firstn. lia.
    + rewrite length_skipn. lia.
  - pose proof (pars_skipn (length ps) _ _ Hs) as H'. rewrite skipn_app, skipn_all, Nat.sub_diag in H'.
    exact H'.
Qed.

Lemma par_hyp : forall D s pre pre' env env' Bs vs a a',
  pars pre pre' -> pars env env' -> a ⇉ a' -> hyp D s pre env Bs vs a ⇉ hyp D s pre' env' Bs vs a'.
Proof.
  intros D s pre pre' env env' Bs vs a a' Hp He Ha. unfold hyp. apply par_lams, par_apps; [apply par_refl | ].
  apply pars_app; [apply pars_map_rename, Hp | apply pars_app].
  - apply pars_map. apply Forall_forall. intros v _. apply par_subst; [apply par_refl | ].
    intros n. unfold inst. destruct (Nat.ltb n (length Bs)); [apply par_refl | ].
    apply par_lift, pars_nth; [exact He | apply par_refl].
  - repeat constructor. apply par_apps; [apply par_lift, Ha | apply pars_refl].
Qed.

Lemma pars_iota_args : forall D s pre pre' fs env env' xs xs',
  pars pre pre' -> pars env env' -> pars xs xs' ->
  pars (iota_args D s pre env fs xs) (iota_args D s pre' env' fs xs').
Proof.
  intros D s pre pre' fs. induction fs as [|fd fs IH]; intros env env' xs xs' Hp He Hx; [constructor | ].
  destruct Hx as [|a a' xs xs' Ha Hx]; [destruct fd; constructor | ].
  destruct fd as [A | Bs vs]; cbn [iota_args].
  - constructor; [exact Ha | apply IH; [exact Hp | constructor; assumption | exact Hx]].
  - constructor; [exact Ha | constructor; [apply par_hyp; assumption | ]].
    apply IH; [exact Hp | constructor; assumption | exact Hx].
Qed.

(** The head of a spine with an arity: an instance with active rules,
    which only reduces to itself, or a [fix]. *)
Lemma head_arity_cases : forall h m, head_arity sg h = Some m ->
  (exists D s d, h = Const (Elim D s) /\ elim_head sg h = Some (D, s, d)) \/
  (exists A k b, h = Fix A k b /\ elim_head sg h = None).
Proof.
  intros h m H. unfold head_arity in H. destruct (elim_head sg h) as [[[D s] d]|] eqn:E.
  - left. exists D, s, d. split; [ | reflexivity].
    destruct h; try discriminate E. destruct g; try discriminate E. unfold elim_head in E.
    destruct (sig_elim sg s0 s1) as [[? [|]]|]; destruct (sig_ind sg s0); try discriminate E.
    injection E as -> -> _. reflexivity.
  - right. destruct h; try discriminate H. exists h1, n, h2. split; reflexivity.
Qed.

Lemma head_iota_par : forall h h' args args' u,
  head_iota sg h args = Some u -> head_arity sg h <> None -> h ⇉ h' -> pars args args' ->
  spine_head h' = h' /\ head_arity sg h' = head_arity sg h /\
  exists u', head_iota sg h' args' = Some u' /\ u ⇉ u'.
Proof.
  intros h h' args args' u E Ha Hh Hs.
  destruct (head_arity sg h) as [m|] eqn:Em; [ | contradiction].
  destruct (head_arity_cases h m Em) as [(D & s & d & -> & Ee) | (A & k & b & -> & Ee)].
  - inversion Hh; subst; [ | discriminate]. split; [reflexivity | split; [exact Em | ]].
    unfold head_iota in E |- *. rewrite Ee in E |- *. unfold iota_at in E |- *.
    destruct (ctor_view D d (last args (Var 0))) as [[[i cd] xs]|] eqn:Ev; [ | discriminate E].
    destruct (ctor_view_par _ _ _ _ _ _ _ Ev (pars_last _ _ _ Hs (par_refl _))) as (xs' & Ev' & Hx).
    rewrite Ev'.
    destruct (nth_error _ i) as [mt|] eqn:En; [ | discriminate E]. injection E as <-.
    destruct (pars_nth_error _ _ _ _ (pars_firstn _ _ _ (pars_skipn _ _ _ Hs)) En) as (mt' & En' & Hm).
    rewrite En'. eexists. split; [reflexivity | ].
    apply par_apps; [exact Hm | apply pars_iota_args; [exact (pars_firstn (S (length (ind_params d)) + length (ind_ctors d)) _ _ Hs) | | exact Hx]].
    rewrite !rev'_rev. apply pars_rev, pars_firstn, Hs.
  - inversion Hh; subst. split; [reflexivity | split; [rewrite <- Em; reflexivity | ]].
    unfold head_iota in E |- *. cbn [elim_head] in E |- *. unfold fix_at in E |- *.
    destruct (spine_head (last args (Var 0))) eqn:Eh; try discriminate E. destruct g as [ | D c | | ]; try discriminate E.
    injection E as <-.
    destruct (par_ctor_spine _ _ D c (pars_last _ _ _ Hs (par_refl _)) Eh) as (xa & -> & _).
    rewrite spine_head_apps. cbn [spine_head]. eexists. split; [reflexivity | ].
    apply par_apps; [ | exact Hs]. apply par_subst1; [assumption | constructor; assumption].
Qed.

(** The contraction of a spine commutes with the parallel reduction of
    its parts: the redex survives, and the contractions are in parallel
    reduction. *)
Lemma spine_iota_par : forall f a u f' a', spine_iota sg (App f a) = Some u -> f ⇉ f' -> a ⇉ a' ->
  exists u', spine_iota sg (App f' a') = Some u' /\ u ⇉ u'.
Proof.
  intros f a u f' a' E Hf Ha. rewrite spine_iota_head in E. cbn [spine_head] in E.
  rewrite spine_args_App in E.
  destruct (head_arity sg (spine_head f)) as [m|] eqn:Em; [ | discriminate E].
  destruct (Nat.eqb _ m) eqn:El; [ | discriminate E]. apply Nat.eqb_eq in El. rewrite length_app in El.
  destruct (par_spine f f' Hf) as (h' & args' & -> & Hh & Hs).
  { intros b Eb. rewrite Eb in Em. discriminate Em. }
  { unfold arity_below. rewrite Em. cbn in El. lia. }
  assert (Hs' : pars (spine_args f ++ [a]) (args' ++ [a'])) by (apply pars_app; [exact Hs | repeat constructor; exact Ha]).
  destruct (head_iota_par _ _ _ _ _ E ltac:(rewrite Em; discriminate) Hh Hs') as (Eh' & Ea & u' & E' & Hu).
  exists u'. split; [ | exact Hu].
  rewrite spine_iota_head, <- apps_snoc, spine_head_apps, spine_args_apps, Eh', (spine_head_args _ Eh'), app_nil_l.
  rewrite Ea, Em, length_app, (pars_length _ _ Hs). cbn in El |- *.
  replace (Nat.eqb _ m) with true by (symmetry; apply Nat.eqb_eq; lia). exact E'.
Qed.

Lemma case_iota_par : forall D s P P' x x' bs bs' u, case_iota sg (Case D s P x bs) = Some u ->
  P ⇉ P' -> x ⇉ x' -> pars bs bs' -> exists u', case_iota sg (Case D s P' x' bs') = Some u' /\ u ⇉ u'.
Proof.
  intros D s P P' x x' bs bs' u E HP Hx Hb. unfold case_iota in E |- *.
  destruct (sig_ind sg D) as [d|]; [ | discriminate E].
  destruct (ctor_view D d x) as [[[i cd] xs]|] eqn:Ev; [ | discriminate E].
  destruct (ctor_view_par _ _ _ _ _ _ _ Ev Hx) as (xs' & -> & Hxs).
  destruct (nth_error bs i) as [b|] eqn:En; [ | discriminate E]. injection E as <-.
  destruct (pars_nth_error _ _ _ _ Hb En) as (b' & -> & Hb'). eexists. split; [reflexivity | ].
  apply par_apps; assumption.
Qed.

(** ** Complete development

    Every redex of the term contracted, after its parts.  A redex is
    recognized on the term itself; the contraction is taken of the
    developed parts, where it survives ([spine_iota_par],
    [case_iota_par]). *)

Fixpoint rho (t : term) : term :=
  match t with
  | Srt s => Srt s
  | Var n => Var n
  | Pi A B => Pi (rho A) (rho B)
  | Lam b => Lam (rho b)
  | App f a =>
      match spine_iota sg (App f a) with
      | Some _ =>
          match spine_iota sg (App (rho f) (rho a)) with
          | Some u => u
          | None => App (rho f) (rho a)
          end
      | None =>
          match f with
          | Lam b => subst1 (rho b) (rho a)
          | _ => App (rho f) (rho a)
          end
      end
  | Ann u _ => rho u
  | Void => Void
  | ElimVoid C e => ElimVoid (rho C) (rho e)
  | Unit => Unit
  | Tt => Tt
  | ElimUnit C c u =>
      match u with
      | Tt => rho c
      | _ => ElimUnit (rho C) (rho c) (rho u)
      end
  | Bool => Bool
  | BTrue => BTrue
  | BFalse => BFalse
  | ElimBool C x y b =>
      match b with
      | BTrue => rho x
      | BFalse => rho y
      | _ => ElimBool (rho C) (rho x) (rho y) (rho b)
      end
  | Sigma A B => Sigma (rho A) (rho B)
  | Pair a b => Pair (rho a) (rho b)
  | Fst p =>
      match p with
      | Pair a _ => rho a
      | _ => Fst (rho p)
      end
  | Snd p =>
      match p with
      | Pair _ b => rho b
      | _ => Snd (rho p)
      end
  | Const g =>
      match sig_delta sg g with
      | Some b => b
      | None => Const g
      end
  | Case D s P x bs =>
      match case_iota sg (Case D s P x bs) with
      | Some _ =>
          match case_iota sg (Case D s (rho P) (rho x) (map rho bs)) with
          | Some u => u
          | None => Case D s (rho P) (rho x) (map rho bs)
          end
      | None => Case D s (rho P) (rho x) (map rho bs)
      end
  | Fix A k b => Fix (rho A) k (rho b)
  end.

Lemma par_lam_inv : forall b t, Lam b ⇉ t -> exists b', t = Lam b' /\ b ⇉ b'.
Proof. intros b t H. inversion H; subst. eauto. Qed.

Lemma par_pair_inv : forall a b t, Pair a b ⇉ t -> exists a' b', t = Pair a' b' /\ a ⇉ a' /\ b ⇉ b'.
Proof. intros a b t H. inversion H; subst. eauto. Qed.

(** Every term reduces in parallel to its development. *)
Lemma par_rho : forall t, t ⇉ rho t.
Proof.
  induction t using term_ind'; cbn [rho].
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - (* application *)
    destruct (spine_iota sg (App t1 t2)) as [v|] eqn:E.
    + destruct (spine_iota_par _ _ _ _ _ E IHt1 IHt2) as (u & Eu & _). rewrite Eu.
      eapply P_Spine; [exact IHt1 | exact IHt2 | rewrite E; discriminate | exact Eu].
    + destruct t1; try (constructor; assumption).
      destruct (par_lam_inv _ _ IHt1) as (b' & Eb & Hb). injection Eb as <-.
      apply P_Beta; assumption.
  - apply P_AnnE. assumption.
  - constructor.
  - constructor; assumption.
  - constructor.
  - constructor.
  - destruct t3; constructor; assumption.
  - constructor.
  - constructor.
  - constructor.
  - destruct t4; constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - destruct t; try (constructor; assumption).
    destruct (par_pair_inv _ _ _ IHt) as (a' & b' & E & Ha & _). injection E as <- <-.
    apply P_FstPair. assumption.
  - destruct t; try (constructor; assumption).
    destruct (par_pair_inv _ _ _ IHt) as (a' & b' & E & _ & Hb). injection E as <- <-.
    apply P_SndPair. assumption.
  - destruct (sig_delta sg g) eqn:E; [apply P_Delta; exact E | constructor].
  - (* match *)
    assert (Hl : pars l (map rho l)) by (rewrite <- (map_id l) at 1; apply pars_map; exact IHl).
    destruct (case_iota sg (Case D s t1 t2 l)) as [v|] eqn:E.
    + destruct (case_iota_par _ _ _ _ _ _ _ _ _ E IHt1 IHt2 Hl) as (u & Eu & _). rewrite Eu.
      eapply P_CaseI; [exact IHt1 | exact IHt2 | exact Hl | rewrite E; discriminate | exact Eu].
    + constructor; assumption.
  - constructor; assumption.
Qed.

Lemma pars_rho : forall l, pars l (map rho l).
Proof. intros l. rewrite <- (map_id l) at 1. apply pars_map, Forall_forall. intros t _. apply par_rho. Qed.

(** The triangle: a parallel reduct reduces in parallel to the
    development. *)
Lemma par_triangle_pars :
  (forall t u, t ⇉ u -> u ⇉ rho t) /\ (forall l l', pars l l' -> pars l' (map rho l)).
Proof.
  apply par_pars_mut; cbn [rho map].
  - intros. constructor.
  - intros. constructor.
  - intros. constructor; assumption.
  - intros. constructor; assumption.
  - (* application *)
    intros f f' a a' Hf IHf Ha IHa.
    destruct (spine_iota sg (App f a)) as [v|] eqn:E.
    + destruct (spine_iota_par _ _ _ _ _ E (par_rho f) (par_rho a)) as (w & Ew & _). rewrite Ew.
      destruct (spine_iota_par _ _ _ _ _ E Hf Ha) as (u1 & E1 & _).
      eapply P_Spine; [exact IHf | exact IHa | rewrite E1; discriminate | exact Ew].
    + destruct f; try (constructor; assumption).
      destruct (par_lam_inv _ _ Hf) as (b' & -> & _).
      destruct (par_lam_inv _ _ IHf) as (b'' & Eb & Hb). injection Eb as <-.
      apply P_Beta; assumption.
  - intros. apply P_AnnE. assumption.
  - intros. constructor.
  - intros. constructor; assumption.
  - intros. constructor.
  - intros. constructor.
  - intros C C' c c' u u' HC IHC Hc IHc Hu IHu.
    destruct u; try (constructor; assumption). inversion Hu; subst. apply P_UnitTt. assumption.
  - intros. constructor.
  - intros. constructor.
  - intros. constructor.
  - intros C C' x x' y y' b b' HC IHC Hx IHx Hy IHy Hb IHb.
    destruct b; try (constructor; assumption).
    + inversion Hb; subst. apply P_BoolTrue. assumption.
    + inversion Hb; subst. apply P_BoolFalse. assumption.
  - intros. constructor; assumption.
  - intros. constructor; assumption.
  - intros p p' Hp IHp. destruct p; try (constructor; assumption).
    destruct (par_pair_inv _ _ _ Hp) as (a' & b' & -> & _ & _).
    destruct (par_pair_inv _ _ _ IHp) as (a'' & b'' & E & Ha & _). injection E as <- <-.
    apply P_FstPair. assumption.
  - intros p p' Hp IHp. destruct p; try (constructor; assumption).
    destruct (par_pair_inv _ _ _ Hp) as (a' & b' & -> & _ & _).
    destruct (par_pair_inv _ _ _ IHp) as (a'' & b'' & E & _ & Hb). injection E as <- <-.
    apply P_SndPair. assumption.
  - intros g. destruct (sig_delta sg g) eqn:E; [apply P_Delta; exact E | constructor].
  - (* match *)
    intros D s P P' x x' bs bs' HP IHP Hx IHx Hb IHb.
    destruct (case_iota sg (Case D s P x bs)) as [v|] eqn:E.
    + destruct (case_iota_par _ _ _ _ _ _ _ _ _ E (par_rho P) (par_rho x) (pars_rho bs)) as (w & Ew & _).
      rewrite Ew. destruct (case_iota_par _ _ _ _ _ _ _ _ _ E HP Hx Hb) as (u1 & E1 & _).
      eapply P_CaseI; [exact IHP | exact IHx | exact IHb | rewrite E1; discriminate | exact Ew].
    + constructor; assumption.
  - intros. constructor; assumption.
  - (* β *)
    intros b b' a a' Hb IHb Ha IHa. rewrite spine_iota_lam. apply par_subst1; assumption.
  - intros. assumption.
  - intros. assumption.
  - intros. assumption.
  - intros. assumption.
  - intros. assumption.
  - intros. assumption.
  - intros g b e. rewrite e. apply par_refl.
  - (* a redex of a spine *)
    intros f f' a a' u Hf IHf Ha IHa n e.
    destruct (spine_iota sg (App f a)) as [v|] eqn:E; [ | contradiction].
    destruct (spine_iota_par _ _ _ _ _ E (par_rho f) (par_rho a)) as (w & Ew & _). rewrite Ew.
    destruct (spine_iota_par _ _ _ _ _ e IHf IHa) as (w' & Ew' & Hu).
    rewrite Ew in Ew'. injection Ew' as <-. exact Hu.
  - (* a redex of a match *)
    intros D s P P' x x' bs bs' u HP IHP Hx IHx Hb IHb n e.
    destruct (case_iota sg (Case D s P x bs)) as [v|] eqn:E; [ | contradiction].
    destruct (case_iota_par _ _ _ _ _ _ _ _ _ E (par_rho P) (par_rho x) (pars_rho bs)) as (w & Ew & _).
    rewrite Ew. destruct (case_iota_par _ _ _ _ _ _ _ _ _ e IHP IHx IHb) as (w' & Ew' & Hu).
    rewrite Ew in Ew'. injection Ew' as <-. exact Hu.
  - constructor.
  - intros. constructor; assumption.
Qed.

Lemma par_triangle : forall t u, t ⇉ u -> u ⇉ rho t.
Proof. exact (proj1 par_triangle_pars). Qed.

Lemma par_diamond : forall t u v, t ⇉ u -> t ⇉ v -> exists w, u ⇉ w /\ v ⇉ w.
Proof. intros t u v Hu Hv. exists (rho t). split; apply par_triangle; assumption. Qed.

(** ** Confluence *)

Local Notation "t ⇉* u" := (clos_refl_trans term par t u) (at level 70).

Lemma par_strip : forall t u v, t ⇉ u -> t ⇉* v -> exists w, u ⇉* w /\ v ⇉ w.
Proof.
  intros t u v Hu Hv. revert u Hu. induction Hv as [t v Hv | t | t m v _ IH1 _ IH2]; intros u Hu.
  - destruct (par_diamond _ _ _ Hu Hv) as (w & Hw1 & Hw2). exists w. split; [apply rt_step | ]; assumption.
  - exists u. split; [apply rt_refl | exact Hu].
  - destruct (IH1 u Hu) as (w1 & Hw1 & Hm). destruct (IH2 w1 Hm) as (w2 & Hw2 & Hv).
    exists w2. split; [eapply rt_trans; eassumption | exact Hv].
Qed.

Lemma par_star_confluent : forall t u v, t ⇉* u -> t ⇉* v -> exists w, u ⇉* w /\ v ⇉* w.
Proof.
  intros t u v Hu. revert v. induction Hu as [t u Hu | t | t m u _ IH1 _ IH2]; intros v Hv.
  - destruct (par_strip _ _ _ Hu Hv) as (w & Hw1 & Hw2). exists w. split; [exact Hw1 | apply rt_step, Hw2].
  - exists v. split; [exact Hv | apply rt_refl].
  - destruct (IH1 v Hv) as (w1 & Hm & Hv1). destruct (IH2 w1 Hm) as (w2 & Hu2 & Hw2).
    exists w2. split; [exact Hu2 | eapply rt_trans; eassumption].
Qed.

Lemma red_par_star : forall t u, t ⇝* u -> t ⇉* u.
Proof.
  intros t u H. induction H; [apply rt_step, red1_par; assumption | apply rt_refl | eapply rt_trans; eassumption].
Qed.

Lemma par_star_red : forall t u, t ⇉* u -> t ⇝* u.
Proof.
  intros t u H. induction H; [apply par_red; assumption | apply rt_refl | eapply rt_trans; eassumption].
Qed.

Theorem red_confluent : forall t u v, t ⇝* u -> t ⇝* v -> exists w, u ⇝* w /\ v ⇝* w.
Proof.
  intros t u v Hu Hv.
  destruct (par_star_confluent _ _ _ (red_par_star _ _ Hu) (red_par_star _ _ Hv)) as (w & H1 & H2).
  exists w. split; apply par_star_red; assumption.
Qed.

(** Convertible terms have a common reduct. *)
Theorem church_rosser : forall t u, conv sg t u -> exists w, t ⇝* w /\ u ⇝* w.
Proof.
  intros t u H. induction H as [t u H | t | t u _ IH | t m u _ IH1 _ IH2].
  - exists u. split; [apply rt_step, H | apply rt_refl].
  - exists t. split; apply rt_refl.
  - destruct IH as (w & H1 & H2). exists w. split; assumption.
  - destruct IH1 as (w1 & Ht & Hm1). destruct IH2 as (w2 & Hm2 & Hu).
    destruct (red_confluent _ _ _ Hm1 Hm2) as (w & Hw1 & Hw2).
    exists w. split; eapply rt_trans; eassumption.
Qed.

(** ** Injectivity of Π and Σ *)

(** A Π reduces only inside: it has no contraction at its root. *)
Lemma red_pi_inv : forall A B t, Pi A B ⇝* t -> exists A' B', t = Pi A' B' /\ A ⇝* A' /\ B ⇝* B'.
Proof.
  intros A B t H. remember (Pi A B) as p eqn:Ep. revert A B Ep.
  induction H as [p t H | p | p m t _ IH1 _ IH2]; intros A B Ep; subst.
  - inversion H; subst.
    + exists A', B. split; [reflexivity | split; [apply rt_step; assumption | apply rt_refl]].
    + exists A, B'. split; [reflexivity | split; [apply rt_refl | apply rt_step; assumption]].
    + destruct (spine_iota_app _ _ _ H0) as (f & a & E). discriminate E.
    + destruct (case_iota_case _ _ _ H0) as (D & s & P & x & bs & E). discriminate E.
  - exists A, B. split; [reflexivity | split; apply rt_refl].
  - destruct (IH1 A B eq_refl) as (A1 & B1 & -> & HA1 & HB1).
    destruct (IH2 A1 B1 eq_refl) as (A2 & B2 & -> & HA2 & HB2).
    exists A2, B2. split; [reflexivity | split; eapply rt_trans; eassumption].
Qed.

Lemma red_sigma_inv : forall A B t, Sigma A B ⇝* t -> exists A' B', t = Sigma A' B' /\ A ⇝* A' /\ B ⇝* B'.
Proof.
  intros A B t H. remember (Sigma A B) as p eqn:Ep. revert A B Ep.
  induction H as [p t H | p | p m t _ IH1 _ IH2]; intros A B Ep; subst.
  - inversion H; subst.
    + exists A', B. split; [reflexivity | split; [apply rt_step; assumption | apply rt_refl]].
    + exists A, B'. split; [reflexivity | split; [apply rt_refl | apply rt_step; assumption]].
    + destruct (spine_iota_app _ _ _ H0) as (f & a & E). discriminate E.
    + destruct (case_iota_case _ _ _ H0) as (D & s & P & x & bs & E). discriminate E.
  - exists A, B. split; [reflexivity | split; apply rt_refl].
  - destruct (IH1 A B eq_refl) as (A1 & B1 & -> & HA1 & HB1).
    destruct (IH2 A1 B1 eq_refl) as (A2 & B2 & -> & HA2 & HB2).
    exists A2, B2. split; [reflexivity | split; eapply rt_trans; eassumption].
Qed.

Lemma conv_common : forall t u w, t ⇝* w -> u ⇝* w -> conv sg t u.
Proof. intros t u w Ht Hu. eapply conv_trans; [apply red_conv, Ht | apply conv_sym, red_conv, Hu]. Qed.

Theorem pi_inj : forall A B A' B', conv sg (Pi A B) (Pi A' B') -> conv sg A A' /\ conv sg B B'.
Proof.
  intros A B A' B' H. destruct (church_rosser _ _ H) as (w & H1 & H2).
  destruct (red_pi_inv _ _ _ H1) as (A1 & B1 & -> & HA & HB).
  destruct (red_pi_inv _ _ _ H2) as (A2 & B2 & E & HA' & HB'). injection E as <- <-.
  split; eapply conv_common; eassumption.
Qed.

Theorem sigma_inj : forall A B A' B', conv sg (Sigma A B) (Sigma A' B') -> conv sg A A' /\ conv sg B B'.
Proof.
  intros A B A' B' H. destruct (church_rosser _ _ H) as (w & H1 & H2).
  destruct (red_sigma_inv _ _ _ H1) as (A1 & B1 & -> & HA & HB).
  destruct (red_sigma_inv _ _ _ H2) as (A2 & B2 & E & HA' & HB'). injection E as <- <-.
  split; eapply conv_common; eassumption.
Qed.

End Par.

(** ** Spines of a family, and convertible arguments *)

Lemma pars_forall2_red : forall sg l l', pars sg l l' -> Forall2 (red sg) l l'.
Proof. intros sg l l' H. induction H; constructor; [apply par_red; assumption | assumption]. Qed.

(** A family has no contraction, applied or not. *)
Lemma red_ind_spine : forall sg D l w, red sg (apps (Const (Ind D)) l) w ->
  exists l', w = apps (Const (Ind D)) l' /\ Forall2 (red sg) l l'.
Proof.
  intros sg D l w H. remember (apps (Const (Ind D)) l) as t eqn:Et. revert l Et.
  induction H as [t u H | t | t u v _ IH1 _ IH2]; intros l Et; subst.
  - apply red1_par in H.
    destruct (par_spine sg _ _ H) as (h' & args' & -> & Hh & Hs).
    + intros b. rewrite spine_head_apps. discriminate.
    + unfold arity_below. rewrite spine_head_apps. exact I.
    + rewrite spine_head_apps in Hh. cbn [spine_head] in Hh. rewrite spine_args_apps in Hs.
      inversion Hh; subst.
      * exists args'. split; [reflexivity | apply pars_forall2_red; exact Hs].
      * match goal with Hd : sig_delta _ _ = Some _ |- _ => discriminate Hd end.
  - exists l. split; [reflexivity | apply red_list_refl].
  - destruct (IH1 l eq_refl) as (l1 & -> & H1). destruct (IH2 l1 eq_refl) as (l2 & -> & H2).
    exists l2. split; [reflexivity | eapply forall2_red_trans; eassumption].
Qed.

Theorem conv_ind_spine : forall sg D l l',
  conv sg (apps (Const (Ind D)) l) (apps (Const (Ind D)) l') -> Forall2 (conv sg) l l'.
Proof.
  intros sg D l l' H. destruct (church_rosser sg _ _ H) as (w & H1 & H2).
  destruct (red_ind_spine sg D l w H1) as (l1 & -> & R1).
  destruct (red_ind_spine sg D l' _ H2) as (l2 & E & R2). apply apps_const_inj in E. subst l2.
  clear H H1 H2. revert l' R2.
  induction R1 as [|x y xs ys Hxy _ IH]; intros l' R2; inversion R2; subst; constructor.
  - eapply conv_common; eassumption.
  - apply IH. assumption.
Qed.

(** Convertible lists have a common list of reducts. *)
Lemma common_reducts : forall sg l l', Forall2 (conv sg) l l' ->
  exists ws, Forall2 (red sg) l ws /\ Forall2 (red sg) l' ws.
Proof.
  intros sg l l' H. induction H as [|a a' l l' Ha _ (ws & H1 & H2)]; [exists []; split; constructor | ].
  destruct (church_rosser sg _ _ Ha) as (w & Hw1 & Hw2).
  exists (w :: ws). split; constructor; assumption.
Qed.

Lemma red_tsub : forall sg l ws, Forall2 (red sg) l ws -> forall i, red sg (tsub l i) (tsub ws i).
Proof.
  intros sg l ws H i. pose proof (Forall2_length H) as Hl. unfold tsub. rewrite Hl.
  destruct (Nat.lt_ge_cases i (length l)) as [Hi | Hi].
  - apply forall2_nth; [apply forall2_rev, H | rewrite length_rev; exact Hi].
  - rewrite !nth_overflow by (rewrite length_rev; lia). apply rt_refl.
Qed.

(** Substituting convertible arguments gives convertible terms. *)
Lemma conv_subst_tsub : forall sg l l', Forall2 (conv sg) l l' ->
  forall m t, conv sg (subst (upn m (tsub l)) t) (subst (upn m (tsub l')) t).
Proof.
  intros sg l l' H m t. destruct (common_reducts sg l l' H) as (ws & H1 & H2).
  apply (conv_common sg _ _ (subst (upn m (tsub ws)) t)); apply red_subst_pointwise; apply red_upn;
    apply red_tsub; assumption.
Qed.

Lemma forall2_conv_subst_tsub : forall sg n l l' ts, Forall2 (conv sg) l l' ->
  Forall2 (conv sg) (map (subst (upn n (tsub l))) ts) (map (subst (upn n (tsub l'))) ts).
Proof. intros sg n l l' ts H. apply forall2_conv_map. intros v. apply conv_subst_tsub, H. Qed.

Lemma conv_subst_tele_tsub : forall sg l l', Forall2 (conv sg) l l' ->
  forall Ts m, Forall2 (conv sg) (subst_tele (upn m (tsub l)) Ts) (subst_tele (upn m (tsub l')) Ts).
Proof.
  intros sg l l' H Ts. induction Ts as [|T Ts IH]; intros m; cbn [subst_tele]; constructor.
  - apply conv_subst_tsub, H.
  - exact (IH (S m)).
Qed.

(** ** The structural argument of a [fix] under reduction *)

Lemma red_pi_shape : forall sg A T B A', red sg A (Pi T B) -> red sg A A' ->
  exists T' B', red sg A' (Pi T' B') /\ red sg T T' /\ red sg B B'.
Proof.
  intros sg A T B A' H1 H2. destruct (red_confluent sg _ _ _ H1 H2) as (w & Hw1 & Hw2).
  destruct (red_pi_inv sg _ _ _ Hw1) as (T' & B' & -> & HT & HB). exists T', B'. auto.
Qed.

Theorem struct_arg_red : forall sg A k D, struct_arg sg A k D -> forall A', red sg A A' ->
  struct_arg sg A' k D.
Proof.
  intros sg A k D H. induction H as [A T B D us HA HT | A T B k D HA H IH]; intros A' HA'.
  - destruct (red_pi_shape sg _ _ _ _ HA HA') as (T' & B' & H1 & H2 & _).
    destruct (red_confluent sg _ _ _ HT H2) as (w & Hw1 & Hw2).
    destruct (red_ind_spine sg D us w Hw1) as (us' & -> & _).
    exact (SA_Here sg A' T' B' D us' H1 Hw2).
  - destruct (red_pi_shape sg _ _ _ _ HA HA') as (T' & B' & H1 & _ & H3).
    exact (SA_Next sg A' T' B' k D H1 (IH B' H3)).
Qed.
