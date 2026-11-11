(** * Values of the source evaluator and their canonical forms

    [vvalue sg v]: the shape of the values [eval_nested] of PTS.EvalSrc
    reaches ([eval_nested_vvalue]): no variable, annotation, match,
    projection or eliminator of a primitive at the head; an application
    is a spine its head cannot reduce yet, a constant has no body.

    The canonical forms of closed values ([value_shape]): a value whose
    type reduces to Bool is a boolean, to Unit [tt], to a Σ a pair, to
    a family a constructor of it applied to all its arguments.  Every
    other value has a type convertible to a Π (a λ, a [fix], a partial
    application of a constructor, an instance or a [fix]) or to a sort
    (a type).  Types are compared by the shape of the head of their
    reducts ([shape_of]), which reduction keeps: uniqueness of types,
    which fails for the unannotated λ, is not needed.

    The types of the instances of eliminators are read off the
    signature, so they are asked to be telescopes of the arity of their
    eliminator ([instances_shaped]): with any other type a partial
    application of an instance could have the type of data.  The
    instances a registration generates are so (Checked/Shaped.v of
    elim-inductive-types). *)

From Stdlib Require Import String List Bool Arith Lia Relations.
Import ListNotations.
From DepTypes.Common Require Import Outcome.
From DepTypes.PTS Require Import Syntax Telescope Spec Signature Reduction SubstLaws Confluence Guard GuardSubst
  Typing Inversion SubjectRed EvalSrc.

Local Open Scope list_scope.

(** ** Values of the source evaluator *)

Fixpoint vvalue (sg : signature) (t : term) : Prop :=
  match t with
  | App f a => spine_value sg t = true /\ vvalue sg f /\ vvalue sg a
  | Pair a b => vvalue sg a /\ vvalue sg b
  | Const g => sig_delta sg g = None
  | Var _ | Ann _ _ | Case _ _ _ _ _ | Fst _ | Snd _ | ElimVoid _ _ | ElimUnit _ _ _ | ElimBool _ _ _ _ => False
  | _ => True
  end.

Lemma eval_nested_vvalue : forall sg n t v, eval_nested sg n t = CbvValue v -> vvalue sg v.
Proof.
  intros sg. induction n as [|n IH]; intros t v H; [discriminate H | ].
  cbn [eval_nested] in H. destruct t; cbn [eval_node] in H.
  all: try (injection H as <-; exact I).
  all: try discriminate H.
  (* an application *)
  - unfold nested_app in H.
    destruct (eval_nested sg n t1) as [vf|uf|] eqn:Ef; try discriminate H.
    destruct (eval_nested sg n t2) as [va|ua|] eqn:Ea; try discriminate H.
    unfold nested_apply in H. destruct vf; try exact (IH _ _ H).
    all: destruct (spine_iota sg _); [exact (IH _ _ H) | ].
    all: destruct (spine_value sg _) eqn:Hsv; [injection H as <- | discriminate H].
    all: split; [exact Hsv | split; [exact (IH _ _ Ef) | exact (IH _ _ Ea)]].
  - exact (IH _ _ H).
  - destruct (eval_nested sg n t2); discriminate H.
  - destruct (eval_nested sg n t3) as [vu|uu|]; try discriminate H.
    destruct vu; try discriminate H. exact (IH _ _ H).
  - destruct (eval_nested sg n t4) as [vb|ub|]; try discriminate H.
    destruct vb; try discriminate H; exact (IH _ _ H).
  - destruct (eval_nested sg n t1) as [va|ua|] eqn:Ea; try discriminate H.
    destruct (eval_nested sg n t2) as [vb|ub|] eqn:Eb; try discriminate H.
    injection H as <-. split; [exact (IH _ _ Ea) | exact (IH _ _ Eb)].
  - destruct (eval_nested sg n t) as [vp|up|] eqn:Ep; try discriminate H.
    destruct vp; try discriminate H. injection H as <-. exact (proj1 (IH _ _ Ep)).
  - destruct (eval_nested sg n t) as [vp|up|] eqn:Ep; try discriminate H.
    destruct vp; try discriminate H. injection H as <-. exact (proj2 (IH _ _ Ep)).
  - destruct (sig_delta sg g) eqn:Ed; [exact (IH _ _ H) | injection H as <-; exact Ed].
  - destruct (eval_nested sg n t2) as [vx|ux|]; try discriminate H.
    destruct (case_iota sg _); [exact (IH _ _ H) | discriminate H].
Qed.

(** ** The shape of the head of a type *)

Inductive shape : Type := SSrt | SPi | SSigma | SUnit | SBool | SVoid | SInd (D : string).

Definition shape_of (t : term) : option shape :=
  match spine_head t with
  | Srt _ => Some SSrt
  | Pi _ _ => Some SPi
  | Sigma _ _ => Some SSigma
  | Unit => Some SUnit
  | Bool => Some SBool
  | Void => Some SVoid
  | Const (Ind D) => Some (SInd D)
  | _ => None
  end.

Lemma shape_of_apps_ind : forall D l, shape_of (apps (Const (Ind D)) l) = Some (SInd D).
Proof. intros D l. unfold shape_of. rewrite spine_head_apps. reflexivity. Qed.

(** A rigid head reduces only inside, to a head of the same shape. *)
Lemma par_rigid : forall sg h h' k, par sg h h' -> shape_of h = Some k -> spine_head h = h ->
  shape_of h' = Some k /\ spine_head h' = h'.
Proof.
  intros sg h h' k H Hs Hh. unfold shape_of in Hs. rewrite Hh in Hs.
  destruct h; try discriminate Hs.
  all: try (injection Hs as <-; inversion H; subst; split; reflexivity).
  match goal with g : gref |- _ => destruct g; try discriminate Hs end.
  injection Hs as <-. inversion H; subst; [split; reflexivity | ].
  match goal with Hd : sig_delta _ _ = Some _ |- _ => discriminate Hd end.
Qed.

Lemma red_shape : forall sg t w k, red sg t w -> shape_of t = Some k -> shape_of w = Some k.
Proof.
  intros sg t w k H. induction H as [t u H | t | t u v _ IH1 _ IH2]; intros Hs; [ | exact Hs | exact (IH2 (IH1 Hs))].
  apply red1_par in H.
  assert (Hh : spine_head (spine_head t) = spine_head t) by apply spine_head_idem.
  assert (Hs' : shape_of (spine_head t) = Some k) by (unfold shape_of in *; rewrite Hh; exact Hs).
  destruct (par_spine sg _ _ H) as (h' & args' & -> & Hp & _).
  - intros b E. unfold shape_of in Hs. rewrite E in Hs. discriminate Hs.
  - unfold arity_below. unfold shape_of in Hs.
    destruct (spine_head t) eqn:E; try discriminate Hs; try exact I.
    destruct g; try discriminate Hs. exact I.
  - destruct (par_rigid sg _ _ _ Hp Hs' Hh) as [Hs2 Hh2].
    unfold shape_of in Hs2 |- *. rewrite spine_head_apps, Hh2. rewrite Hh2 in Hs2. exact Hs2.
Qed.

(** Convertible types have heads of the same shape. *)
Lemma conv_shape' : forall sg t u k1 k2, conv sg t u -> shape_of t = Some k1 -> shape_of u = Some k2 -> k1 = k2.
Proof.
  intros sg t u k1 k2 H H1 H2. destruct (church_rosser sg _ _ H) as (w & Hw1 & Hw2).
  pose proof (red_shape sg _ _ _ Hw1 H1) as E1. pose proof (red_shape sg _ _ _ Hw2 H2) as E2.
  rewrite E1 in E2. injection E2 as ->. reflexivity.
Qed.

(** The types of the instances are telescopes of the arity of their
    eliminator. *)
Definition instances_shaped (sg : signature) : Prop :=
  forall D s A act, sig_elim sg D s = Some (A, act) ->
  exists d Ts R, sig_ind sg D = Some d /\ A = pis Ts R /\ length Ts = elim_arity d.

(** An instance with active rules. *)
Lemma elim_head_spec : forall sg D s D' s' d, elim_head sg (Const (Elim D s)) = Some (D', s', d) ->
  D' = D /\ s' = s /\ (exists A, sig_elim sg D s = Some (A, true)) /\ sig_ind sg D = Some d.
Proof.
  intros sg D s D' s' d H. unfold elim_head in H.
  destruct (sig_elim sg D s) as [[A [|]]|] eqn:E1; try discriminate H.
  destruct (sig_ind sg D) as [d0|] eqn:E2; [ | discriminate H]. injection H as <- <- <-. eauto 6.
Qed.

Section Canonical.
  Variable S : spec.
  Variable sg : signature.
  Hypothesis Hsig : signature_typed S sg.
  Hypothesis Helim : instances_shaped sg.
  Local Notation typed := (has_type S sg).
  Local Notation "t ≡ u" := (conv sg t u).

  (** [T] converts to a type of shape [k1], and reduces to one of
      shape [k2]. *)
  Lemma ctype_clash : forall G X T Y k1 k2, ctype S sg G X T -> red sg T Y ->
    shape_of X = Some k1 -> shape_of Y = Some k2 -> k1 = k2.
  Proof.
    intros G X T Y k1 k2 H HY H1 H2.
    apply (conv_shape' sg X Y); [ | exact H1 | exact H2].
    eapply conv_trans; [exact (ctype_conv_of S sg _ _ _ H) | exact (red_conv _ _ HY)].
  Qed.

  Lemma conv_clash : forall X T Y k1 k2, X ≡ T -> red sg T Y ->
    shape_of X = Some k1 -> shape_of Y = Some k2 -> k1 = k2.
  Proof.
    intros X T Y k1 k2 H HY H1 H2. apply (conv_shape' sg X Y); [ | exact H1 | exact H2].
    eapply conv_trans; [exact H | exact (red_conv _ _ HY)].
  Qed.

  (** *** The types of spines *)

  Lemma typed_apps_prefix : forall l2 h l1 G T, typed G (apps h (l1 ++ l2)) T -> exists T', typed G (apps h l1) T'.
  Proof.
    induction l2 as [|a l2 IH] using rev_ind; intros h l1 G T H; [rewrite app_nil_r in H; eauto | ].
    rewrite app_assoc, apps_snoc in H. destruct (inv_app S sg _ _ _ _ H) as (A & B & Hf & _ & _).
    exact (IH _ _ _ _ Hf).
  Qed.

  (** A head whose types are convertible to [Π Ts. R0]: below the length
      of the telescope a Π, at its length [R0] instantiated, past it
      [R0] instantiated is applied, so is a Π. *)
  Lemma spine_type : forall args G h T Ts R0 s0,
    typed G (apps h args) T -> (forall H, typed G h H -> H ≡ pis Ts R0) -> typed G (pis Ts R0) (Srt s0) ->
    (length args < length Ts /\ exists A B, Pi A B ≡ T) \/
    (length args = length Ts /\ subst (tsub args) R0 ≡ T /\ args_typed S sg G Ts args) \/
    (length Ts < length args /\ exists A B, subst (tsub (firstn (length Ts) args)) R0 ≡ Pi A B).
  Proof.
    intros args G h T Ts R0 s0 Ht Hh HP.
    destruct (Nat.lt_total (length args) (length Ts)) as [Hlt | [Heq | Hgt]].
    - left. split; [exact Hlt | ].
      rewrite <- (firstn_skipn (length args) Ts) in Hh, HP.
      assert (Hl1 : length (firstn (length args) Ts) = length args) by (rewrite length_firstn; lia).
      destruct (skipn (length args) Ts) as [|T2 Ts2] eqn:Es.
      { exfalso. apply (f_equal (@length term)) in Es. rewrite length_skipn in Es. cbn in Es. lia. }
      rewrite pis_app in Hh, HP.
      destruct (apps_inv S sg args G h T _ _ s0 Hl1 Ht Hh HP) as [_ Hc].
      rewrite subst_pis in Hc. cbn [subst_tele pis] in Hc. eexists _, _. exact Hc.
    - right; left. destruct (apps_inv S sg args G h T Ts R0 s0 (eq_sym Heq) Ht Hh HP) as [Ha Hc]. auto.
    - right; right. split; [exact Hgt | ].
      rewrite <- (firstn_skipn (length Ts) args) in Ht.
      destruct (skipn (length Ts) args) as [|a rest] eqn:Es.
      { exfalso. apply (f_equal (@length term)) in Es. rewrite length_skipn in Es. cbn in Es. lia. }
      destruct (typed_apps_prefix rest h (firstn (length Ts) args ++ [a]) G T ltac:(rewrite <- app_assoc; exact Ht))
        as [T' Ht'].
      rewrite apps_snoc in Ht'. destruct (inv_app S sg _ _ _ _ Ht') as (A & B & Hf & _ & _).
      destruct (apps_inv S sg (firstn (length Ts) args) G h _ Ts R0 s0 ltac:(rewrite length_firstn; lia) Hf Hh HP) as [_ Hc].
      eauto.
  Qed.

  (** A [fix] applied below its structural argument has a Π-type. *)
  Lemma fix_spine_type : forall args G A k b T, typed G (apps (Fix A k b) args) T -> length args <= k ->
    exists X j D, X ≡ T /\ struct_arg sg X j D /\ length args + j = k.
  Proof.
    induction args as [|a args IH] using rev_ind; intros G A k b T H Hl.
    - destruct (inv_fix S sg _ _ _ _ _ H) as (s & D & _ & Hsa & _ & _ & _ & HT).
      exists A, k, D. split; [exact (ctype_conv_of S sg _ _ _ HT) | split; [exact Hsa | reflexivity]].
    - rewrite length_app in Hl. cbn [length] in Hl.
      rewrite apps_snoc in H. destruct (inv_app S sg _ _ _ _ H) as (A1 & B1 & Hf & _ & HT).
      destruct (IH _ _ _ _ _ Hf ltac:(lia)) as (X & j & D & Hc & Hsa & Hj).
      destruct j as [|j]; [lia | ].
      inversion Hsa as [| X0 T2 B2 j0 D0 HX Hsa' ]; subst.
      assert (Hpi : Pi T2 B2 ≡ Pi A1 B1) by (eapply conv_trans; [apply conv_sym, red_conv, HX | exact Hc]).
      apply pi_inj in Hpi as [_ HB].
      exists (subst1 B2 a), j, D. split; [ | split; [exact (struct_arg_subst _ _ _ _ _ Hsa') | rewrite length_app; cbn; lia]].
      eapply conv_trans; [apply conv_subst; exact HB | exact (ctype_conv_of S sg _ _ _ HT)].
  Qed.

  Lemma struct_arg_pi : forall X j D, struct_arg sg X j D -> exists A B, red sg X (Pi A B).
  Proof. intros X j D H. destruct H; eauto. Qed.

  (** *** Canonical forms *)

  Lemma head_typed : forall h args G T, typed G (apps h args) T -> exists H, typed G h H.
  Proof. intros h args G T H. exact (typed_apps_prefix args h [] G T H). Qed.

  Lemma shape_pis_cons : forall T Ts R, shape_of (pis (T :: Ts) R) = Some SPi.
  Proof. reflexivity. Qed.

  (** A family applied: a type, or a type family. *)
  Lemma ind_spine_shape : forall args D T Y k, typed [] (apps (Const (Ind D)) args) T -> red sg T Y ->
    shape_of Y = Some k -> k = SPi \/ k = SSrt.
  Proof.
    intros args D T Y k H HY Hk. destruct (head_typed _ _ _ _ H) as [H0 Hh].
    destruct (inv_const S sg _ _ _ Hh) as (A & _ & _ & Hty & _).
    cbn [sig_type] in Hty. destruct (sig_ind sg D) as [d|] eqn:Hd; [ | discriminate Hty].
    cbn [option_map] in Hty. injection Hty as <-.
    assert (Hty : sig_type sg (Ind D) = Some (ind_type d)) by (cbn [sig_type]; rewrite Hd; reflexivity).
    destruct (const_type_typed S sg Hsig [] _ _ (W_Nil _ _) Hty) as [s0 Hs0]. unfold ind_type in Hs0.
    destruct (spine_type args [] _ T _ _ s0 H (const_head S sg _ _ _ Hty) Hs0)
      as [(_ & A & B & Hc) | [(_ & Hc & _) | (_ & A & B & Hc)]].
    - left. symmetry. exact (conv_clash _ _ _ _ _ Hc HY eq_refl Hk).
    - right. symmetry. exact (conv_clash _ _ _ _ _ Hc HY eq_refl Hk).
    - exfalso. pose proof (conv_shape' sg _ _ SSrt SPi Hc eq_refl eq_refl) as E. discriminate E.
  Qed.

  (** An instance applied below its arity. *)
  Lemma elim_spine_shape : forall args D s d T Y k, typed [] (apps (Const (Elim D s)) args) T ->
    sig_ind sg D = Some d -> length args < elim_arity d -> red sg T Y -> shape_of Y = Some k -> k = SPi.
  Proof.
    intros args D s d T Y k H Hd Hl HY Hk. destruct (head_typed _ _ _ _ H) as [H0 Hh].
    destruct (inv_const S sg _ _ _ Hh) as (A & _ & _ & Hty & _).
    pose proof Hty as Hty'. cbn [sig_type] in Hty'.
    destruct (sig_elim sg D s) as [[A' act]|] eqn:He; [ | discriminate Hty']. cbn [option_map fst] in Hty'.
    injection Hty' as <-.
    destruct (Helim _ _ _ _ He) as (d' & Ts & R & Hd' & -> & Hlen). rewrite Hd in Hd'. injection Hd' as <-.
    destruct (const_type_typed S sg Hsig [] _ _ (W_Nil _ _) Hty) as [s0 Hs0].
    destruct (spine_type args [] _ T _ _ s0 H (const_head S sg _ _ _ Hty) Hs0)
      as [(_ & A & B & Hc) | [(Heq & _) | (Hgt & _)]]; [ | lia | lia].
    symmetry. exact (conv_clash _ _ _ _ _ Hc HY eq_refl Hk).
  Qed.

  Lemma fix_shape : forall args A k0 b T Y k, typed [] (apps (Fix A k0 b) args) T -> length args <= k0 ->
    red sg T Y -> shape_of Y = Some k -> k = SPi.
  Proof.
    intros args A k0 b T Y k H Hl HY Hk. destruct (fix_spine_type _ _ _ _ _ _ H Hl) as (X & j & D & Hc & Hsa & _).
    destruct (struct_arg_pi _ _ _ Hsa) as (A' & B' & HX).
    symmetry. apply (conv_clash (Pi A' B') T Y SPi k); [ | exact HY | reflexivity | exact Hk].
    eapply conv_trans; [apply conv_sym, red_conv, HX | exact Hc].
  Qed.

  (** A constructor applied: below its arity a Π, at its arity an
      element of its family. *)
  Lemma ctor_spine_shape : forall args D c T Y k, typed [] (apps (Const (Ctor D c)) args) T ->
    red sg T Y -> shape_of Y = Some k ->
    k = SPi \/ (k = SInd D /\ exists d i cd, sig_ind sg D = Some d /\ find_ctor (ind_ctors d) c = Some (i, cd) /\
                                 length args = length (ind_params d) + length (ctor_fields cd)).
  Proof.
    intros args D c T Y k H HY Hk. destruct (head_typed _ _ _ _ H) as [H0 Hh].
    destruct (inv_const S sg _ _ _ Hh) as (A & _ & _ & Hty & _).
    pose proof Hty as Hty'. cbn [sig_type] in Hty'.
    destruct (sig_ind sg D) as [d|] eqn:Hd; [ | discriminate Hty'].
    destruct (find_ctor (ind_ctors d) c) as [[i cd]|] eqn:Hc; [ | discriminate Hty']. cbn [option_map snd] in Hty'.
    injection Hty' as <-.
    destruct (const_type_typed S sg Hsig [] _ _ (W_Nil _ _) Hty) as [s0 Hs0].
    unfold ctor_type in Hs0. cbv zeta in Hs0.
    destruct (spine_type args [] _ T _ _ s0 H (const_head S sg _ _ _ Hty) Hs0)
      as [(_ & A' & B & Hcv) | [(Heq & Hcv & _) | (_ & A' & B & Hcv)]].
    - left. symmetry. exact (conv_clash _ _ _ _ _ Hcv HY eq_refl Hk).
    - right. rewrite subst_apps in Hcv. cbn [subst] in Hcv.
      pose proof (conv_clash _ _ _ _ _ Hcv HY (shape_of_apps_ind _ _) Hk) as E.
      rewrite (sig_ind_name _ _ _ Hd) in E. split; [symmetry; exact E | ].
      exists d, i, cd. split; [reflexivity | split; [exact Hc | ]].
      rewrite length_app, field_types_length in Heq. lia.
    - exfalso. rewrite subst_apps in Hcv. cbn [subst] in Hcv.
      pose proof (conv_shape' sg _ _ _ SPi Hcv (shape_of_apps_ind _ _) eq_refl) as E. discriminate E.
  Qed.

  Lemma head_value_cases : forall h n, head_value sg h n = true ->
    (exists g, h = Const g) \/ (exists A k b, h = Fix A k b /\ n < Datatypes.S k).
  Proof.
    intros h n H. unfold head_value, head_arity, elim_head in H.
    destruct h; cbn [is_inert orb] in H; try discriminate H.
    - left. eauto.
    - right. apply Nat.ltb_lt in H. eauto.
  Qed.

  (** The canonical forms of closed values at a type that reduces to one
      of shape neither Π nor sort. *)
  Theorem value_shape : forall v T Y k, vvalue sg v -> typed [] v T -> red sg T Y -> shape_of Y = Some k ->
    k <> SPi -> k <> SSrt ->
    match k with
    | SBool => v = BTrue \/ v = BFalse
    | SUnit => v = Tt
    | SSigma => exists a b, v = Pair a b
    | SInd D => exists c args d i cd, v = apps (Const (Ctor D c)) args /\ sig_ind sg D = Some d /\
                  find_ctor (ind_ctors d) c = Some (i, cd) /\
                  length args = length (ind_params d) + length (ctor_fields cd)
    | _ => False
    end.
  Proof.
    intros v T Y k Hv H HY Hk Hpi Hsrt.
    (* spines of a constant *)
    assert (Hconst : forall g args, v = apps (Const g) args ->
                     head_value sg (Const g) (length args) = true \/ (args = [] /\ sig_delta sg g = None) ->
                     match k with
                     | SInd D => exists c args d i cd, v = apps (Const (Ctor D c)) args /\ sig_ind sg D = Some d /\
                                   find_ctor (ind_ctors d) c = Some (i, cd) /\
                                   length args = length (ind_params d) + length (ctor_fields cd)
                     | _ => False
                     end).
    { intros g args -> Hhv. destruct g as [D' | D' c | D' s | f].
      - exfalso. destruct (ind_spine_shape _ _ _ _ _ H HY Hk) as [E | E]; contradiction.
      - destruct (ctor_spine_shape _ _ _ _ _ _ H HY Hk) as [E | (-> & d & i & cd & Hd & Hc & Hl)]; [contradiction | ].
        exists c, args, d, i, cd. auto.
      - exfalso. apply Hpi.
        destruct (head_typed _ _ _ _ H) as [H0 Hh0].
        destruct (inv_const S sg _ _ _ Hh0) as (A & _ & _ & Hty & _).
        cbn [sig_type] in Hty. destruct (sig_elim sg D' s) as [[A' act]|] eqn:He; [ | discriminate Hty].
        destruct (Helim _ _ _ _ He) as (d & Ts & R & Hd & _ & Hlen).
        apply (elim_spine_shape args D' s d T Y k H Hd); [ | exact HY | exact Hk].
        destruct Hhv as [Hhv | [-> _]]; [ | unfold elim_arity; cbn; lia].
        unfold head_value, head_arity in Hhv. cbn [is_inert orb] in Hhv.
        destruct (elim_head sg (Const (Elim D' s))) as [[[D2 s2] d2]|] eqn:Eh; [ | discriminate Hhv].
        destruct (elim_head_spec _ _ _ _ _ _ Eh) as (_ & _ & _ & Hd2). rewrite Hd in Hd2. injection Hd2 as <-.
        apply Nat.ltb_lt in Hhv. exact Hhv.
      - exfalso. destruct (head_typed _ _ _ _ H) as [H0 Hh0].
        destruct (inv_const S sg _ _ _ Hh0) as (A & _ & _ & Hty & _).
        cbn [sig_type] in Hty. destruct (sig_def sg f) as [[A' b]|] eqn:Ef; [ | discriminate Hty].
        destruct Hhv as [Hhv | [_ Hn]].
        + unfold head_value, head_arity in Hhv. cbn [is_inert orb elim_head] in Hhv. discriminate Hhv.
        + cbn [sig_delta] in Hn. rewrite Ef in Hn. discriminate Hn. }
    (* spines of a fix *)
    assert (Hfix : forall A k0 b args, v = apps (Fix A k0 b) args -> length args <= k0 -> False).
    { intros A k0 b args -> Hl. apply Hpi. exact (fix_shape args A k0 b _ _ _ H Hl HY Hk). }
    destruct v.
    all: try (exfalso; exact Hv).
    (* sorts, Π, Σ and the primitive types: types *)
    all: try (exfalso; apply Hsrt;
              match type of H with
              | typed _ (Srt _) _ => destruct (inv_sort S sg _ _ _ H) as (s' & _ & Hc)
              | typed _ (Pi _ _) _ => destruct (inv_pi S sg _ _ _ _ H) as (s1 & s2 & s' & _ & _ & _ & Hc)
              | typed _ (Sigma _ _) _ => destruct (inv_sigma S sg _ _ _ _ H) as (s1 & s2 & s' & _ & _ & _ & Hc)
              | typed _ Void _ => destruct (inv_prim S sg _ _ _ H (or_introl eq_refl)) as (s' & _ & Hc)
              | typed _ Unit _ => destruct (inv_prim S sg _ _ _ H (or_intror (or_introl eq_refl))) as (s' & _ & Hc)
              | typed _ Bool _ => destruct (inv_prim S sg _ _ _ H (or_intror (or_intror eq_refl))) as (s' & _ & Hc)
              end; symmetry; exact (ctype_clash _ _ _ _ _ _ Hc HY eq_refl Hk); fail).
    (* a λ *)
    - exfalso. apply Hpi. destruct (inv_lam S sg _ _ _ H) as (A & B & s & _ & _ & Hc).
      symmetry. exact (ctype_clash _ _ _ _ _ _ Hc HY eq_refl Hk).
    (* an application: a spine of a constant or of a fix *)
    - destruct Hv as (Hsv & _ & _). unfold spine_value in Hsv.
      pose proof (apps_spine (App v1 v2)) as Ev.
      destruct (head_value_cases _ _ Hsv) as [(g & Eg) | (A & k0 & b & Eg & Hl)]; rewrite Eg in Ev, Hsv.
      + pose proof (Hconst g _ (eq_sym Ev) (or_introl Hsv)) as Hs.
        destruct k; try exact Hs; destruct Hs.
      + exfalso. exact (Hfix _ _ _ _ (eq_sym Ev) ltac:(lia)).
    (* tt *)
    - pose proof (ctype_clash _ _ _ _ _ _ (inv_tt S sg _ _ H) HY eq_refl Hk) as E. subst k. reflexivity.
    (* the booleans *)
    - pose proof (ctype_clash _ _ _ _ _ _ (inv_bool_value S sg _ _ _ H (or_introl eq_refl)) HY eq_refl Hk) as E.
      subst k. left. reflexivity.
    - pose proof (ctype_clash _ _ _ _ _ _ (inv_bool_value S sg _ _ _ H (or_intror eq_refl)) HY eq_refl Hk) as E.
      subst k. right. reflexivity.
    (* a pair *)
    - destruct (inv_pair S sg _ _ _ _ H) as (A & B & s & _ & _ & _ & Hc).
      pose proof (ctype_clash _ _ _ _ _ _ Hc HY eq_refl Hk) as E. subst k. eauto.
    (* a constant *)
    - pose proof (Hconst g [] eq_refl (or_intror (conj eq_refl Hv))) as Hs.
      destruct k; try exact Hs; destruct Hs.
    (* a fix *)
    - exfalso. exact (Hfix _ _ _ [] eq_refl (Nat.le_0_l _)).
  Qed.
End Canonical.
