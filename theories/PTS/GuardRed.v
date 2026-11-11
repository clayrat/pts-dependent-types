(** * Stability of the guard under reduction

    The guard of PTS.Guard is syntactic, and a [fix] body keeps it under
    one-step reduction ([guarded_red1], [fix_guarded_red1]), wherever the
    step happens.  This is what subject reduction needs for a step inside
    the body of a [fix]: [T_Fix] asks for the guard again.

    The argument rests on four facts about the judgment [Guarded]:
    - it is monotone in the marks: a variable marked [Large] may get any
      mark but [Self] ([guarded_mono]).  A match whose scrutinee becomes
      a structural origin gives its branches fields where they had none,
      and the λ peeled with a field mark were entered with [Large]
      before; so the lemma is stated for a term peeled with any fields;
    - an application of guarded terms is guarded ([guarded_app]): if
      the function is a call of [Self], it already has its structural
      argument, and the application is a longer call;
    - it is stable under a substitution that keeps the marks of the
      variables it does not replace, and replaces only [Large] ones by
      guarded terms ([guarded_subst_gen]).  This gives β and the
      unfolding of an inner [fix] (its function is [Large] in the outer
      guard), and renamings that keep the marks;
    - a spine headed by a variable reduces only in its arguments, keeping
      their number ([red1_var_spine]), so a structural origin and a
      strict subterm stay what they are.

    Reduction inside a call [f a₁ … aₙ] happens in one argument, and the
    partial spine [f a₁ … aᵢ] is not guarded by itself; so the main
    induction carries a second statement, about the arguments of a spine
    headed by a variable.  The contractions of the signature: the body of
    a δ-constant is closed; the ι of an eliminator instance builds its
    result from the guarded arguments of the redex and from closed
    descriptions ([guarded_iota]); the ι of a match on a constructor
    spine takes a branch that was checked without fields. *)

From Stdlib Require Import List Arith Lia Bool.
From Stdlib Require String.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Telescope Signature Reduction SubstLaws Guard GuardSubst.

(** ** Spines headed by a variable *)

Lemma apps_not_lam : forall h l b, (forall c, h <> Lam c) -> apps h l <> Lam b.
Proof.
  intros h l b Hh. induction l as [|a l _] using rev_ind; [apply Hh | ].
  rewrite apps_snoc. discriminate.
Qed.

Lemma apps_var_not_lam : forall i l b, apps (Var i) l <> Lam b.
Proof. intros i l b. apply apps_not_lam. discriminate. Qed.

Lemma apps_var_snoc_inv : forall i l f a, apps (Var i) l = App f a ->
  exists l0, l = l0 ++ [a] /\ f = apps (Var i) l0.
Proof.
  intros i l f a E. induction l as [|x l _] using rev_ind; [discriminate E | ].
  rewrite apps_snoc in E. injection E as <- <-. exists l. split; reflexivity.
Qed.

Lemma spine_iota_var : forall sg t i, spine_head t = Var i -> spine_iota sg t = None.
Proof. intros sg t i H. rewrite spine_iota_head, H. reflexivity. Qed.

Lemma red1_var : forall sg i w, ~ red1 sg (Var i) w.
Proof.
  intros sg i w H. inversion H; subst.
  - rewrite (spine_iota_var sg (Var i) i eq_refl) in H0. discriminate H0.
  - discriminate H0.
Qed.

(** A spine headed by a variable reduces in its arguments. *)
Lemma red1_var_spine : forall sg i l w, red1 sg (apps (Var i) l) w ->
  exists l', w = apps (Var i) l' /\ length l' = length l.
Proof.
  intros sg i l. induction l as [|a l IH] using rev_ind; intros w H.
  - exfalso. exact (red1_var sg i w H).
  - rewrite apps_snoc in H. remember (apps (Var i) l) as f eqn:Ef.
    inversion H; subst.
    + exfalso. exact (apps_var_not_lam i l b (eq_sym H1)).
    + destruct (IH f' H3) as (l' & -> & Hl). exists (l' ++ [a]).
      rewrite apps_snoc, !length_app, Hl. split; reflexivity.
    + exists (l ++ [a']). rewrite apps_snoc. split; [reflexivity | rewrite !length_app; reflexivity].
    + rewrite (spine_iota_var sg _ i) in H0; [discriminate H0 | ].
      cbn [spine_head]. rewrite spine_head_apps. reflexivity.
    + discriminate H0.
Qed.

Section GuardRed.
  Variable sg : signature.
  Variable k : nat.
  Local Notation guarded := (Guarded sg k).

  (** ** Inversion *)

  Definition ginv (ms : list mark) (t : term) : Prop :=
    match t with
    | Var i => is_self (mark_at ms i) = false
    | Lam b => guarded (Large :: ms) b
    | Pi A B | Sigma A B => guarded ms A /\ guarded (Large :: ms) B
    | Fix A _ b => guarded ms A /\ guarded (Large :: ms) b
    | Ann u A | ElimVoid u A | Pair u A => guarded ms u /\ guarded ms A
    | ElimUnit C c u => guarded ms C /\ guarded ms c /\ guarded ms u
    | ElimBool C t f b => guarded ms C /\ guarded ms t /\ guarded ms f /\ guarded ms b
    | Fst p | Snd p => guarded ms p
    | Case D _ P x bs => guarded ms P /\ guarded ms x /\
        (forall j b, nth_error bs j = Some b ->
           guarded (fst (peel ms (nth j (branch_fields sg ms D x) []) b))
                   (snd (peel ms (nth j (branch_fields sg ms D x) []) b)))
    | _ => True
    end.

  Lemma guarded_inv : forall ms t, guarded ms t -> ginv ms t.
  Proof.
    intros ms t H. destruct H; cbn [ginv]; try (repeat split; assumption).
    - induction args as [|a args _] using rev_ind; [cbn in H0; lia | ].
      rewrite apps_snoc. exact I.
    - destruct t; cbn in H; try discriminate H; exact I.
  Qed.

  Lemma self_headed_app : forall ms f a, self_headed ms (App f a) = self_headed ms f.
  Proof. reflexivity. Qed.

  Lemma self_headed_apps : forall ms h l, self_headed ms (apps h l) = self_headed ms h.
  Proof. intros ms h l. unfold self_headed. rewrite spine_head_apps. reflexivity. Qed.

  Lemma guarded_app_inv : forall ms f a, guarded ms (App f a) -> self_headed ms (App f a) = false ->
    guarded ms f /\ guarded ms a.
  Proof.
    intros ms f a H Hs. remember (App f a) as t eqn:Et. destruct H; try discriminate Et.
    - exfalso. rewrite self_headed_apps in Hs. cbn in Hs. rewrite H in Hs. discriminate Hs.
    - injection Et as -> ->. split; assumption.
    - subst. discriminate.
  Qed.

  (** A guarded term headed by the function is a call. *)
  Lemma guarded_self_inv : forall ms t, guarded ms t -> self_headed ms t = true ->
    exists i args, t = apps (Var i) args /\ mark_at ms i = Self /\ k < length args /\
      sub_arg ms (nth k args (Var 0)) = true /\ Forall (guarded ms) args.
  Proof.
    intros ms t H Hs. destruct H; try discriminate Hs.
    - exists i, args. repeat split; try assumption. apply Forall_forall. assumption.
    - unfold self_headed in Hs. cbn in Hs. rewrite H in Hs. discriminate Hs.
    - rewrite H in Hs. discriminate Hs.
    - match goal with Ha : atomic ?u = true |- _ => destruct u; try discriminate Ha; discriminate Hs end.
  Qed.

  (** ** Applications of guarded terms *)

  Lemma guarded_app : forall ms f a, guarded ms f -> guarded ms a -> guarded ms (App f a).
  Proof.
    intros ms f a Hf Ha. destruct (self_headed ms (App f a)) eqn:Es.
    - destruct (guarded_self_inv ms f Hf Es) as (i & args & -> & Hi & Hk & Hsub & Hargs).
      rewrite <- apps_snoc. apply G_Call; [exact Hi | rewrite length_app; cbn [length]; lia | | ].
      + rewrite app_nth1 by exact Hk. exact Hsub.
      + intros b Hb. apply in_app_or in Hb as [Hb | [<- | []]]; [ | exact Ha].
        rewrite Forall_forall in Hargs. exact (Hargs b Hb).
    - apply G_App; assumption.
  Qed.

  Lemma guarded_apps : forall l ms h, guarded ms h -> Forall (guarded ms) l -> guarded ms (apps h l).
  Proof.
    induction l as [|a l IH]; intros ms h Hh Hl; [exact Hh | ].
    inversion Hl; subst. cbn [apps fold_left]. apply IH; [apply guarded_app | ]; assumption.
  Qed.

  Lemma guarded_apps_inv : forall l ms h, guarded ms (apps h l) -> self_headed ms h = false ->
    guarded ms h /\ Forall (guarded ms) l.
  Proof.
    induction l as [|a l IH] using rev_ind; intros ms h H Hs; [split; [exact H | constructor] | ].
    rewrite apps_snoc in H. destruct (guarded_app_inv ms _ _ H) as [H1 H2].
    - rewrite self_headed_app, self_headed_apps. exact Hs.
    - destruct (IH ms h H1 Hs) as [Hh Hl]. split; [exact Hh | ].
      apply Forall_app. split; [exact Hl | constructor; [exact H2 | constructor]].
  Qed.

  Lemma repeat_large_cons : forall m ms, repeat Large m ++ Large :: ms = Large :: repeat Large m ++ ms.
  Proof. induction m as [|m IH]; intros ms; [reflexivity | cbn [repeat app]; rewrite IH; reflexivity]. Qed.

  Lemma guarded_lams : forall m ms X, guarded (repeat Large m ++ ms) X -> guarded ms (lams m X).
  Proof.
    induction m as [|m IH]; intros ms X H; [exact H | ].
    cbn [lams]. apply G_Lam. apply IH. rewrite repeat_large_cons. exact H.
  Qed.

  (** ** Monotonicity in the marks *)

  (** [ms'] marks at least as much as [ms]: a [Large] variable may get
      any mark but [Self]. *)
  Definition marks_le (ms ms' : list mark) : Prop :=
    forall i, mark_at ms i = mark_at ms' i \/ (mark_at ms i = Large /\ is_self (mark_at ms' i) = false).

  Lemma marks_le_refl : forall ms, marks_le ms ms.
  Proof. intros ms i. left. reflexivity. Qed.

  Lemma marks_le_cons : forall m ms ms', marks_le ms ms' -> marks_le (m :: ms) (m :: ms').
  Proof. intros m ms ms' H [|i]; [left; reflexivity | exact (H i)]. Qed.

  Lemma marks_le_cons_large : forall m ms ms', is_self m = false -> marks_le ms ms' ->
    marks_le (Large :: ms) (m :: ms').
  Proof. intros m ms ms' Hm H [|i]; [right; split; [reflexivity | exact Hm] | exact (H i)]. Qed.

  Lemma marks_le_app : forall E ms ms', marks_le ms ms' -> marks_le (E ++ ms) (E ++ ms').
  Proof. induction E as [|m E IH]; intros ms ms' H; [exact H | apply marks_le_cons, IH, H]. Qed.

  Lemma mark_self_mono : forall ms ms' i, marks_le ms ms' -> mark_at ms i = Self -> mark_at ms' i = Self.
  Proof.
    intros ms ms' i H E. destruct (H i) as [E' | [E' _]]; [rewrite <- E'; exact E | ].
    rewrite E in E'. discriminate E'.
  Qed.

  Lemma self_headed_mono : forall ms ms' t, marks_le ms ms' -> self_headed ms t = false ->
    self_headed ms' t = false.
  Proof.
    intros ms ms' t H Hs. unfold self_headed in *. destruct (spine_head t); try reflexivity.
    destruct (H n) as [E | [_ E]]; [rewrite <- E; exact Hs | exact E].
  Qed.

  Lemma sub_arg_mono : forall ms ms' a, marks_le ms ms' -> sub_arg ms a = true -> sub_arg ms' a = true.
  Proof.
    intros ms ms' a H Ha. unfold sub_arg in *. destruct (spine_head a); try discriminate Ha.
    destruct (mark_at ms n) eqn:E; try discriminate Ha.
    destruct (H n) as [E' | [E' _]]; [rewrite <- E', E; exact Ha | rewrite E in E'; discriminate E'].
  Qed.

  Lemma is_arg_mono : forall ms ms' x, marks_le ms ms' -> is_arg ms x = true -> is_arg ms' x = true.
  Proof.
    intros ms ms' x H Hx. destruct x; try discriminate Hx. cbn [is_arg] in *.
    destruct (mark_at ms n) eqn:E; try discriminate Hx.
    destruct (H n) as [E' | [E' _]]; [rewrite <- E', E; reflexivity | rewrite E in E'; discriminate E'].
  Qed.

  Lemma origin_mono : forall ms ms' x, marks_le ms ms' -> origin ms x = true -> origin ms' x = true.
  Proof.
    intros ms ms' x H Hx. unfold origin in *. apply orb_true_iff in Hx as [Hx | Hx].
    - rewrite (is_arg_mono _ _ _ H Hx). reflexivity.
    - rewrite (sub_arg_mono _ _ _ H Hx), orb_true_r. reflexivity.
  Qed.

  Lemma branch_fields_origin : forall ms ms' D x x', origin ms x = true -> origin ms' x' = true ->
    branch_fields sg ms' D x' = branch_fields sg ms D x.
  Proof. intros ms ms' D x x' H H'. unfold branch_fields. rewrite H, H'. reflexivity. Qed.

  Lemma branch_fields_nonorigin : forall ms D x, origin ms x = false -> branch_fields sg ms D x = [].
  Proof. intros ms D x H. unfold branch_fields. rewrite H. reflexivity. Qed.

  Lemma nth_nil_fields : forall j, nth j (@nil (list field)) [] = [].
  Proof. intros [|j]; reflexivity. Qed.

  (** *** Peeling *)

  Lemma peel_spec : forall fds b, exists n b0, n <= length fds /\ b = lams n b0 /\
    forall ms, peel ms fds b = (rev (map field_mark (firstn n fds)) ++ ms, b0).
  Proof.
    induction fds as [|fd fds IH]; intros b.
    - exists 0, b. split; [lia | split; [reflexivity | intros ms; reflexivity]].
    - assert (Hl : (exists b', b = Lam b') \/ (forall b', b <> Lam b'))
        by (destruct b; first [left; eexists; reflexivity | right; intros ? ?; discriminate]).
      destruct Hl as [[b' ->] | Hnl].
      + destruct (IH b') as (n & b0 & Hn & -> & Hp). exists (S n), b0.
        split; [cbn [length]; lia | split; [reflexivity | ]].
        intros ms. cbn [peel lams]. rewrite Hp. cbn [firstn map rev]. rewrite <- app_assoc. reflexivity.
      + exists 0, b. split; [lia | split; [reflexivity | ]].
        intros ms. rewrite (peel_nolam ms _ b Hnl). reflexivity.
  Qed.

  Lemma peel_lams : forall n fds ms X, n <= length fds ->
    peel ms fds (lams n X) = peel (rev (map field_mark (firstn n fds)) ++ ms) (skipn n fds) X.
  Proof.
    induction n as [|n IH]; intros fds ms X Hn; [reflexivity | ].
    destruct fds as [|fd fds]; [cbn [length] in Hn; lia | ].
    cbn [lams firstn skipn map rev peel]. rewrite IH by (cbn [length] in Hn; lia).
    rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma length_peel_marks : forall n fds, n <= length fds ->
    length (rev (map field_mark (firstn n fds))) = n.
  Proof. intros n fds H. rewrite length_rev, length_map, length_firstn. lia. Qed.

  (** Monotonicity, for a term peeled with any fields: a λ entered with
      [Large] may be peeled with the mark of a field. *)
  Theorem guarded_mono : forall ms t, guarded ms t -> forall ms' fds, marks_le ms ms' ->
    guarded (fst (peel ms' fds t)) (snd (peel ms' fds t)).
  Proof.
    induction 1 as
      [ms i args Hself Hk Hsub _ IH | ms i Hi | ms f a Hs _ IHf _ IHa | ms b _ IHb
      | ms A B _ IHA _ IHB | ms A B _ IHA _ IHB | ms A k' b _ IHA _ IHb
      | ms u A _ IHu _ IHA | ms C e _ IHC _ IHe | ms a b _ IHa _ IHb
      | ms C c u _ IHC _ IHc _ IHu | ms C t f b _ IHC _ IHt _ IHf _ IHb
      | ms p _ IHp | ms p _ IHp
      | ms D s P x bs _ IHP _ IHx _ IHbs | ms t Ht ]; intros ms' fds Hle.
    (* λ: peeled with the mark of a field, or entered with Large *)
    4: { destruct fds as [|fd fds]; cbn [peel fst snd].
         - apply G_Lam. exact (IHb (Large :: ms') [] (marks_le_cons _ _ _ Hle)).
         - exact (IHb (field_mark fd :: ms') fds (marks_le_cons_large _ _ _ (field_mark_not_self fd) Hle)). }
    1: rewrite (peel_nolam ms' fds _ (apps_var_not_lam i args)).
    15: destruct t; try discriminate Ht; rewrite peel_nolam by (intros ? ?; discriminate); apply G_Atom; reflexivity.
    all: try (rewrite peel_nolam by (intros ? ?; discriminate)).
    all: cbn [fst snd].
    - apply G_Call; [exact (mark_self_mono _ _ _ Hle Hself) | exact Hk | exact (sub_arg_mono _ _ _ Hle Hsub) | ].
      intros a Ha. exact (IH a Ha ms' [] Hle).
    - apply G_Var. destruct (Hle i) as [E | [_ E]]; [rewrite <- E; exact Hi | exact E].
    - apply G_App; [exact (self_headed_mono _ _ _ Hle Hs) | exact (IHf ms' [] Hle) | exact (IHa ms' [] Hle)].
    - apply G_Pi; [exact (IHA ms' [] Hle) | exact (IHB (Large :: ms') [] (marks_le_cons _ _ _ Hle))].
    - apply G_Sigma; [exact (IHA ms' [] Hle) | exact (IHB (Large :: ms') [] (marks_le_cons _ _ _ Hle))].
    - apply G_Fix; [exact (IHA ms' [] Hle) | exact (IHb (Large :: ms') [] (marks_le_cons _ _ _ Hle))].
    - apply G_Ann; [exact (IHu ms' [] Hle) | exact (IHA ms' [] Hle)].
    - apply G_ElimVoid; [exact (IHC ms' [] Hle) | exact (IHe ms' [] Hle)].
    - apply G_Pair; [exact (IHa ms' [] Hle) | exact (IHb ms' [] Hle)].
    - apply G_ElimUnit; [exact (IHC ms' [] Hle) | exact (IHc ms' [] Hle) | exact (IHu ms' [] Hle)].
    - apply G_ElimBool;
        [exact (IHC ms' [] Hle) | exact (IHt ms' [] Hle) | exact (IHf ms' [] Hle) | exact (IHb ms' [] Hle)].
    - apply G_Fst. exact (IHp ms' [] Hle).
    - apply G_Snd. exact (IHp ms' [] Hle).
    (* a match: an origin keeps its fields, a branch without fields may get some *)
    - apply G_Case; [exact (IHP ms' [] Hle) | exact (IHx ms' [] Hle) | ].
      intros j b Hj. cbv zeta. specialize (IHbs j b Hj). cbv zeta in IHbs.
      destruct (origin ms x) eqn:Eo.
      + rewrite (branch_fields_origin ms ms' D x x Eo (origin_mono _ _ _ Hle Eo)) in *.
        destruct (peel_spec (nth j (branch_fields sg ms D x) []) b) as (n & b0 & Hn & -> & Hp).
        rewrite Hp in IHbs |- *. cbn [fst snd] in IHbs |- *.
        exact (IHbs _ [] (marks_le_app _ _ _ Hle)).
      + rewrite (branch_fields_nonorigin ms D x Eo), nth_nil_fields in IHbs. exact (IHbs ms' _ Hle).
  Qed.

  Corollary peel_guarded : forall ms fds t, guarded ms t -> guarded (fst (peel ms fds t)) (snd (peel ms fds t)).
  Proof. intros ms fds t H. exact (guarded_mono ms t H ms fds (marks_le_refl ms)). Qed.

  Corollary guarded_mono0 : forall ms ms' t, guarded ms t -> marks_le ms ms' -> guarded ms' t.
  Proof. intros ms ms' t H Hle. exact (guarded_mono ms t H ms' [] Hle). Qed.

  (** ** Substitution *)

  (** [sb] keeps the marks of the variables it sends to variables, and
      replaces only [Large] ones by other terms, guarded under any marks
      pushed above the target marks. *)
  Definition sub_marks (ms ms' : list mark) (sb : nat -> term) : Prop :=
    forall i, (exists j, sb i = Var j /\ mark_at ms' j = mark_at ms i) \/
              (mark_at ms i = Large /\ forall E, guarded (E ++ ms') (lift (length E) (sb i))).

  Lemma lift_lift_add : forall m n t, lift m (lift n t) = lift (m + n) t.
  Proof. intros m n t. unfold lift. rewrite rename_rename. apply rename_ext. intros i. lia. Qed.

  Lemma sub_marks_up : forall m ms ms' sb, sub_marks ms ms' sb -> sub_marks (m :: ms) (m :: ms') (up_sub sb).
  Proof.
    intros m ms ms' sb H [|i]; [left; exists 0; split; reflexivity | ].
    cbn [up_sub]. destruct (H i) as [(j & E & Ej) | [Hl HE]].
    - left. exists (S j). rewrite E. split; [reflexivity | exact Ej].
    - right. split; [exact Hl | ]. intros E. specialize (HE (E ++ [m])).
      rewrite <- app_assoc, length_app in HE. cbn [app length] in HE.
      rewrite lift_lift_add. exact HE.
  Qed.

  Lemma sub_marks_upn : forall E ms ms' sb, sub_marks ms ms' sb ->
    sub_marks (E ++ ms) (E ++ ms') (upn (length E) sb).
  Proof.
    induction E as [|m E IH]; intros ms ms' sb H; [exact H | ].
    cbn [app length upn]. apply sub_marks_up, IH, H.
  Qed.

  Lemma spine_subst_var : forall t sb i j, spine_head t = Var i -> sb i = Var j ->
    spine_head (subst sb t) = Var j /\ spine_args (subst sb t) = map (subst sb) (spine_args t).
  Proof.
    induction t; intros sb i j H Hs; cbn [spine_head] in H; try discriminate H.
    - injection H as ->. cbn [subst]. rewrite Hs. split; reflexivity.
    - cbn [subst spine_head]. destruct (IHt1 sb i j H Hs) as [E1 E2].
      split; [exact E1 | rewrite !spine_args_App, map_app, E2; reflexivity].
  Qed.

  Lemma mark_kept : forall ms ms' sb i, sub_marks ms ms' sb -> mark_at ms i <> Large ->
    exists j, sb i = Var j /\ mark_at ms' j = mark_at ms i.
  Proof. intros ms ms' sb i H Hi. destruct (H i) as [Hj | [Hl _]]; [exact Hj | contradiction]. Qed.

  Lemma sub_arg_subst_gen : forall ms ms' sb a, sub_marks ms ms' sb -> sub_arg ms a = true ->
    sub_arg ms' (subst sb a) = true.
  Proof.
    intros ms ms' sb a H Ha. unfold sub_arg in *. destruct (spine_head a) eqn:Eh; try discriminate Ha.
    destruct (mark_at ms n) eqn:Em; try discriminate Ha.
    destruct (mark_kept ms ms' sb n H ltac:(rewrite Em; discriminate)) as (j & Ej & Ejm).
    destruct (spine_subst_var a sb n j Eh Ej) as [E1 E2].
    rewrite E1, E2, length_map, Ejm, Em. exact Ha.
  Qed.

  Lemma is_arg_subst_gen : forall ms ms' sb x, sub_marks ms ms' sb -> is_arg ms x = true ->
    is_arg ms' (subst sb x) = true.
  Proof.
    intros ms ms' sb x H Hx. destruct x; try discriminate Hx. cbn [is_arg subst] in *.
    destruct (mark_at ms n) eqn:Em; try discriminate Hx.
    destruct (mark_kept ms ms' sb n H ltac:(rewrite Em; discriminate)) as (j & -> & Ejm).
    cbn [is_arg]. rewrite Ejm, Em. reflexivity.
  Qed.

  Lemma origin_subst_gen : forall ms ms' sb x, sub_marks ms ms' sb -> origin ms x = true ->
    origin ms' (subst sb x) = true.
  Proof.
    intros ms ms' sb x H Hx. unfold origin in *. apply orb_true_iff in Hx as [Hx | Hx].
    - rewrite (is_arg_subst_gen _ _ _ _ H Hx). reflexivity.
    - rewrite (sub_arg_subst_gen _ _ _ _ H Hx), orb_true_r. reflexivity.
  Qed.

  (** A substitution that keeps the marks it does not replace, and
      replaces [Large] variables by guarded terms, keeps the guard.  A
      branch peeled before may be peeled further after, when a variable
      replaced by a λ heads it: [peel_guarded] covers it. *)
  Theorem guarded_subst_gen : forall ms t, guarded ms t -> forall ms' sb, sub_marks ms ms' sb ->
    guarded ms' (subst sb t).
  Proof.
    induction 1 as
      [ms i args Hself Hk Hsub _ IH | ms i Hi | ms f a Hs _ IHf _ IHa | ms b _ IHb
      | ms A B _ IHA _ IHB | ms A B _ IHA _ IHB | ms A k' b _ IHA _ IHb
      | ms u A _ IHu _ IHA | ms C e _ IHC _ IHe | ms a b _ IHa _ IHb
      | ms C c u _ IHC _ IHc _ IHu | ms C t f b _ IHC _ IHt _ IHf _ IHb
      | ms p _ IHp | ms p _ IHp
      | ms D s P x bs _ IHP _ IHx _ IHbs | ms t Ht ]; intros ms' sb Hsb.
    (* a call: the function is kept with its mark, the arguments substituted *)
    - destruct (mark_kept ms ms' sb i Hsb ltac:(rewrite Hself; discriminate)) as (j & Ej & Ejm).
      rewrite subst_apps. cbn [subst]. rewrite Ej.
      apply G_Call; [rewrite Ejm; exact Hself | rewrite length_map; exact Hk | | ].
      + rewrite (nth_indep _ (Var 0) (subst sb (Var 0))) by (rewrite length_map; exact Hk).
        rewrite map_nth. exact (sub_arg_subst_gen _ _ _ _ Hsb Hsub).
      + intros a Ha. apply in_map_iff in Ha as (a' & <- & Ha'). exact (IH a' Ha' ms' sb Hsb).
    (* a variable: kept, or replaced by a guarded term *)
    - cbn [subst]. destruct (Hsb i) as [(j & -> & Ej) | [_ HE]].
      + apply G_Var. rewrite Ej. exact Hi.
      + pose proof (HE []) as H0. cbn [app length] in H0. rewrite lift_zero in H0. exact H0.
    - cbn [subst]. apply guarded_app; [exact (IHf ms' sb Hsb) | exact (IHa ms' sb Hsb)].
    - cbn [subst]. apply G_Lam. exact (IHb _ _ (sub_marks_up _ _ _ _ Hsb)).
    - cbn [subst]. apply G_Pi; [exact (IHA ms' sb Hsb) | exact (IHB _ _ (sub_marks_up _ _ _ _ Hsb))].
    - cbn [subst]. apply G_Sigma; [exact (IHA ms' sb Hsb) | exact (IHB _ _ (sub_marks_up _ _ _ _ Hsb))].
    - cbn [subst]. apply G_Fix; [exact (IHA ms' sb Hsb) | exact (IHb _ _ (sub_marks_up _ _ _ _ Hsb))].
    - cbn [subst]. apply G_Ann; [exact (IHu ms' sb Hsb) | exact (IHA ms' sb Hsb)].
    - cbn [subst]. apply G_ElimVoid; [exact (IHC ms' sb Hsb) | exact (IHe ms' sb Hsb)].
    - cbn [subst]. apply G_Pair; [exact (IHa ms' sb Hsb) | exact (IHb ms' sb Hsb)].
    - cbn [subst]. apply G_ElimUnit; [exact (IHC ms' sb Hsb) | exact (IHc ms' sb Hsb) | exact (IHu ms' sb Hsb)].
    - cbn [subst]. apply G_ElimBool;
        [exact (IHC ms' sb Hsb) | exact (IHt ms' sb Hsb) | exact (IHf ms' sb Hsb) | exact (IHb ms' sb Hsb)].
    - cbn [subst]. apply G_Fst. exact (IHp ms' sb Hsb).
    - cbn [subst]. apply G_Snd. exact (IHp ms' sb Hsb).
    (* a match: an origin stays an origin with the same fields *)
    - cbn [subst]. apply G_Case; [exact (IHP ms' sb Hsb) | exact (IHx ms' sb Hsb) | ].
      intros j b' Hj. cbv zeta. rewrite nth_error_map in Hj.
      destruct (nth_error bs j) as [b|] eqn:Ej; [ | discriminate Hj]. injection Hj as <-.
      specialize (IHbs j b Ej). cbv zeta in IHbs.
      destruct (origin ms x) eqn:Eo.
      + rewrite (branch_fields_origin ms ms' D x (subst sb x) Eo (origin_subst_gen _ _ _ _ Hsb Eo)).
        destruct (peel_spec (nth j (branch_fields sg ms D x) []) b) as (n & b0 & Hn & -> & Hp).
        rewrite Hp in IHbs. cbn [fst snd] in IHbs.
        rewrite subst_lams, peel_lams by exact Hn. apply peel_guarded. apply IHbs.
        pose proof (sub_marks_upn (rev (map field_mark (firstn n (nth j (branch_fields sg ms D x) []))))
                      ms ms' sb Hsb) as Hu.
        rewrite length_peel_marks in Hu by exact Hn. exact Hu.
      + rewrite (branch_fields_nonorigin ms D x Eo), nth_nil_fields in IHbs. cbn [peel fst snd] in IHbs.
        apply peel_guarded. exact (IHbs ms' sb Hsb).
    - destruct t; try discriminate Ht; apply G_Atom; reflexivity.
  Qed.

  Corollary guarded_rename : forall ms ms' r t, guarded ms t -> (forall i, mark_at ms' (r i) = mark_at ms i) ->
    guarded ms' (rename r t).
  Proof.
    intros ms ms' r t H Hr. rewrite rename_as_subst. apply (guarded_subst_gen ms t H).
    intros i. left. exists (r i). split; [reflexivity | apply Hr].
  Qed.

  Corollary guarded_lift : forall E ms t, guarded ms t -> guarded (E ++ ms) (lift (length E) t).
  Proof.
    intros E ms t H. apply (guarded_rename ms); [exact H | ].
    intros i. unfold mark_at. rewrite app_nth2 by lia. f_equal. lia.
  Qed.

  (** The same, with the replacing terms guarded under the target marks. *)
  Definition sub_large (ms ms' : list mark) (sb : nat -> term) : Prop :=
    forall i, (exists j, sb i = Var j /\ mark_at ms' j = mark_at ms i) \/
              (mark_at ms i = Large /\ guarded ms' (sb i)).

  Corollary guarded_subst_large : forall ms ms' sb t, guarded ms t -> sub_large ms ms' sb ->
    guarded ms' (subst sb t).
  Proof.
    intros ms ms' sb t H Hsb. apply (guarded_subst_gen ms t H).
    intros i. destruct (Hsb i) as [Hj | [Hl Hg]]; [left; exact Hj | right; split; [exact Hl | ]].
    intros E. exact (guarded_lift E ms' (sb i) Hg).
  Qed.

  (** β: the bound variable is [Large]. *)
  Corollary guarded_subst1 : forall ms b u, guarded (Large :: ms) b -> guarded ms u -> guarded ms (subst1 b u).
  Proof.
    intros ms b u Hb Hu. apply (guarded_subst_large (Large :: ms)); [exact Hb | ].
    intros [|i]; [right; split; [reflexivity | exact Hu] | left; exists i; split; reflexivity].
  Qed.

  Lemma mark_at_nil : forall i, mark_at [] i = Large.
  Proof. intros [|i]; reflexivity. Qed.

  (** A term closed above [n], with guarded terms for its [n] variables. *)
  Lemma guarded_subst_closed : forall ms n v sb, closed_above n v = true ->
    (forall i, i < n -> guarded ms (sb i)) -> guarded ms (subst sb v).
  Proof.
    intros ms n v sb Hc Hs.
    rewrite (subst_ext_closed_above v n sb (fun i => if Nat.ltb i n then sb i else Tt) Hc)
      by (intros i Hi; rewrite (proj2 (Nat.ltb_lt i n) Hi); reflexivity).
    apply (guarded_subst_large []).
    - exact (guarded_nonself sg k v [] [] (fun i _ => f_equal is_self (mark_at_nil i))).
    - intros i. right. split; [apply mark_at_nil | ].
      destruct (Nat.ltb i n) eqn:E; [apply Hs, Nat.ltb_lt, E | apply G_Atom; reflexivity].
  Qed.

  Corollary guarded_closed : forall ms t, closed t = true -> guarded ms t.
  Proof.
    intros ms t H. rewrite <- (subst_var t). apply (guarded_subst_closed ms 0); [exact H | intros i Hi; lia].
  Qed.

  (** ** The contractions of the signature *)

  Lemma in_firstn_l : forall {A : Type} n (l : list A) x, In x (firstn n l) -> In x l.
  Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.

  Lemma in_skipn_l : forall {A : Type} n (l : list A) x, In x (skipn n l) -> In x l.
  Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. right. exact H. Qed.

  Lemma in_vars : forall base n v, In v (vars base n) -> exists j, v = Var (base + j) /\ j < n.
  Proof.
    intros base n. induction n as [|n IH]; intros v H; [destruct H | ].
    destruct H as [<- | H]; [exists n; split; [reflexivity | lia] | ].
    destruct (IH v H) as (j & -> & Hj). exists j. split; [reflexivity | lia].
  Qed.

  Lemma mark_at_large_prefix : forall m ms i, i < m -> mark_at (repeat Large m ++ ms) i = Large.
  Proof.
    intros m ms i H. unfold mark_at. rewrite app_nth1 by (rewrite repeat_length; exact H).
    apply nth_repeat.
  Qed.

  Lemma guarded_lift_large : forall m ms t, guarded ms t -> guarded (repeat Large m ++ ms) (lift m t).
  Proof.
    intros m ms t H. pose proof (guarded_lift (repeat Large m) ms t H) as G.
    rewrite repeat_length in G. exact G.
  Qed.

  (** The hypothesis of a recursive field: the eliminator applied under
      [Large] binders to guarded terms, to the closed indices of the
      description instantiated with guarded terms, and to the field. *)
  Lemma guarded_hyp : forall ms D s pre env Bs vs a,
    Forall (guarded ms) pre -> Forall (guarded ms) env -> guarded ms a ->
    forallb (closed_above (length env + length Bs)) vs = true ->
    guarded ms (hyp D s pre env Bs vs a).
  Proof.
    intros ms D s pre env Bs vs a Hp He Ha Hvs. unfold hyp. cbv zeta.
    apply guarded_lams. apply guarded_apps; [apply G_Atom; reflexivity | ].
    rewrite Forall_forall in Hp, He. apply Forall_forall. intros x Hx.
    apply in_app_or in Hx as [Hx | Hx]; [ | apply in_app_or in Hx as [Hx | [<- | []]]].
    - apply in_map_iff in Hx as (p & <- & Hpx). apply guarded_lift_large, Hp, Hpx.
    - apply in_map_iff in Hx as (v & <- & Hv).
      apply (guarded_subst_closed _ (length env + length Bs)); [exact (proj1 (forallb_forall _ _) Hvs v Hv) | ].
      intros i Hi. unfold inst. destruct (Nat.ltb i (length Bs)) eqn:E.
      + apply G_Var. rewrite mark_at_large_prefix by (apply Nat.ltb_lt, E). reflexivity.
      + apply Nat.ltb_ge in E. apply guarded_lift_large, He, nth_In. lia.
    - apply guarded_apps; [apply guarded_lift_large, Ha | ].
      apply Forall_forall. intros x Hx. destruct (in_vars 0 _ x Hx) as (j & -> & Hj).
      apply G_Var. rewrite mark_at_large_prefix by lia. reflexivity.
  Qed.

  Lemma guarded_iota_args : forall ms D s pre fs env xs,
    Forall (guarded ms) pre -> Forall (guarded ms) env -> Forall (guarded ms) xs ->
    fields_closed (length env) fs = true ->
    Forall (guarded ms) (iota_args D s pre env fs xs).
  Proof.
    intros ms D s pre fs. induction fs as [|fd fs IH]; intros env xs Hp He Hx Hc; [destruct xs; constructor | ].
    destruct xs as [|a xs]; [destruct fd; constructor | ].
    pose proof (Forall_inv Hx) as Ha. pose proof (Forall_inv_tail Hx) as Hxs.
    cbn [fields_closed] in Hc. apply andb_prop in Hc as [Hfd Hc].
    destruct fd as [A | Bs vs]; cbn [iota_args].
    - constructor; [exact Ha | apply IH; [exact Hp | constructor; assumption | exact Hxs | exact Hc]].
    - cbn [field_closed] in Hfd. apply andb_prop in Hfd as [_ Hvs].
      constructor; [exact Ha | constructor; [apply guarded_hyp; assumption | ]].
      apply IH; [exact Hp | constructor; assumption | exact Hxs | exact Hc].
  Qed.

  (** ι of an eliminator instance: the method and the arguments come from
      the guarded spine, the rest from closed descriptions. *)
  Lemma guarded_iota : forall ms t u, iota sg t = Some u -> guarded ms t -> guarded ms u.
  Proof.
    intros ms t u H Ht. unfold iota in H.
    destruct (elim_view sg t) as [[[D s] d]|] eqn:Ev; [ | discriminate H].
    destruct (elim_view_spec _ _ _ _ _ Ev) as (Eh & Hlen & Hd).
    rewrite <- (apps_spine t), Eh in Ht. destruct (guarded_apps_inv _ _ _ Ht eq_refl) as [_ Ha].
    set (a := spine_args t) in *. unfold iota_at in H. cbv zeta in H.
    destruct (ctor_view D d (last a (Var 0))) as [[[i cd] xs]|] eqn:Ec; [ | discriminate H].
    destruct (nth_error (firstn (length (ind_ctors d)) (skipn (S (length (ind_params d))) a)) i)
      as [m|] eqn:Em; [ | discriminate H].
    injection H as <-. rewrite Forall_forall in Ha.
    assert (Hne : a <> []) by (intros E; rewrite E in Hlen; unfold elim_arity in Hlen; cbn [length] in Hlen; lia).
    assert (Hlast : In (last a (Var 0)) a)
      by (rewrite (app_removelast_last (Var 0) Hne) at 2; apply in_or_app; right; left; reflexivity).
    destruct (ctor_view_spec _ _ _ _ _ _ Ec) as (c & ps & Ex & Hc & Hps & Hxs).
    pose proof (Ha _ Hlast) as Hx. rewrite Ex in Hx.
    destruct (guarded_apps_inv _ _ _ Hx eq_refl) as [_ Hpx]. apply Forall_app in Hpx as [_ Hxs'].
    apply guarded_apps.
    - apply Ha. apply nth_error_In in Em. exact (in_skipn_l _ _ _ (in_firstn_l _ _ _ Em)).
    - apply guarded_iota_args.
      + apply Forall_forall. intros x Hx'.
        exact (Ha x (in_firstn_l (S (length (ind_params d)) + length (ind_ctors d)) _ _ Hx')).
      + apply Forall_forall. intros x Hx'. rewrite rev'_rev, <- in_rev in Hx'. exact (Ha x (in_firstn_l _ _ _ Hx')).
      + exact Hxs'.
      + rewrite rev'_rev, length_rev, length_firstn.
        replace (Nat.min (length (ind_params d)) (length a)) with (length (ind_params d))
          by (unfold elim_arity in Hlen; lia).
        unfold ind_closed in Hd. cbv zeta in Hd. apply andb_prop in Hd as [_ Hcs].
        pose proof (find_ctor_closed _ _ _ _ _ Hcs Hc) as Hcd. unfold ctor_closed in Hcd.
        apply andb_prop in Hcd as [Hf _]. exact Hf.
  Qed.

  (** The unfolding of a [fix]: its function is [Large] in the guard. *)
  Lemma guarded_fix_unfold : forall ms t u, fix_unfold t = Some u -> guarded ms t -> guarded ms u.
  Proof.
    intros ms t u H Ht. unfold fix_unfold in H.
    destruct (fix_view t) as [[[A k'] b]|] eqn:Ev; [ | discriminate H].
    destruct (fix_view_spec _ _ _ _ Ev) as [Eh _].
    assert (E : u = apps (subst1 b (Fix A k' b)) (spine_args t)).
    { unfold fix_at in H.
      repeat match type of H with context [match ?e with _ => _ end] => destruct e end;
        try discriminate H.
      injection H as <-. reflexivity. }
    subst u. rewrite <- (apps_spine t), Eh in Ht. destruct (guarded_apps_inv _ _ _ Ht eq_refl) as [Hf Hargs].
    apply guarded_inv in Hf. cbn [ginv] in Hf. destruct Hf as [HA Hb].
    apply guarded_apps; [ | exact Hargs].
    apply guarded_subst1; [exact Hb | ]. apply G_Fix; assumption.
  Qed.

  Lemma guarded_spine_iota : forall ms t u, spine_iota sg t = Some u -> guarded ms t -> guarded ms u.
  Proof.
    intros ms t u H Ht. unfold spine_iota in H. destruct (iota sg t) as [u'|] eqn:E.
    - injection H as <-. exact (guarded_iota ms t u' E Ht).
    - exact (guarded_fix_unfold ms t u H Ht).
  Qed.

  (** ι of a match: the scrutinee is a constructor spine, no origin, so
      the branch was checked without fields. *)
  Lemma guarded_case_iota : forall ms t u, case_iota sg t = Some u -> guarded ms t -> guarded ms u.
  Proof.
    intros ms t u H Ht. destruct (case_iota_case _ _ _ H) as (D & s & P & x & bs & ->).
    unfold case_iota in H. destruct (sig_ind sg D) as [d|] eqn:Ed; [ | discriminate H].
    destruct (ctor_view D d x) as [[[i cd] xs]|] eqn:Ec; [ | discriminate H].
    destruct (nth_error bs i) as [b|] eqn:Eb; cbn [option_map] in H; [ | discriminate H].
    injection H as <-. apply guarded_inv in Ht. cbn [ginv] in Ht. destruct Ht as (_ & Hx & Hbs).
    destruct (ctor_view_spec _ _ _ _ _ _ Ec) as (c & ps & Ex & _ & _ & _).
    assert (Eo : origin ms x = false).
    { rewrite Ex. unfold origin, sub_arg. rewrite spine_head_apps. cbn [spine_head]. rewrite orb_false_r.
      destruct (ps ++ xs) as [|y l] using rev_ind; [reflexivity | rewrite apps_snoc; reflexivity]. }
    specialize (Hbs i b Eb). rewrite (branch_fields_nonorigin ms D x Eo), nth_nil_fields in Hbs.
    cbn [peel fst snd] in Hbs. rewrite Ex in Hx.
    destruct (guarded_apps_inv _ _ _ Hx eq_refl) as [_ Hpx]. apply Forall_app in Hpx as [_ Hxs].
    apply guarded_apps; assumption.
  Qed.

  (** ** One step of reduction *)

  Lemma sub_arg_red1 : forall ms a a', red1 sg a a' -> sub_arg ms a = true -> sub_arg ms a' = true.
  Proof.
    intros ms a a' H Ha. unfold sub_arg in *. destruct (spine_head a) eqn:Eh; try discriminate Ha.
    rewrite <- (apps_spine a), Eh in H. destruct (red1_var_spine _ _ _ _ H) as (l' & -> & Hl).
    rewrite spine_head_apps, spine_args_apps. change (spine_args (Var n)) with (@nil term).
    cbn [spine_head app]. rewrite Hl. exact Ha.
  Qed.

  Lemma origin_red1 : forall ms x x', red1 sg x x' -> origin ms x = true -> origin ms x' = true.
  Proof.
    intros ms x x' H Hx. unfold origin in *. apply orb_true_iff in Hx as [Hx | Hx].
    - destruct x; try discriminate Hx. exfalso. exact (red1_var _ _ _ H).
    - rewrite (sub_arg_red1 _ _ _ H Hx), orb_true_r. reflexivity.
  Qed.

  (** The branches of a match whose scrutinee reduces: an origin stays
      one, and a branch checked without fields may get some. *)
  Lemma branches_scr : forall ms D x x' bs,
    (forall j b, nth_error bs j = Some b ->
       guarded (fst (peel ms (nth j (branch_fields sg ms D x) []) b))
               (snd (peel ms (nth j (branch_fields sg ms D x) []) b))) ->
    (origin ms x = true -> origin ms x' = true) ->
    forall j b, nth_error bs j = Some b ->
      guarded (fst (peel ms (nth j (branch_fields sg ms D x') []) b))
              (snd (peel ms (nth j (branch_fields sg ms D x') []) b)).
  Proof.
    intros ms D x x' bs H Ho. destruct (origin ms x) eqn:Eo.
    - rewrite (branch_fields_origin ms ms D x x' Eo (Ho eq_refl)). exact H.
    - intros j b Hj. specialize (H j b Hj).
      rewrite (branch_fields_nonorigin ms D x Eo), nth_nil_fields in H. apply peel_guarded. exact H.
  Qed.

  Lemma nth_error_app_other : forall (l1 l2 : list term) a a' j, j <> length l1 ->
    nth_error (l1 ++ a :: l2) j = nth_error (l1 ++ a' :: l2) j.
  Proof.
    intros l1 l2 a a' j H. destruct (Nat.lt_ge_cases j (length l1)) as [Hj | Hj].
    - rewrite !nth_error_app1 by exact Hj. reflexivity.
    - rewrite !nth_error_app2 by exact Hj. replace (j - length l1) with (S (j - length l1 - 1)) by lia.
      reflexivity.
  Qed.

  (** The two statements of the induction: the guard of a term peeled
      with any fields, and the arguments of a spine headed by a
      variable, which reduce one at a time and stay guarded. *)
  Definition red_peel (t t' : term) : Prop :=
    forall ms fds, guarded (fst (peel ms fds t)) (snd (peel ms fds t)) ->
                   guarded (fst (peel ms fds t')) (snd (peel ms fds t')).

  Definition red_args (t t' : term) : Prop :=
    forall ms i args, t = apps (Var i) args -> Forall (guarded ms) args ->
    exists args', t' = apps (Var i) args' /\ Forall (guarded ms) args' /\ length args' = length args /\
      forall j, sub_arg ms (nth j args (Var 0)) = true -> sub_arg ms (nth j args' (Var 0)) = true.

  Lemma red_peel_nolam : forall t t', (forall b, t <> Lam b) ->
    (forall ms, guarded ms t -> guarded ms t') -> red_peel t t'.
  Proof.
    intros t t' Hl H ms fds Hg. rewrite (peel_nolam ms fds t Hl) in Hg. apply peel_guarded, H, Hg.
  Qed.

  Lemma red_args_novar : forall t t', (forall i, spine_head t <> Var i) -> red_args t t'.
  Proof. intros t t' H ms i args E _. exfalso. apply (H i). rewrite E, spine_head_apps. reflexivity. Qed.

  (** The argument at a position of a call keeps its sub_arg when the
      arguments before the last one reduce, or the last one does. *)
  Lemma sub_arg_snoc : forall ms l l' a a' j, length l' = length l ->
    (forall j, sub_arg ms (nth j l (Var 0)) = true -> sub_arg ms (nth j l' (Var 0)) = true) ->
    (sub_arg ms a = true -> sub_arg ms a' = true) ->
    sub_arg ms (nth j (l ++ [a]) (Var 0)) = true -> sub_arg ms (nth j (l' ++ [a']) (Var 0)) = true.
  Proof.
    intros ms l l' a a' j Hlen Hl Ha H. destruct (Nat.lt_ge_cases j (length l)) as [Hj | Hj].
    - rewrite app_nth1 in H by exact Hj. rewrite app_nth1 by lia. exact (Hl j H).
    - rewrite app_nth2 in H by exact Hj. rewrite app_nth2 by lia. rewrite Hlen.
      destruct (j - length l) as [|j']; [exact (Ha H) | destruct j'; exact H].
  Qed.

  Local Ltac nolam := apply red_peel_nolam; [intros ? ?; discriminate | intros ms Hg].
  Local Ltac novar := apply red_args_novar; intros ? ?; discriminate.
  Local Ltac inv Hg := apply guarded_inv in Hg; cbn [ginv] in Hg.

  Lemma red1_peel_args : forall t t', red1 sg t t' -> red_peel t t' /\ red_args t t'.
  Proof.
    induction 1 as
      [ b u | t A | C c | C t f | C t f | a b | a b
      | A A' B H [IH _] | A B B' H [IH _] | b b' H [IH _]
      | f f' a H [IH IHq] | f a a' H [IH _]
      | t t' A H [IH _] | t A A' H [IH _]
      | C C' e H [IH _] | C e e' H [IH _]
      | C C' c u H [IH _] | C c c' u H [IH _] | C c u u' H [IH _]
      | C C' t f b H [IH _] | C t t' f b H [IH _] | C t f f' b H [IH _] | C t f b b' H [IH _]
      | A A' B H [IH _] | A B B' H [IH _]
      | a a' b H [IH _] | a b b' H [IH _]
      | p p' H [IH _] | p p' H [IH _]
      | D s P P' x bs H [IH _] | D s P x x' bs H [IH _] | D s P x bs1 b b' bs2 H [IH _]
      | A A' k' b H [IH _] | A k' b b' H [IH _]
      | g b H | t u H | t u H ].
    (* β *)
    - split; [ | novar]. nolam. destruct (guarded_app_inv ms _ _ Hg eq_refl) as [Hl Hu].
      inv Hl. exact (guarded_subst1 ms b u Hl Hu).
    (* the annotation, the primitives, the projections *)
    - split; [ | novar]. nolam. inv Hg. apply Hg.
    - split; [ | novar]. nolam. inv Hg. apply Hg.
    - split; [ | novar]. nolam. inv Hg. apply Hg.
    - split; [ | novar]. nolam. inv Hg. apply Hg.
    - split; [ | novar]. nolam. inv Hg. inv Hg. apply Hg.
    - split; [ | novar]. nolam. inv Hg. inv Hg. apply Hg.
    (* Π *)
    - split; [ | novar]. nolam. inv Hg. destruct Hg as [HA HB]. apply G_Pi; [exact (IH ms [] HA) | exact HB].
    - split; [ | novar]. nolam. inv Hg. destruct Hg as [HA HB].
      apply G_Pi; [exact HA | exact (IH (Large :: ms) [] HB)].
    (* λ: peeled with the mark of a field, or entered with Large *)
    - split; [ | novar]. intros ms [|fd fds] Hg; cbn [peel fst snd] in Hg |- *.
      + inv Hg. apply G_Lam. exact (IH (Large :: ms) [] Hg).
      + exact (IH (field_mark fd :: ms) fds Hg).
    (* the function of an application: a call stays a call *)
    - split.
      + nolam. destruct (self_headed ms (App f a)) eqn:Es.
        * destruct (guarded_self_inv ms _ Hg Es) as (i & args & E & Hi & Hk & Hsub & Hargs).
          destruct (apps_var_snoc_inv i args f a (eq_sym E)) as (l0 & -> & ->).
          apply Forall_app in Hargs as [Hl0 Ha]. pose proof (Forall_inv Ha) as Ha'.
          destruct (IHq ms i l0 eq_refl Hl0) as (l' & -> & Hl' & Hlen & Hsubs).
          rewrite <- apps_snoc. apply G_Call; [exact Hi | rewrite length_app in *; cbn [length] in *; lia | | ].
          -- exact (sub_arg_snoc ms l0 l' a a k Hlen Hsubs (fun H => H) Hsub).
          -- intros x Hx. apply in_app_or in Hx as [Hx | [<- | []]]; [ | exact Ha'].
             rewrite Forall_forall in Hl'. exact (Hl' x Hx).
        * destruct (guarded_app_inv ms _ _ Hg Es) as [Hf Ha]. apply guarded_app; [exact (IH ms [] Hf) | exact Ha].
      + intros ms i args E Hargs. destruct (apps_var_snoc_inv i args f a (eq_sym E)) as (l0 & -> & ->).
        apply Forall_app in Hargs as [Hl0 Ha].
        destruct (IHq ms i l0 eq_refl Hl0) as (l' & -> & Hl' & Hlen & Hsubs).
        exists (l' ++ [a]). split; [rewrite apps_snoc; reflexivity | ].
        split; [apply Forall_app; split; assumption | ].
        split; [rewrite !length_app, Hlen; reflexivity | ].
        intros j Hj. exact (sub_arg_snoc ms l0 l' a a j Hlen Hsubs (fun H => H) Hj).
    (* the argument of an application *)
    - split.
      + nolam. destruct (self_headed ms (App f a)) eqn:Es.
        * destruct (guarded_self_inv ms _ Hg Es) as (i & args & E & Hi & Hk & Hsub & Hargs).
          destruct (apps_var_snoc_inv i args f a (eq_sym E)) as (l0 & -> & ->).
          apply Forall_app in Hargs as [Hl0 Ha]. pose proof (IH ms [] (Forall_inv Ha)) as Ha'.
          change (guarded ms (App (apps (Var i) l0) a')). rewrite <- apps_snoc.
          apply G_Call; [exact Hi | rewrite length_app in *; cbn [length] in *; lia | | ].
          -- exact (sub_arg_snoc ms l0 l0 a a' k eq_refl (fun j H => H) (sub_arg_red1 ms a a' H) Hsub).
          -- intros x Hx. apply in_app_or in Hx as [Hx | [<- | []]]; [ | exact Ha'].
             rewrite Forall_forall in Hl0. exact (Hl0 x Hx).
        * destruct (guarded_app_inv ms _ _ Hg Es) as [Hf Ha]. apply guarded_app; [exact Hf | exact (IH ms [] Ha)].
      + intros ms i args E Hargs. destruct (apps_var_snoc_inv i args f a (eq_sym E)) as (l0 & -> & ->).
        apply Forall_app in Hargs as [Hl0 Ha].
        exists (l0 ++ [a']). split; [rewrite apps_snoc; reflexivity | ].
        split; [apply Forall_app; split; [exact Hl0 | constructor; [exact (IH ms [] (Forall_inv Ha)) | constructor]] | ].
        split; [rewrite !length_app; reflexivity | ].
        intros j Hj. exact (sub_arg_snoc ms l0 l0 a a' j eq_refl (fun j H => H) (sub_arg_red1 ms a a' H) Hj).
    (* the annotation *)
    - split; [ | novar]. nolam. inv Hg. destruct Hg as [Ht HA]. apply G_Ann; [exact (IH ms [] Ht) | exact HA].
    - split; [ | novar]. nolam. inv Hg. destruct Hg as [Ht HA]. apply G_Ann; [exact Ht | exact (IH ms [] HA)].
    (* the eliminators of the primitives *)
    - split; [ | novar]. nolam. inv Hg. destruct Hg as [HC He]. apply G_ElimVoid; [exact (IH ms [] HC) | exact He].
    - split; [ | novar]. nolam. inv Hg. destruct Hg as [HC He]. apply G_ElimVoid; [exact HC | exact (IH ms [] He)].
    - split; [ | novar]. nolam. inv Hg. destruct Hg as (HC & Hc & Hu).
      apply G_ElimUnit; [exact (IH ms [] HC) | exact Hc | exact Hu].
    - split; [ | novar]. nolam. inv Hg. destruct Hg as (HC & Hc & Hu).
      apply G_ElimUnit; [exact HC | exact (IH ms [] Hc) | exact Hu].
    - split; [ | novar]. nolam. inv Hg. destruct Hg as (HC & Hc & Hu).
      apply G_ElimUnit; [exact HC | exact Hc | exact (IH ms [] Hu)].
    - split; [ | novar]. nolam. inv Hg. destruct Hg as (HC & Ht & Hf & Hb).
      apply G_ElimBool; [exact (IH ms [] HC) | exact Ht | exact Hf | exact Hb].
    - split; [ | novar]. nolam. inv Hg. destruct Hg as (HC & Ht & Hf & Hb).
      apply G_ElimBool; [exact HC | exact (IH ms [] Ht) | exact Hf | exact Hb].
    - split; [ | novar]. nolam. inv Hg. destruct Hg as (HC & Ht & Hf & Hb).
      apply G_ElimBool; [exact HC | exact Ht | exact (IH ms [] Hf) | exact Hb].
    - split; [ | novar]. nolam. inv Hg. destruct Hg as (HC & Ht & Hf & Hb).
      apply G_ElimBool; [exact HC | exact Ht | exact Hf | exact (IH ms [] Hb)].
    (* Σ, pairs, projections *)
    - split; [ | novar]. nolam. inv Hg. destruct Hg as [HA HB]. apply G_Sigma; [exact (IH ms [] HA) | exact HB].
    - split; [ | novar]. nolam. inv Hg. destruct Hg as [HA HB].
      apply G_Sigma; [exact HA | exact (IH (Large :: ms) [] HB)].
    - split; [ | novar]. nolam. inv Hg. destruct Hg as [Ha Hb]. apply G_Pair; [exact (IH ms [] Ha) | exact Hb].
    - split; [ | novar]. nolam. inv Hg. destruct Hg as [Ha Hb]. apply G_Pair; [exact Ha | exact (IH ms [] Hb)].
    - split; [ | novar]. nolam. inv Hg. apply G_Fst. exact (IH ms [] Hg).
    - split; [ | novar]. nolam. inv Hg. apply G_Snd. exact (IH ms [] Hg).
    (* match: the motive, the scrutinee, a branch *)
    - split; [ | novar]. nolam. inv Hg. destruct Hg as (HP & Hx & Hbs).
      apply G_Case; [exact (IH ms [] HP) | exact Hx | exact Hbs].
    - split; [ | novar]. nolam. inv Hg. destruct Hg as (HP & Hx & Hbs).
      apply G_Case; [exact HP | exact (IH ms [] Hx) | ].
      exact (branches_scr ms D x x' bs Hbs (origin_red1 ms x x' H)).
    - split; [ | novar]. nolam. inv Hg. destruct Hg as (HP & Hx & Hbs).
      apply G_Case; [exact HP | exact Hx | ]. intros j c Hj. cbv zeta.
      destruct (Nat.eq_dec j (length bs1)) as [-> | Hne].
      + rewrite nth_error_app2, Nat.sub_diag in Hj by lia. injection Hj as <-.
        apply IH. apply Hbs. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
      + apply Hbs. rewrite (nth_error_app_other bs1 bs2 b b' j Hne). exact Hj.
    (* fix: its type, its body *)
    - split; [ | novar]. nolam. inv Hg. destruct Hg as [HA Hb]. apply G_Fix; [exact (IH ms [] HA) | exact Hb].
    - split; [ | novar]. nolam. inv Hg. destruct Hg as [HA Hb].
      apply G_Fix; [exact HA | exact (IH (Large :: ms) [] Hb)].
    (* δ: a closed body *)
    - split; [ | novar]. nolam. exact (guarded_closed ms b (sig_delta_closed _ _ _ H)).
    (* the contractions of spines *)
    - split.
      + apply red_peel_nolam; [ | intros ms Hg; exact (guarded_spine_iota ms t u H Hg)].
        intros c E. destruct (spine_iota_app _ _ _ H) as (f & a & E'). rewrite E' in E. discriminate E.
      + intros ms i args E _. exfalso. rewrite (spine_iota_var sg t i) in H; [discriminate H | ].
        rewrite E, spine_head_apps. reflexivity.
    (* ι of a match *)
    - destruct (case_iota_case _ _ _ H) as (D & s & P & x & bs & ->). split; [ | novar].
      apply red_peel_nolam; [intros ? ?; discriminate | intros ms Hg; exact (guarded_case_iota ms _ u H Hg)].
  Qed.

  (** The guard survives one step of reduction. *)
  Theorem guarded_red1 : forall ms t t', guarded ms t -> red1 sg t t' -> guarded ms t'.
  Proof. intros ms t t' Hg H. exact (proj1 (red1_peel_args t t' H) ms [] Hg). Qed.

  Lemma red1_lams : forall n X w, red1 sg (lams n X) w -> exists X', w = lams n X' /\ red1 sg X X'.
  Proof.
    induction n as [|n IH]; intros X w H; [exists w; split; [reflexivity | exact H] | ].
    cbn [lams] in H. inversion H; subst.
    - destruct (IH X b' H1) as (X' & -> & HX). exists X'. split; [reflexivity | exact HX].
    - discriminate H0.
    - discriminate H0.
  Qed.

  (** A step in a guarded body of a [fix] is under its leading λ. *)
  Theorem fix_guarded_red1 : forall b b', fix_guarded sg k b -> red1 sg b b' -> fix_guarded sg k b'.
  Proof.
    intros b b' (body & -> & Hg) H. destruct (red1_lams _ _ _ H) as (body' & -> & Hb).
    exists body'. split; [reflexivity | exact (guarded_red1 _ _ _ Hg Hb)].
  Qed.
End GuardRed.
