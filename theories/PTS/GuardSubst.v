(** * The guard under substitution

    The guard of a [fix] marks the variables of the body, and every
    variable of the enclosing context gets [Large].  A substitution for
    those variables gives terms that cannot mention the function
    ([below]), so a guarded body stays guarded ([guarded_subst]), and so
    does the body of a [fix] under substitution and renaming
    ([fix_guarded_subst], [fix_guarded_rename]).  Weakening and
    substitution for the typing rules (PTS.TypingSubst) and the guard
    under reduction (PTS.GuardRed) rest on it; it needs only the guard
    and the substitution laws. *)

From Stdlib Require Import List Arith Lia Bool.
From Stdlib Require String.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Telescope Signature Reduction SubstLaws Guard.

Section GuardSubst.
  Variable sg : signature.
  Variable k : nat.
  Local Notation guarded := (Guarded sg k).

  Lemma mark_at_ge : forall ms i, length ms <= i -> mark_at ms i = Large.
  Proof. intros ms i H. unfold mark_at. apply nth_overflow, H. Qed.

  Lemma field_mark_not_self : forall fd, is_self (field_mark fd) = false.
  Proof. intros [A | Bs vs]; reflexivity. Qed.

  Lemma peel_nolam : forall ms fds t, (forall b, t <> Lam b) -> peel ms fds t = (ms, t).
  Proof.
    intros ms [|fd fds] t H; [reflexivity | ].
    destruct t; try reflexivity. exfalso. exact (H t eq_refl).
  Qed.

  (** *** Terms that do not mention the function *)

  Definition nonself (ms : list mark) (t : term) : Prop :=
    forall i, free_in i t = true -> is_self (mark_at ms i) = false.

  (** Such a term is guarded, whatever leading λ are peeled off it with
      the marks of fields. *)
  Lemma guarded_nonself : forall t ms fds, nonself ms t ->
    guarded (fst (peel ms fds t)) (snd (peel ms fds t)).
  Proof.
    assert (G0 : forall t, (forall ms fds, nonself ms t -> guarded (fst (peel ms fds t)) (snd (peel ms fds t))) ->
                 forall ms, nonself ms t -> guarded ms t)
      by (intros t H ms Hn; exact (H ms [] Hn)).
    induction t using term_ind'; intros ms fds Hn.
    (* λ: peeled with the mark of its field, or entered with Large *)
    4: { destruct fds as [|fd fds]; cbn [peel fst snd].
         - apply G_Lam. apply (G0 _ IHt). intros [|i] Hi; [reflexivity | exact (Hn i Hi)].
         - apply IHt. intros [|i] Hi; [exact (field_mark_not_self fd) | exact (Hn i Hi)]. }
    all: rewrite peel_nolam by (intros ? ?; discriminate); cbn [fst snd].
    all: repeat match goal with
                | IH : forall ms fds, nonself ms ?t -> guarded (fst (peel ms fds ?t)) (snd (peel ms fds ?t)) |- _ =>
                    let H' := fresh "IH" in pose proof (G0 _ IH) as H'; clear IH
                end.
    all: lazymatch goal with
         | |- guarded _ (Var _) => apply G_Var; apply Hn; cbn [free_in]; apply Nat.eqb_refl
         | |- guarded _ (App _ _) => apply G_App
         | |- guarded _ (Pi _ _) => apply G_Pi
         | |- guarded _ (Sigma _ _) => apply G_Sigma
         | |- guarded _ (Fix _ _ _) => apply G_Fix
         | |- guarded _ (Ann _ _) => apply G_Ann
         | |- guarded _ (ElimVoid _ _) => apply G_ElimVoid
         | |- guarded _ (Pair _ _) => apply G_Pair
         | |- guarded _ (ElimUnit _ _ _) => apply G_ElimUnit
         | |- guarded _ (ElimBool _ _ _ _) => apply G_ElimBool
         | |- guarded _ (Fst _) => apply G_Fst
         | |- guarded _ (Snd _) => apply G_Snd
         | |- guarded _ (Case _ _ _ _ _) => apply G_Case
         | |- _ => apply G_Atom; reflexivity
         end.
    (* the head of an application is not the function *)
    all: try (unfold self_headed; destruct (spine_head (App _ _)) eqn:E; try reflexivity;
              apply Hn; apply free_in_head; exact E).
    (* the branches *)
    all: try (intros j b Hj; cbv zeta; rewrite Forall_forall in IHl;
              apply (IHl b (nth_error_In _ _ Hj)); intros i Hi; apply Hn; cbn [free_in];
              rewrite (proj2 (existsb_exists _ _) (ex_intro _ b (conj (nth_error_In _ _ Hj) Hi))), orb_true_r;
              reflexivity).
    (* the subterms, under a binder or not *)
    all: match goal with IH : forall ms, nonself ms ?t -> guarded ms ?t |- guarded _ ?t => apply IH end.
    all: first
      [ intros i Hi; apply Hn; cbn [free_in]; rewrite Hi, ?orb_true_r, ?orb_true_l; reflexivity
      | intros [|i] Hi; [reflexivity | ];
        match goal with |- is_self (mark_at (_ :: ?ms) (S ?i)) = _ => change (is_self (mark_at ms i) = false) end;
        apply Hn; cbn [free_in]; rewrite Hi, ?orb_true_r, ?orb_true_l; reflexivity ].
  Qed.

  (** *** Substitutions for the enclosing context *)

  (** [sb] keeps the variables marked in [ms] and replaces the others by
      terms of the context outside them. *)
  Definition below (ms : list mark) (sb : nat -> term) : Prop :=
    (forall i, i < length ms -> sb i = Var i) /\
    (forall i, length ms <= i -> exists t, sb i = lift (length ms) t).

  Lemma below_up : forall m ms sb, below ms sb -> below (m :: ms) (up_sub sb).
  Proof.
    intros m ms sb [Hl Hg]. split; cbn [length].
    - intros [|i] Hi; cbn [up_sub]; [reflexivity | ]. rewrite Hl by lia. reflexivity.
    - intros [|i] Hi; [lia | ]. cbn [up_sub]. destruct (Hg i ltac:(lia)) as [t ->].
      exists t. apply lift_lift.
  Qed.

  Lemma below_free : forall ms sb i j, below ms sb -> length ms <= i -> free_in j (sb i) = true ->
    length ms <= j.
  Proof.
    intros ms sb i j [_ Hg] Hi Hj. destruct (Hg i Hi) as [t E]. rewrite E in Hj.
    exact (free_in_lift _ _ _ Hj).
  Qed.

  Lemma below_nonself : forall ms sb i, below ms sb -> length ms <= i -> nonself ms (sb i).
  Proof.
    intros ms sb i Hb Hi j Hj. rewrite mark_at_ge by exact (below_free _ _ _ _ Hb Hi Hj). reflexivity.
  Qed.

  (** The head of a spine keeps its mark, or has none before and after. *)
  Lemma head_subst : forall ms sb t, below ms sb ->
    (exists i, i < length ms /\ spine_head t = Var i /\ spine_head (subst sb t) = Var i /\
       spine_args (subst sb t) = map (subst sb) (spine_args t)) \/
    ((forall i, spine_head t = Var i -> length ms <= i) /\
     (forall i, spine_head (subst sb t) = Var i -> length ms <= i)).
  Proof.
    intros ms sb t Hb. rewrite (spine_head_subst t sb).
    destruct (spine_head t) eqn:E.
    all: try (right; split; intros i Hi; cbn [subst spine_head] in Hi; discriminate Hi).
    - destruct (Nat.lt_ge_cases n (length ms)) as [H | H].
      + left. exists n. split; [exact H | ]. split; [reflexivity | ].
        cbn [subst]. rewrite (proj1 Hb n H). split; [reflexivity | ].
        exact (spine_args_subst_var t sb n E (proj1 Hb n H)).
      + right. split; [intros i Hi; injection Hi as <-; exact H | ].
        intros i Hi. cbn [subst] in Hi. exact (below_free _ _ _ _ Hb H (free_in_head _ _ Hi)).
    - exfalso. exact (spine_head_not_app _ _ _ E).
  Qed.

  Definition hd_self (ms : list mark) (h : term) : bool :=
    match h with Var i => is_self (mark_at ms i) | _ => false end.

  Definition hd_sub (ms : list mark) (h : term) (n : nat) : bool :=
    match h with
    | Var i => match mark_at ms i with Sub m => Nat.eqb n m | _ => false end
    | _ => false
    end.

  Lemma hd_self_large : forall ms h, (forall i, h = Var i -> length ms <= i) -> hd_self ms h = false.
  Proof.
    intros ms [] H; try reflexivity. cbn [hd_self]. rewrite mark_at_ge by (apply H; reflexivity). reflexivity.
  Qed.

  Lemma hd_sub_large : forall ms h n, (forall i, h = Var i -> length ms <= i) -> hd_sub ms h n = false.
  Proof.
    intros ms h n H; destruct h; try reflexivity. cbn [hd_sub]. rewrite mark_at_ge by (apply H; reflexivity). reflexivity.
  Qed.

  Lemma self_headed_subst : forall ms sb t, below ms sb -> self_headed ms (subst sb t) = self_headed ms t.
  Proof.
    intros ms sb t Hb.
    change (hd_self ms (spine_head (subst sb t)) = hd_self ms (spine_head t)).
    destruct (head_subst ms sb t Hb) as [(i & _ & E1 & E2 & _) | [H1 H2]].
    - rewrite E1, E2. reflexivity.
    - rewrite (hd_self_large _ _ H1), (hd_self_large _ _ H2). reflexivity.
  Qed.

  Lemma sub_arg_subst : forall ms sb a, below ms sb -> sub_arg ms (subst sb a) = sub_arg ms a.
  Proof.
    intros ms sb a Hb.
    change (hd_sub ms (spine_head (subst sb a)) (length (spine_args (subst sb a))) =
            hd_sub ms (spine_head a) (length (spine_args a))).
    destruct (head_subst ms sb a Hb) as [(i & _ & E1 & E2 & E3) | [H1 H2]].
    - rewrite E1, E2, E3, length_map. reflexivity.
    - rewrite (hd_sub_large _ _ _ H1), (hd_sub_large _ _ _ H2). reflexivity.
  Qed.

  Lemma is_arg_subst : forall ms sb x, below ms sb -> is_arg ms (subst sb x) = is_arg ms x.
  Proof.
    intros ms sb x Hb. destruct x; try reflexivity. cbn [subst].
    destruct (Nat.lt_ge_cases n (length ms)) as [H | H]; [rewrite (proj1 Hb n H); reflexivity | ].
    cbn [is_arg]. rewrite (mark_at_ge ms n H).
    destruct (sb n) eqn:E; try reflexivity.
    assert (Hj : length ms <= n0)
      by (apply (below_free ms sb n n0 Hb H); rewrite E; cbn [free_in]; apply Nat.eqb_refl).
    cbn [is_arg]. rewrite (mark_at_ge ms n0 Hj). reflexivity.
  Qed.

  Lemma branch_fields_subst : forall ms sb D x, below ms sb ->
    branch_fields sg ms D (subst sb x) = branch_fields sg ms D x.
  Proof.
    intros ms sb D x Hb. unfold branch_fields, origin. rewrite is_arg_subst, sub_arg_subst by exact Hb.
    reflexivity.
  Qed.

  (** A branch substituted, then peeled: either it is peeled as before,
      or a variable outside became a λ, and does not mention the
      function. *)
  Lemma peel_subst_guarded : forall fds ms b sb, below ms sb ->
    (forall sb', below (fst (peel ms fds b)) sb' ->
       guarded (fst (peel ms fds b)) (subst sb' (snd (peel ms fds b)))) ->
    guarded (fst (peel ms fds (subst sb b))) (snd (peel ms fds (subst sb b))).
  Proof.
    induction fds as [|fd fds IH]; intros ms b sb Hb H; [exact (H sb Hb) | ].
    assert (Hl : (exists b', b = Lam b') \/ (forall b', b <> Lam b'))
      by (destruct b; first [left; eexists; reflexivity | right; intros ? ?; discriminate]).
    destruct Hl as [[b' ->] | Hnl].
    - exact (IH _ _ _ (below_up _ _ _ Hb) H).
    - rewrite (peel_nolam ms (fd :: fds) b Hnl) in H. cbn [fst snd] in H.
      assert (Hs : (exists c, subst sb b = Lam c) \/ (forall c, subst sb b <> Lam c))
        by (destruct (subst sb b); first [left; eexists; reflexivity | right; intros ? ?; discriminate]).
      destruct Hs as [[c Ec] | Hs].
      + destruct (subst_lam_cases sb b c Ec) as [[b' ->] | (i & -> & Ei)]; [exfalso; exact (Hnl b' eq_refl) | ].
        destruct (Nat.lt_ge_cases i (length ms)) as [Hi | Hi];
          [rewrite (proj1 Hb i Hi) in Ei; discriminate Ei | ].
        cbn [subst]. exact (guarded_nonself (sb i) ms (fd :: fds) (below_nonself ms sb i Hb Hi)).
      + rewrite (peel_nolam ms (fd :: fds) _ Hs). exact (H sb Hb).
  Qed.

  Theorem guarded_subst : forall ms t, guarded ms t -> forall sb, below ms sb -> guarded ms (subst sb t).
  Proof.
    induction 1 as
      [ms i args Hself Hk Hsub _ IH | ms i Hi | ms f a Hs _ IHf _ IHa | ms b _ IHb
      | ms A B _ IHA _ IHB | ms A B _ IHA _ IHB | ms A k' b _ IHA _ IHb
      | ms u A _ IHu _ IHA | ms C e _ IHC _ IHe | ms a b _ IHa _ IHb
      | ms C c u _ IHC _ IHc _ IHu | ms C t f b _ IHC _ IHt _ IHf _ IHb
      | ms p _ IHp | ms p _ IHp
      | ms D s P x bs _ IHP _ IHx _ IHbs | ms t Ht ]; intros sb Hb.
    (* a recursive call: its head is kept, its arguments substituted *)
    - assert (Hi : i < length ms).
      { destruct (Nat.lt_ge_cases i (length ms)) as [Hi | Hi]; [exact Hi | ].
        rewrite (mark_at_ge _ _ Hi) in Hself. discriminate Hself. }
      rewrite subst_apps. cbn [subst]. rewrite (proj1 Hb i Hi).
      apply G_Call; [exact Hself | rewrite length_map; exact Hk | | ].
      + rewrite (nth_indep _ (Var 0) (subst sb (Var 0))) by (rewrite length_map; exact Hk).
        rewrite map_nth, sub_arg_subst by exact Hb. exact Hsub.
      + intros a Ha. apply in_map_iff in Ha as (a' & <- & Ha'). exact (IH a' Ha' sb Hb).
    (* a variable: kept, or replaced by a term without the function *)
    - cbn [subst]. destruct (Nat.lt_ge_cases i (length ms)) as [Hl | Hl].
      + rewrite (proj1 Hb i Hl). apply G_Var. exact Hi.
      + exact (guarded_nonself (sb i) ms [] (below_nonself _ _ _ Hb Hl)).
    - cbn [subst]. apply G_App; [ | exact (IHf sb Hb) | exact (IHa sb Hb)].
      change (App (subst sb f) (subst sb a)) with (subst sb (App f a)).
      rewrite self_headed_subst by exact Hb. exact Hs.
    - cbn [subst]. apply G_Lam. exact (IHb _ (below_up _ _ _ Hb)).
    - cbn [subst]. apply G_Pi; [exact (IHA sb Hb) | exact (IHB _ (below_up _ _ _ Hb))].
    - cbn [subst]. apply G_Sigma; [exact (IHA sb Hb) | exact (IHB _ (below_up _ _ _ Hb))].
    - cbn [subst]. apply G_Fix; [exact (IHA sb Hb) | exact (IHb _ (below_up _ _ _ Hb))].
    - cbn [subst]. apply G_Ann; [exact (IHu sb Hb) | exact (IHA sb Hb)].
    - cbn [subst]. apply G_ElimVoid; [exact (IHC sb Hb) | exact (IHe sb Hb)].
    - cbn [subst]. apply G_Pair; [exact (IHa sb Hb) | exact (IHb sb Hb)].
    - cbn [subst]. apply G_ElimUnit; [exact (IHC sb Hb) | exact (IHc sb Hb) | exact (IHu sb Hb)].
    - cbn [subst]. apply G_ElimBool; [exact (IHC sb Hb) | exact (IHt sb Hb) | exact (IHf sb Hb) | exact (IHb sb Hb)].
    - cbn [subst]. apply G_Fst. exact (IHp sb Hb).
    - cbn [subst]. apply G_Snd. exact (IHp sb Hb).
    (* a match: the scrutinee keeps its origin, so the branches their fields *)
    - cbn [subst]. apply G_Case; [exact (IHP sb Hb) | exact (IHx sb Hb) | ].
      intros j b' Hj. cbv zeta. rewrite nth_error_map in Hj.
      destruct (nth_error bs j) as [b|] eqn:Ej; [ | discriminate Hj]. injection Hj as <-.
      rewrite branch_fields_subst by exact Hb.
      apply peel_subst_guarded; [exact Hb | exact (IHbs j b Ej)].
    - destruct t; cbn [atomic] in Ht; try discriminate Ht; apply G_Atom; reflexivity.
  Qed.

  (** The variables of the context of a [fix] are outside the marks of
      its body. *)
  Theorem fix_guarded_subst : forall b sb, fix_guarded sg k b -> fix_guarded sg k (subst (up_sub sb) b).
  Proof.
    intros b sb (body & -> & Hg). exists (subst (upn (S (S k)) sb) body). split.
    - rewrite subst_lams. f_equal. apply subst_ext. intros n. apply up_sub_upn.
    - apply guarded_subst; [exact Hg | ].
      assert (Hl : length (entry_marks k) = S (S k))
        by (unfold entry_marks; cbn [length]; rewrite length_app, repeat_length; cbn [length]; lia).
      split; rewrite Hl.
      + intros i Hi. apply upn_lt, Hi.
      + intros i Hi. exists (sb (i - S (S k))).
        replace i with (S (S k) + (i - S (S k))) at 1 by lia. apply upn_ge.
  Qed.

  Corollary fix_guarded_rename : forall b r, fix_guarded sg k b -> fix_guarded sg k (rename (up_ren r) b).
  Proof. intros b r H. rewrite rename_up_as_subst. apply fix_guarded_subst, H. Qed.
End GuardSubst.
