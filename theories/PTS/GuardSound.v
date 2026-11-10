(** * Soundness of the guard of fix

    [guard] is the executable check; [Guarded] states the same rules as
    an inductive judgment over maximal spines, and [guard_sound] proves
    that the check implies it.  The meaning of the marks is stated
    independently of both, by a strict subterm relation on terms
    ([immediate], [strict_sub]): [u] is an immediate subterm of [v] when
    [v] reduces to a full constructor spine, read by [ctor_view] of
    PTS.Signature as ι reads it, and [u] is one of its recursive fields
    applied to arguments for all its positions.  A substitution
    [σ] of the variables respects the marks for the value [v] of the
    structural argument when [Arg] variables are [v] and [Sub m]
    variables are strict subterms of [v] once applied to [m] arguments.
    Then ([guard_invariants]):
    - the marks at the entry of the body are respected once the
      structural argument is [v] ([respects_entry]);
    - a binder keeps them respected, whatever it is bound to
      ([respects_binder]);
    - a guarded [match] on a structural origin that reduces to a
      constructor gives the branch of that constructor a guarded body,
      with marks respected by the fields of the constructor
      ([case_step]);
    - the structural argument of every call the guard accepts is then a
      strict subterm of [v] ([call_decreases]).
    These are the invariants along the evaluation of a fix applied to a
    constructor.  That [strict_sub] is well founded on well-typed values,
    and hence that guarded fixpoints terminate, is an open obligation
    (PTS/Contracts.v). *)

From Stdlib Require Import List Bool Arith Lia Relations.
From Stdlib Require String.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Signature Reduction SubstLaws Guard.

(** ** The check implies the judgment *)

Section Sound.
  Variable sg : signature.
  Variable k : nat.
  Local Notation guard := (guard sg k).
  Local Notation call_ok := (call_ok k).
  Local Notation guard_entry := (guard_entry sg k).
  Local Notation guard_fix := (guard_fix sg k).
  Local Notation Guarded := (Guarded sg k).
  Local Notation fix_guarded := (fix_guarded sg k).

  Lemma peel_with_peel : forall g b ms fds,
    peel_with g ms fds b = g (fst (peel ms fds b)) (snd (peel ms fds b)).
  Proof.
    intros g b. induction b; intros ms fds; destruct fds; try reflexivity. cbn. apply IHb.
  Qed.

  Lemma each_branch_ok : forall g bs ms fss u, each_branch g ms fss bs = Ok u ->
    forall j b, nth_error bs j = Some b -> peel_with g ms (nth j fss []) b = Ok tt.
  Proof.
    intros g bs. induction bs as [|b' bs IH]; intros ms fss u H j b Hj;
      [destruct j; discriminate Hj | ].
    cbn [each_branch] in H. bind_in H v Hv.
    destruct j as [|j]; cbn in Hj.
    - injection Hj as <-. destruct fss; cbn in Hv |- *; destruct v; exact Hv.
    - specialize (IH _ _ _ H j b Hj). destruct fss; cbn in IH |- *; [destruct j | ]; exact IH.
  Qed.

  Lemma apps_guarded : forall args h ms, self_headed ms h = false -> Guarded ms h ->
    (forall a, In a args -> Guarded ms a) -> Guarded ms (apps h args).
  Proof.
    induction args as [|a args IH]; intros h ms Hs Hh Ha; [exact Hh | ].
    cbn [apps fold_left]. apply IH.
    - exact Hs.
    - apply G_App; [exact Hs | exact Hh | apply Ha; left; reflexivity].
    - intros a' Hin. apply Ha. right. exact Hin.
  Qed.

  Definition spine_ok (ms : list mark) (t : term) : Prop :=
    (forall a, In a (spine_args t) -> Guarded ms a) /\
    match spine_head t with Var _ => True | h => Guarded ms h end.

  Definition gfalse (ms : list mark) (u : term) : result guard_error unit := guard ms u false.

  Ltac runs :=
    repeat match goal with
    | H : bind _ _ = Ok _ |- _ => let x := fresh "x" in let Hx := fresh "Hx" in bind_in H x Hx
    | x : unit |- _ => destruct x
    end.

  Lemma guard_flag : forall ms t, (forall f a, t <> App f a) -> (forall i, t <> Var i) ->
    guard ms t true = guard ms t false.
  Proof.
    intros ms t H1 H2. destruct t; try reflexivity.
    - destruct (H2 n eq_refl).
    - destruct (H1 _ _ eq_refl).
  Qed.

  Lemma peel_not_lam : forall g ms fds t, (forall b, t <> Lam b) ->
    peel ms fds t = (ms, t) /\ peel_with g ms fds t = g ms t.
  Proof.
    intros g ms fds t H.
    destruct t; try destruct (H t eq_refl); destruct fds; split; reflexivity.
  Qed.

  Lemma peel_with_nil : forall g ms b, peel_with g ms [] b = g ms b.
  Proof. intros g ms b. destruct b; reflexivity. Qed.

  Lemma from_peel : forall u,
    (forall ms fds, peel_with gfalse ms fds u = Ok tt -> Guarded (fst (peel ms fds u)) (snd (peel ms fds u))) ->
    forall ms, guard ms u false = Ok tt -> Guarded ms u.
  Proof. intros u IH ms H. apply (IH ms []). rewrite peel_with_nil. exact H. Qed.

  Lemma is_self_true : forall m, is_self m = true -> m = Self.
  Proof. intros [] H; try discriminate H; reflexivity. Qed.

  Lemma guard_sound_gen : forall t,
    (forall ms fds, peel_with gfalse ms fds t = Ok tt ->
       Guarded (fst (peel ms fds t)) (snd (peel ms fds t))) /\
    (forall ms, guard ms t true = Ok tt -> spine_ok ms t).
  Proof.
    induction t using term_ind'.
    (* variables *)
    2: { split.
         - intros ms fds H. destruct (peel_not_lam gfalse ms fds (Var n) ltac:(discriminate)) as [-> E].
           rewrite E in H. unfold gfalse in H. cbn in H |- *.
           destruct (is_self (mark_at ms n)) eqn:Es; [discriminate H | constructor; exact Es].
         - intros ms _. split; [intros a [] | exact I]. }
    (* λ *)
    3: { split.
         - intros ms [|fd fds] H; cbn in H |- *.
           + apply G_Lam. exact (from_peel _ (proj1 IHt) _ H).
           + exact (proj1 IHt _ _ H).
         - intros ms H. cbn in H. split; [intros a [] | ]. apply G_Lam. exact (from_peel _ (proj1 IHt) _ H). }
    (* application *)
    3: { assert (Hf : forall ms, guard ms t1 true = Ok tt -> guard ms t2 false = Ok tt ->
                    spine_ok ms (App t1 t2)).
         { intros ms H1 H2. destruct (proj2 IHt1 _ H1) as [Ha Hh]. split.
           - rewrite spine_args_App. intros a Hin. apply in_app_or in Hin as [Hin | [<- | []]];
               [exact (Ha _ Hin) | exact (from_peel _ (proj1 IHt2) _ H2)].
           - exact Hh. }
         split.
         - intros ms fds H. destruct (peel_not_lam gfalse ms fds (App t1 t2) ltac:(discriminate)) as [-> E].
           rewrite E in H. unfold gfalse in H. cbn [Guard.guard] in H. runs. cbn [fst snd].
           destruct (Hf _ Hx0 H) as [Ha Hh].
           destruct (self_headed ms (App t1 t2)) eqn:Es.
           + unfold Guard.call_ok in Hx. rewrite Es in Hx.
             destruct (Nat.ltb k _) eqn:El; [ | discriminate Hx].
             destruct (sub_arg ms _) eqn:Esub; [ | discriminate Hx].
             unfold self_headed in Es. destruct (spine_head (App t1 t2)) eqn:Eh; try discriminate Es.
             rewrite <- (apps_spine (App t1 t2)), Eh.
             apply G_Call; [exact (is_self_true _ Es) | apply Nat.ltb_lt, El | exact Esub | exact Ha].
           + apply G_App; [exact Es | | exact (from_peel _ (proj1 IHt2) _ H)].
             destruct (proj2 IHt1 _ Hx0) as [Ha1 Hh1].
             rewrite <- (apps_spine t1). apply apps_guarded; [ | | exact Ha1].
             * unfold self_headed in *. rewrite spine_head_idem. exact Es.
             * unfold self_headed in Es. cbn [spine_head] in Es.
               destruct (spine_head t1); try exact Hh1. constructor. exact Es.
         - intros ms H. cbn [Guard.guard] in H. runs. exact (Hf _ Hx0 H). }
    (* the other formers: no λ, no spine *)
    all: lazymatch goal with
         | |- (forall ms fds, peel_with gfalse ms fds ?t = Ok tt -> _) /\ _ =>
             enough (Hp : forall ms, guard ms t false = Ok tt -> Guarded ms t)
               by (split;
                   [ intros ms fds H;
                     destruct (peel_not_lam gfalse ms fds t ltac:(intros ? ?; discriminate)) as [-> E];
                     rewrite E in H; exact (Hp _ H)
                   | intros ms H; rewrite guard_flag in H by (intros; discriminate);
                     split; [cbn; intros ? [] | cbn; exact (Hp _ H)] ]);
             intros ms H; cbn [Guard.guard] in H; runs
         end.
    all: repeat match goal with
         | IH : (forall ms fds, peel_with gfalse ms fds ?u = Ok tt -> _) /\ _,
           Hg : guard ?m ?u false = Ok tt |- _ => apply (from_peel _ (proj1 IH)) in Hg
         end.
    all: try solve [constructor; assumption | apply G_Atom; reflexivity].
    (* match: each branch after the leading λ that bind its fields *)
    apply G_Case; [assumption | assumption | ].
    intros j b Hj. rewrite Forall_forall in IHl.
    apply (proj1 (IHl b (nth_error_In _ _ Hj))).
    exact (each_branch_ok _ _ _ _ _ H _ _ Hj).
  Qed.

  Theorem guard_sound : forall ms t, guard ms t false = Ok tt -> Guarded ms t.
  Proof. intros ms t. exact (from_peel t (proj1 (guard_sound_gen t)) ms). Qed.

  Lemma repeat_snoc : forall (A : Type) (x : A) n l, repeat x n ++ x :: l = x :: repeat x n ++ l.
  Proof. intros A x n. induction n as [|n IH]; intros l; [reflexivity | cbn; now rewrite IH]. Qed.

  Lemma guard_entry_sound : forall n ms b, guard_entry n ms b = Ok tt ->
    exists body, b = lams (S n) body /\ Guarded (Arg :: repeat Large n ++ ms) body.
  Proof.
    induction n as [|n IH]; intros ms b H; destruct b; cbn in H; try discriminate H.
    - exists b. split; [reflexivity | exact (guard_sound _ _ H)].
    - destruct (IH _ _ H) as (body & -> & Hg). exists body. split; [reflexivity | ].
      rewrite repeat_snoc in Hg. exact Hg.
  Qed.

  Theorem guard_fix_sound : forall b, guard_fix b = Ok tt -> fix_guarded b.
  Proof. intros b H. exact (guard_entry_sound k [Self] b H). Qed.
End Sound.

(** ** The marks against the strict subterm relation *)

Lemma peel_lams : forall fds ms body,
  peel ms fds (lams (length fds) body) = (rev (map field_mark fds) ++ ms, body).
Proof.
  induction fds as [|fd fds IH]; intros ms body; [reflexivity | ].
  cbn [length lams peel]. rewrite IH. cbn [map rev]. now rewrite <- app_assoc.
Qed.

Lemma apps_not_case : forall args h D s P x bs, ((exists i, h = Var i) \/ exists f a, h = App f a) ->
  apps h args <> Case D s P x bs.
Proof.
  induction args as [|a args IH]; intros h D s P x bs Hh; cbn [apps fold_left].
  - destruct Hh as [(i & ->) | (f & a & ->)]; discriminate.
  - apply IH. right. eauto.
Qed.

Section Marks.
  Variable sg : signature.

  (** [u] is an immediate subterm of [v]: [v] reduces to a constructor
      spine, and [u] is one of its recursive fields applied to arguments
      for all the positions of its telescope.  This is the order of the
      constructors of a description, defined without marks. *)
  Inductive immediate : term -> term -> Prop :=
  | Imm : forall v w D d i cd xs j Bs vs a ys,
      red sg v w -> sig_ind sg D = Some d -> ctor_view D d w = Some (i, cd, xs) ->
      nth_error (ctor_fields cd) j = Some (FRec Bs vs) -> nth_error xs j = Some a ->
      length ys = length Bs ->
      immediate (apps a ys) v.

  Definition strict_sub : term -> term -> Prop := clos_trans term immediate.

  (** A substitution of the variables respects the marks for the value
      [v] of the structural argument. *)
  Definition respects (ms : list mark) (σ : nat -> term) (v : term) : Prop :=
    forall i, (mark_at ms i = Arg -> σ i = v) /\
              (forall m, mark_at ms i = Sub m -> forall ys, length ys = m -> strict_sub (apps (σ i) ys) v).

  (** The fields of a constructor bound by the λ of a branch, innermost
      first, in front of [σ]. *)
  Definition with_fields (xs : list term) (σ : nat -> term) : nat -> term :=
    fun n => if Nat.ltb n (length xs) then nth n (rev xs) (Var 0) else σ (n - length xs).

  Lemma entry_marks_rest : forall k i, mark_at (repeat Large k ++ [Self]) i = Large \/
                                       mark_at (repeat Large k ++ [Self]) i = Self.
  Proof.
    intros k i. unfold mark_at. destruct (Nat.lt_ge_cases i k) as [Hi | Hi].
    - left. rewrite app_nth1 by (rewrite repeat_length; exact Hi). apply nth_repeat.
    - rewrite app_nth2 by (rewrite repeat_length; exact Hi). rewrite repeat_length.
      destruct (i - k) as [|[|n]]; cbn; auto.
  Qed.

  Theorem respects_entry : forall k σ v, σ 0 = v -> respects (entry_marks k) σ v.
  Proof.
    intros k σ v H [|i]; split; cbn.
    - intros _. exact H.
    - intros m E. discriminate E.
    - intros E. destruct (entry_marks_rest k i) as [E' | E']; unfold mark_at in E'; congruence.
    - intros m E. destruct (entry_marks_rest k i) as [E' | E']; unfold mark_at in E'; congruence.
  Qed.

  Theorem respects_binder : forall ms σ v u, respects ms σ v -> respects (Large :: ms) (scons u σ) v.
  Proof.
    intros ms σ v u H [|i]; [split; [discriminate | intros m E; discriminate E] | ].
    exact (H i).
  Qed.

  Theorem call_decreases : forall ms σ v a, respects ms σ v -> sub_arg ms a = true ->
    strict_sub (subst σ a) v.
  Proof.
    intros ms σ v a H Ha. unfold sub_arg in Ha.
    destruct (spine_head a) eqn:Eh; try discriminate Ha.
    destruct (mark_at ms n) eqn:Em; try discriminate Ha. apply Nat.eqb_eq in Ha.
    rewrite <- (apps_spine a), Eh, subst_apps. cbn [subst].
    apply (proj2 (H n) n0 Em). rewrite length_map. exact Ha.
  Qed.

  Lemma origin_below : forall ms σ v x, respects ms σ v -> origin ms x = true ->
    subst σ x = v \/ strict_sub (subst σ x) v.
  Proof.
    intros ms σ v x H Ho. unfold origin in Ho. apply orb_true_iff in Ho as [Ho | Ho].
    - left. destruct x; try discriminate Ho. cbn in Ho |- *.
      destruct (mark_at ms n) eqn:Em; try discriminate Ho. exact (proj1 (H n) Em).
    - right. exact (call_decreases _ _ _ _ H Ho).
  Qed.

  Theorem respects_fields : forall ms σ v x w D d i cd xs,
    respects ms σ v -> origin ms x = true -> red sg (subst σ x) w ->
    sig_ind sg D = Some d -> ctor_view D d w = Some (i, cd, xs) ->
    respects (rev (map field_mark (ctor_fields cd)) ++ ms) (with_fields xs σ) v.
  Proof.
    intros ms σ v x w D d i cd xs H Ho Hr Hd Hc n.
    destruct (ctor_view_spec _ _ _ _ _ _ Hc) as (c & ps & _ & _ & _ & Hl).
    unfold mark_at, with_fields.
    destruct (Nat.ltb n (length xs)) eqn:En.
    - apply Nat.ltb_lt in En.
      rewrite app_nth1 by (rewrite length_rev, length_map; lia).
      rewrite rev_nth by (rewrite length_map; lia). rewrite length_map.
      rewrite rev_nth by exact En.
      set (j := length (ctor_fields cd) - S n).
      replace (length xs - S n) with j by (unfold j; lia).
      assert (Hj : j < length (ctor_fields cd)) by (unfold j; lia).
      change Large with (field_mark (FArg (Var 0))). rewrite map_nth.
      destruct (nth j (ctor_fields cd) (FArg (Var 0))) as [A | Bs vs] eqn:Ef; cbn [field_mark].
      + split; [discriminate | intros m E; discriminate E].
      + split; [discriminate | ]. intros m E ys Hys. injection E as <-.
        assert (Ia : immediate (apps (nth j xs (Var 0)) ys) (subst σ x)).
        { eapply Imm; [exact Hr | exact Hd | exact Hc | | | exact Hys].
          - rewrite <- Ef. apply nth_error_nth'. exact Hj.
          - apply nth_error_nth'. lia. }
        destruct (origin_below _ _ _ _ H Ho) as [E' | E'].
        * rewrite <- E'. apply t_step, Ia.
        * eapply t_trans; [apply t_step, Ia | exact E'].
    - apply Nat.ltb_ge in En.
      rewrite app_nth2 by (rewrite length_rev, length_map; lia).
      rewrite length_rev, length_map, <- Hl. exact (H (n - length xs)).
  Qed.

  Lemma guarded_case_inv : forall k ms D s P x bs, Guarded sg k ms (Case D s P x bs) ->
    forall j b, nth_error bs j = Some b ->
    Guarded sg k (fst (peel ms (nth j (branch_fields sg ms D x) []) b))
                 (snd (peel ms (nth j (branch_fields sg ms D x) []) b)).
  Proof.
    intros k ms D s P x bs H. inversion H; subst.
    - exfalso. eapply apps_not_case; [ | eassumption]. left. eauto.
    - assumption.
    - discriminate.
  Qed.

  (** A guarded match on a structural origin, once its scrutinee reduces
      to a constructor: the branch of the constructor binds its fields,
      its body is guarded, and the fields respect their marks. *)
  Theorem case_step : forall k ms σ v D s P x bs w d i cd xs b body,
    Guarded sg k ms (Case D s P x bs) -> respects ms σ v -> origin ms x = true ->
    red sg (subst σ x) w -> sig_ind sg D = Some d -> ctor_view D d w = Some (i, cd, xs) ->
    nth_error bs i = Some b -> b = lams (length (ctor_fields cd)) body ->
    Guarded sg k (rev (map field_mark (ctor_fields cd)) ++ ms) body /\
    respects (rev (map field_mark (ctor_fields cd)) ++ ms) (with_fields xs σ) v.
  Proof.
    intros k ms σ v D s P x bs w d i cd xs b body Hg H Ho Hr Hd Hv Hb ->.
    split; [ | exact (respects_fields _ _ _ _ _ _ _ _ _ _ H Ho Hr Hd Hv)].
    destruct (ctor_view_spec _ _ _ _ _ _ Hv) as (c & ps & _ & Hc & _ & _).
    pose proof (guarded_case_inv _ _ _ _ _ _ _ Hg _ _ Hb) as G.
    assert (E : nth i (branch_fields sg ms D x) [] = ctor_fields cd).
    { unfold branch_fields. rewrite Ho, Hd.
      apply nth_error_nth. rewrite nth_error_map, (find_ctor_nth_error _ _ _ _ Hc). reflexivity. }
    rewrite E, peel_lams in G. exact G.
  Qed.
End Marks.
