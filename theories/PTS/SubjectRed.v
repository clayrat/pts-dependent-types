(** * Subject reduction for the declarative rules

    In a type-correct signature ([signature_typed]), a reduct of a term
    has the types of the term: one step of [red1] ([subject_red1]), and
    so any number of steps ([subject_red]).  Every redex of the kernel
    is covered, in every position, under binders included:
    - β: the λ is typed at a Π convertible to the Π of the function,
      whose components are convertible by injectivity (PTS.Confluence);
      the body is typed by the substitution lemma (PTS.TypingSubst);
    - the annotations, the ι of the primitives and the projections: the
      component of the redex, at a convertible type;
    - δ: the body has the type of its constant in the empty context,
      and both are closed;
    - ι of an eliminator instance: the third condition of
      [signature_typed];
    - the unfolding of a [fix]: [b[fix/0]] has every type of the [fix],
      and so does the spine it heads;
    - ι of a match: the scrutinee is a constructor spine, typed against
      the type of the constructor, whose indices then match those of
      the scrutinee by injectivity of the spines of a family
      ([conv_ind_spine] of PTS.Confluence); the fields are typed against
      the telescope of the branch up to a conversion of its parameters,
      and the branch applied to them has a type convertible to the type
      of the match;
    - a step inside a part: the rule of the former again, at the old
      type up to conversion.  A step in the domain of a binder changes
      the context of the body (context conversion, PTS.Inversion), a
      step in the body of a [fix] keeps its guard (PTS.GuardRed) and a
      step in its type its structural argument ([struct_arg_red] of
      PTS.Confluence).

    Where the type of the former changes, the old type is a type by
    validity (PTS.Inversion).  A step in the motive of a match changes
    the types of the branches; the new ones are types because the motive
    is replaced by its reduct inside the old ones, and the reduct has
    all the types of the motive.  For that the statement is proved for
    every renaming of the term ([subject_red1_ren]): the motive sits
    lifted under the fields in the type of a branch. *)

From Stdlib Require Import List Arith Lia Relations.
From Stdlib Require String.
Import ListNotations.
From DepTypes.Common Require Import Lists.
From DepTypes.PTS Require Import Syntax Telescope Spec Signature Reduction SubstLaws Confluence
  Guard Typing TypingSubst GuardRed Inversion.
(* TODO(elim-inductive-types, erasure-cic): remove these exports once
   theories/Checked/IotaTyped.v of elim-inductive-types and
   theories/Erasure/{Simulation,EraseSound}.v of erasure-cic import
   Common.Lists and PTS.Confluence.  The facts about [Forall2] and the
   conversion of substituted telescopes ([conv_subst_tsub],
   [conv_subst_tele_tsub]) were proved here; they are re-exported for the
   files that use them from this module. *)
From DepTypes.Common Require Export Lists.
From DepTypes.PTS Require Export Confluence.

Section SubjectRed.
  Variable S : spec.
  Variable sg : signature.
  Hypothesis Hsig : signature_typed S sg.
  Local Notation typed := (has_type S sg).
  Local Notation "t ≡ u" := (conv sg t u).

  (** ** Rebuilding a judgment *)

  Lemma typed_conv_ctype : forall G t X Y T s, typed G t X -> X ≡ Y -> typed G Y (Srt s) ->
    ctype S sg G Y T -> typed G t T.
  Proof. intros G t X Y T s H Hc HY HT. eapply ctype_typed; [eapply T_Conv; eassumption | exact HT]. Qed.

  Lemma pi_cod_typed : forall G f A B u, typed G f (Pi A B) -> typed G u A ->
    exists s, typed G (subst1 B u) (Srt s).
  Proof.
    intros G f A B u Hf Hu.
    destruct (validity_type S sg Hsig _ _ _ Hf (fun s E => ltac:(discriminate E))) as [s HP].
    destruct (inv_pi S sg _ _ _ _ HP) as (s1 & s2 & s3 & _ & HB & _ & _).
    exists s2. exact (typing_subst1 S sg _ _ _ _ _ Hu HB).
  Qed.

  Lemma sigma_dom_typed : forall G p A B, typed G p (Sigma A B) -> exists s, typed G A (Srt s).
  Proof.
    intros G p A B Hp.
    destruct (validity_type S sg Hsig _ _ _ Hp (fun s E => ltac:(discriminate E))) as [s HS].
    destruct (inv_sigma S sg _ _ _ _ HS) as (s1 & _ & _ & HA & _ & _ & _). exists s1. exact HA.
  Qed.

  Lemma sigma_cod_typed : forall G p A B u, typed G p (Sigma A B) -> typed G u A ->
    exists s, typed G (subst1 B u) (Srt s).
  Proof.
    intros G p A B u Hp Hu.
    destruct (validity_type S sg Hsig _ _ _ Hp (fun s E => ltac:(discriminate E))) as [s HS].
    destruct (inv_sigma S sg _ _ _ _ HS) as (s1 & s2 & _ & _ & HB & _ & _).
    exists s2. exact (typing_subst1 S sg _ _ _ _ _ Hu HB).
  Qed.

  (** A head replaced by one with all its types. *)
  Lemma apps_replace : forall args G h h' T, typed G (apps h args) T ->
    (forall H, typed G h H -> typed G h' H) -> typed G (apps h' args) T.
  Proof.
    induction args as [|a args IH] using rev_ind; intros G h h' T Ht Hh; [exact (Hh T Ht) | ].
    rewrite apps_snoc in Ht |- *. destruct (inv_app S sg _ _ _ _ Ht) as (A & B & Hf & Ha & HT).
    exact (ctype_typed S sg _ _ _ _ (T_App _ _ _ _ _ _ _ (IH _ _ _ _ Hf Hh) Ha) HT).
  Qed.

  Lemma app_replace : forall G C C' a T, typed G (App C a) T ->
    (forall H, typed G C H -> typed G C' H) -> typed G (App C' a) T.
  Proof. intros G C C' a T H HC. exact (apps_replace [a] G C C' T H HC). Qed.

  (** The codomain of a telescope replaced by one with its sorts. *)
  Lemma pis_replace : forall Ts G R R' s, typed G (pis Ts R) (Srt s) ->
    (forall G' s', typed G' R (Srt s') -> typed G' R' (Srt s')) -> typed G (pis Ts R') (Srt s).
  Proof.
    induction Ts as [|T Ts IH]; intros G R R' s H HR; cbn [pis] in *; [exact (HR _ _ H) | ].
    destruct (inv_pi S sg _ _ _ _ H) as (s1 & s2 & s3 & HT & HB & Hr & Hc).
    exact (ctype_typed S sg _ _ _ _ (T_Pi _ _ _ _ _ _ _ _ HT (IH _ _ _ _ HB HR) Hr) Hc).
  Qed.

  (** ** The branches of a match *)

  Lemma branches_cons_inv : forall G d ps P cs b bs, has_branches S sg G d ps P cs (b :: bs) ->
    exists c cs', cs = c :: cs' /\ typed G b (case_branch_type d ps P c) /\
      has_branches S sg G d ps P cs' bs.
  Proof. intros G d ps P cs b bs H. inversion H; subst. eexists _, _. split; [reflexivity | split; assumption]. Qed.

  Lemma branches_replace : forall bs1 G d ps P cs b b' bs2,
    has_branches S sg G d ps P cs (bs1 ++ b :: bs2) -> (forall T, typed G b T -> typed G b' T) ->
    has_branches S sg G d ps P cs (bs1 ++ b' :: bs2).
  Proof.
    induction bs1 as [|b1 bs1 IH]; intros G d ps P cs b b' bs2 H Hb; cbn [app] in *;
      destruct (branches_cons_inv _ _ _ _ _ _ _ H) as (c & cs' & -> & Hb1 & Hbs); constructor.
    - exact (Hb _ Hb1).
    - exact Hbs.
    - exact Hb1.
    - exact (IH _ _ _ _ _ _ _ _ Hbs Hb).
  Qed.

  (** A step of the motive: the types of the branches are replaced by
      their reducts, which are types since the reduct of the motive has
      all its types, under the fields too. *)
  Lemma branches_motive : forall G d ps P P' cs bs, has_branches S sg G d ps P cs bs ->
    red1 sg P P' -> (forall n G' H, typed G' (lift n P) H -> typed G' (lift n P') H) ->
    has_branches S sg G d ps P' cs bs.
  Proof.
    intros G d ps P P' cs bs H Hr HP. revert cs H. induction bs as [|b bs IH]; intros cs H.
    - inversion H; subst. constructor.
    - destruct (branches_cons_inv _ _ _ _ _ _ _ H) as (c & cs' & -> & Hb & Hbs).
      constructor; [ | exact (IH _ Hbs)].
      destruct (case_branch_type_shape d ps c) as (Ts & n & l & a & E).
      rewrite E in Hb |- *.
      destruct (validity_type S sg Hsig _ _ _ Hb (pis_apps_not_srt _ _ _ _)) as [s0 HBT].
      eapply T_Conv; [exact Hb | | ].
      + apply (pis_replace _ _ _ _ _ HBT). intros G' s' HR. apply (apps_replace _ _ _ _ _ HR). apply HP.
      + apply red_conv, rt_step, red1_pis_cod, red1_apps_head, red1_rename, Hr.
  Qed.

  (** ** Contractions *)

  Lemma sr_beta : forall G b u T, typed G (App (Lam b) u) T -> typed G (subst1 b u) T.
  Proof.
    intros G b u T H. destruct (inv_app S sg _ _ _ _ H) as (A & B & Hf & Hu & HT).
    destruct (inv_lam S sg _ _ _ Hf) as (A' & B' & s & Hb & HP & HPT).
    apply ctype_conv_of, pi_inj in HPT as [HA HB].
    destruct (inv_pi S sg _ _ _ _ HP) as (s1 & _ & _ & HA' & _ & _ & _).
    pose proof (T_Conv _ _ _ _ _ _ _ Hu HA' (conv_sym _ _ HA)) as Hu'.
    pose proof (typing_subst1 S sg _ _ _ _ _ Hu' Hb) as H1.
    destruct (pi_cod_typed _ _ _ _ _ Hf Hu) as [s2 HB2].
    exact (typed_conv_ctype _ _ _ _ _ _ H1 (conv_subst (scons u Var) _ _ HB) HB2 HT).
  Qed.

  Lemma sr_delta : forall G g b T, sig_delta sg g = Some b -> typed G (Const g) T -> typed G b T.
  Proof.
    intros G g b T Hd H. destruct (inv_const S sg _ _ _ H) as (A & HG & _ & Hg & HT).
    pose proof Hsig as [_ [Hb _]].
    exact (ctype_typed S sg _ _ _ _ (typed_closed_weaken S sg _ _ _ (Hb _ _ _ Hg Hd)
             (sig_delta_closed _ _ _ Hd) (sig_type_closed _ _ _ Hg) HG) HT).
  Qed.

  (** [b[fix/0]] has every type of the [fix]. *)
  Lemma sr_fix_body : forall G A k b H, typed G (Fix A k b) H -> typed G (subst1 b (Fix A k b)) H.
  Proof.
    intros G A k b H HF. destruct (inv_fix S sg _ _ _ _ _ HF) as (s & D & HA & Hsa & Hne & Hb & Hg & HT).
    pose proof (T_Fix _ _ _ _ _ _ _ _ HA Hsa Hne Hb Hg) as HF'.
    pose proof (typing_subst1 S sg _ _ _ _ _ HF' Hb) as H1. rewrite subst1_lift in H1.
    exact (ctype_typed S sg _ _ _ _ H1 HT).
  Qed.

  Lemma sr_fix_unfold : forall G t u T, fix_unfold t = Some u -> typed G t T -> typed G u T.
  Proof.
    intros G t u T Hu H. unfold fix_unfold in Hu.
    destruct (fix_view t) as [[[A k] b]|] eqn:Ev; [ | discriminate Hu].
    destruct (fix_view_spec _ _ _ _ Ev) as [Eh _].
    unfold fix_at in Hu.
    repeat match type of Hu with
           | (match ?x with _ => _ end) = Some _ => destruct x; try discriminate Hu
           end.
    injection Hu as <-. rewrite <- (apps_spine t), Eh in H.
    exact (apps_replace _ _ _ _ _ H (sr_fix_body G A k b)).
  Qed.

  Lemma sr_spine : forall G t u T, spine_iota sg t = Some u -> typed G t T -> typed G u T.
  Proof.
    intros G t u T Hu H. unfold spine_iota in Hu. destruct (iota sg t) as [u'|] eqn:Ei.
    - injection Hu as <-. pose proof Hsig as [_ [_ Hi]]. exact (Hi _ _ _ _ Ei H).
    - exact (sr_fix_unfold _ _ _ _ Hu H).
  Qed.

  (** Arguments typed against a telescope are typed against a convertible
      one that is well formed. *)
  Lemma args_typed_conv : forall G Ts args, args_typed S sg G Ts args ->
    forall Ts' R s, Forall2 (conv sg) Ts Ts' -> typed G (pis Ts' R) (Srt s) -> args_typed S sg G Ts' args.
  Proof.
    intros G Ts args H. induction H as [|T Ts a args Ha _ IH]; intros Ts' R s Hc HP.
    - inversion Hc; subst. constructor.
    - destruct (forall2_cons_inv _ _ _ _ Hc) as (T' & Ts'' & -> & HT & HTs).
      cbn [pis] in HP. destruct (inv_pi S sg _ _ _ _ HP) as (s1 & s2 & s3 & HT' & HB & _ & _).
      pose proof (T_Conv _ _ _ _ _ _ _ Ha HT' HT) as Ha'.
      constructor; [exact Ha' | ].
      pose proof (typing_subst1 S sg _ _ _ _ _ Ha' HB) as H1. change (subst1 (Srt s2) a) with (Srt s2) in H1.
      unfold subst1 in H1. rewrite subst_pis in H1.
      exact (IH _ _ _ (forall2_conv_subst_tele _ _ _ HTs (scons a Var)) H1).
  Qed.

  (** ι of a match. *)
  Lemma sr_case_iota : forall G t u T, case_iota sg t = Some u -> typed G t T -> typed G u T.
  Proof.
    intros G t u T Hu H. destruct (case_iota_case _ _ _ Hu) as (D & s & P & x & bs & ->).
    cbn [case_iota] in Hu.
    destruct (sig_ind sg D) as [d0|] eqn:Ed; [ | discriminate Hu].
    destruct (ctor_view D d0 x) as [[[i cd] xs]|] eqn:Ev; [ | discriminate Hu].
    destruct (nth_error bs i) as [b|] eqn:Eb; [ | discriminate Hu]. cbn [option_map] in Hu. injection Hu as <-.
    destruct (inv_case S sg _ _ _ _ _ _ _ H) as (d & ps & us & Hdec & Hd & Hel & Hlp & Hlu & Hx & HP & Hbs & HT).
    rewrite Ed in Hd. injection Hd as Hdd. subst d0.
    destruct (ctor_view_spec _ _ _ _ _ _ Ev) as (c & ps' & Ex & Hc & Hlp' & Hlx). subst x.
    pose proof (typed_wf S sg _ _ _ Hx) as HG.
    destruct (sig_ind_closed _ _ _ Ed) as [_ Hcs].
    pose proof (find_ctor_closed _ _ _ _ _ Hcs Hc) as Hcc. unfold ctor_closed in Hcc.
    apply Bool.andb_true_iff in Hcc as [Hfc Hic].
    pose proof (sig_ind_name _ _ _ Ed) as Hname. pose proof (find_ctor_name _ _ _ _ Hc) as Hcname.
    set (FT := field_types (ind_name d) (length (ind_params d)) 0 (ctor_fields cd)) in *.
    (* the scrutinee, typed against the type of its constructor *)
    assert (Hty : sig_type sg (Ctor D c) = Some (ctor_type d cd)) by (cbn [sig_type]; rewrite Ed, Hc; reflexivity).
    destruct (const_type_typed S sg Hsig G _ _ HG Hty) as [s0 Hs0].
    unfold ctor_type in Hs0. cbv zeta in Hs0. fold FT in Hs0.
    assert (Hl : length (ind_params d ++ FT) = length (ps' ++ xs))
      by (unfold FT; rewrite !length_app, field_types_length; lia).
    destruct (apps_inv S sg (ps' ++ xs) G (Const (Ctor D c)) _ _ _ _ Hl Hx (const_head S sg _ _ _ Hty) Hs0)
      as [Hargs Hcv].
    rewrite subst_apps, map_app in Hcv. cbn [subst] in Hcv.
    rewrite <- Hlx, <- Hlp', map_tsub_vars, Hname in Hcv.
    apply conv_ind_spine in Hcv.
    apply forall2_app_split in Hcv as [Hps Hus]; [ | lia].
    destruct (proj1 (args_typed_app S sg ps' G _ _ xs (eq_sym Hlp')) Hargs) as [_ Hxs].
    (* the branch *)
    pose proof (branches_nth S sg _ _ _ _ _ _ Hbs i cd b (find_ctor_nth_error _ _ _ _ Hc) Eb) as Hb.
    assert (Hbt : case_branch_type d ps P cd =
      pis (subst_tele (tsub ps) FT)
          (apps (lift (length xs) P)
             (map (subst (upn (length xs) (tsub ps))) (ctor_indices cd) ++
              [apps (Const (Ctor D c)) (map (lift (length xs)) ps ++ vars 0 (length xs))]))).
    { unfold case_branch_type. cbv zeta. fold FT. rewrite Hname, Hcname, Hlx.
      rewrite (inst_tele_tsub FT ps 0).
      2: { unfold FT. rewrite Nat.add_0_l, Hlp.
           pose proof (field_types_closed (ind_name d) _ _ 0 ltac:(rewrite Nat.add_0_r; exact Hfc)) as Hft.
           rewrite Nat.add_0_r in Hft. exact Hft. }
      f_equal. f_equal. f_equal. apply map_ext_in. intros t Ht. apply inst_env_tsub.
      rewrite Hlp, Nat.add_comm. exact (proj1 (List.forallb_forall _ _) Hic t Ht). }
    rewrite Hbt in Hb.
    destruct (validity_type S sg Hsig _ _ _ Hb (pis_apps_not_srt _ _ _ _)) as [sb HBT].
    assert (Hxs' : args_typed S sg G (subst_tele (tsub ps) FT) xs).
    { apply (args_typed_conv _ _ _ Hxs _ _ _ (conv_subst_tele_tsub sg _ _ Hps FT 0) HBT). }
    pose proof (typed_apps S sg _ _ _ _ _ Hxs' Hb) as H1.
    rewrite subst_apps, subst_tsub_lift, map_app, map_map in H1. cbn [map] in H1.
    rewrite subst_apps, map_app, map_tsub_lift, map_tsub_vars0 in H1. cbn [subst] in H1.
    rewrite (map_ext _ _ (fun t => subst_subst t (tsub xs) (upn (length xs) (tsub ps)))) in H1.
    rewrite (map_ext _ (subst (tsub (ps ++ xs)))) in H1
      by (intros t; apply subst_ext; apply tsub_app).
    (* its type and the type of the match *)
    destruct (validity_type S sg Hsig _ _ _ Hx (fun s1 => apps_const_not_srt _ _ s1)) as [sx HX].
    pose proof (case_type_typed S sg Hsig _ _ _ _ _ _ _ _ _ Ed Hlp Hlu Hx HP HX) as HPT.
    eapply (typed_conv_ctype _ _ _ _ _ _ H1); [ | exact HPT | exact HT].
    assert (Hpx : Forall2 (conv sg) (ps ++ xs) (ps' ++ xs))
      by (apply Forall2_app; [apply forall2_conv_sym, Hps | apply forall2_conv_refl]).
    apply conv_apps; [apply conv_refl | ]. apply Forall2_app.
    - eapply forall2_conv_trans; [ | exact Hus].
      clear -Hpx. induction (ctor_indices cd) as [|t idx IH]; cbn [map]; constructor; [ | exact IH].
      exact (conv_subst_tsub sg _ _ Hpx 0 t).
    - constructor; [ | constructor]. apply conv_apps; [apply conv_refl | exact Hpx].
  Qed.

  (** ** Subject reduction *)

  Theorem subject_red1_ren : forall t t', red1 sg t t' ->
    forall r G T, typed G (rename r t) T -> typed G (rename r t') T.
  Proof.
    induction 1 as
      [ b u | t A | C c | C t f | C t f | a b | a b
      | A A' B HA IH | A B B' HB IH | b b' Hb IH | f f' a Hf IH | f a a' Ha IH
      | t t' A Ht IH | t A A' HA IH | C C' e HC IH | C e e' He IH
      | C C' c u HC IH | C c c' u Hc IH | C c u u' Hu IH
      | C C' t f b HC IH | C t t' f b Ht IH | C t f f' b Hf IH | C t f b b' Hb IH
      | A A' B HA IH | A B B' HB IH | a a' b Ha IH | a b b' Hb IH | p p' Hp IH | p p' Hp IH
      | D s P P' x bs HP IH | D s P x x' bs Hx IH | D s P x bs1 b b' bs2 Hb IH
      | A A' k b HA IH | A k b b' Hb IH
      | g b Hd | t u Hsp | t u Hca ];
      intros r G T H; cbn [rename] in H |- *.
    (* β, annotations, the primitives, the projections *)
    - rewrite rename_subst1. exact (sr_beta _ _ _ _ H).
    - destruct (inv_ann S sg _ _ _ _ H) as (s & _ & Ht & HT). exact (ctype_typed S sg _ _ _ _ Ht HT).
    - destruct (inv_elim_unit S sg _ _ _ _ _ H) as (s & _ & Hc & _ & HT). exact (ctype_typed S sg _ _ _ _ Hc HT).
    - destruct (inv_elim_bool S sg _ _ _ _ _ _ H) as (s & _ & Ht & _ & _ & HT). exact (ctype_typed S sg _ _ _ _ Ht HT).
    - destruct (inv_elim_bool S sg _ _ _ _ _ _ H) as (s & _ & _ & Hf & _ & HT). exact (ctype_typed S sg _ _ _ _ Hf HT).
    - destruct (inv_fst S sg _ _ _ H) as (A & B & Hp & HT).
      destruct (inv_pair S sg _ _ _ _ Hp) as (A' & B' & s & _ & Ha & _ & HST).
      apply ctype_conv_of, sigma_inj in HST as [HA _].
      destruct (sigma_dom_typed _ _ _ _ Hp) as [s1 HA1].
      exact (typed_conv_ctype _ _ _ _ _ _ Ha HA HA1 HT).
    - destruct (inv_snd S sg _ _ _ H) as (A & B & Hp & HT).
      destruct (inv_pair S sg _ _ _ _ Hp) as (A' & B' & s & _ & _ & Hb & HST).
      apply ctype_conv_of, sigma_inj in HST as [_ HB].
      destruct (sigma_cod_typed _ _ _ _ _ Hp (T_Fst _ _ _ _ _ _ Hp)) as [s2 HB2].
      eapply typed_conv_ctype; [exact Hb | | exact HB2 | exact HT].
      eapply conv_trans; [apply conv_subst; exact HB | ].
      apply conv_sym, red_conv, red_subst1_arg, rt_step, R_FstPair.
    (* Π *)
    - destruct (inv_pi S sg _ _ _ _ H) as (s1 & s2 & s3 & HA1 & HB1 & Hr & HT).
      pose proof (IH r G _ HA1) as HA2.
      assert (Hc : rename r A ≡ rename r A') by (apply red_conv, rt_step, red1_rename, HA).
      exact (ctype_typed S sg _ _ _ _ (T_Pi _ _ _ _ _ _ _ _ HA2 (ctx_conv1 S sg _ _ _ _ _ _ HB1 HA2 Hc) Hr) HT).
    - destruct (inv_pi S sg _ _ _ _ H) as (s1 & s2 & s3 & HA1 & HB1 & Hr & HT).
      exact (ctype_typed S sg _ _ _ _ (T_Pi _ _ _ _ _ _ _ _ HA1 (IH _ _ _ HB1) Hr) HT).
    (* λ, application *)
    - destruct (inv_lam S sg _ _ _ H) as (A & B & s & Hb1 & HP & HT).
      exact (ctype_typed S sg _ _ _ _ (T_Lam _ _ _ _ _ _ _ (IH _ _ _ Hb1) HP) HT).
    - destruct (inv_app S sg _ _ _ _ H) as (A & B & Hf1 & Ha & HT).
      exact (ctype_typed S sg _ _ _ _ (T_App _ _ _ _ _ _ _ (IH _ _ _ Hf1) Ha) HT).
    - destruct (inv_app S sg _ _ _ _ H) as (A & B & Hf & Ha1 & HT).
      pose proof (T_App _ _ _ _ _ _ _ Hf (IH _ _ _ Ha1)) as H1.
      destruct (pi_cod_typed _ _ _ _ _ Hf Ha1) as [s HB].
      eapply typed_conv_ctype; [exact H1 | | exact HB | exact HT].
      apply conv_sym, red_conv, red_subst1_arg, rt_step, red1_rename, Ha.
    (* annotations *)
    - destruct (inv_ann S sg _ _ _ _ H) as (s & HA & Ht1 & HT).
      exact (ctype_typed S sg _ _ _ _ (T_Ann _ _ _ _ _ _ HA (IH _ _ _ Ht1)) HT).
    - destruct (inv_ann S sg _ _ _ _ H) as (s & HA1 & Ht & HT).
      pose proof (IH _ _ _ HA1) as HA2.
      assert (Hc : rename r A ≡ rename r A') by (apply red_conv, rt_step, red1_rename, HA).
      pose proof (T_Ann _ _ _ _ _ _ HA2 (T_Conv _ _ _ _ _ _ _ Ht HA2 Hc)) as H1.
      exact (typed_conv_ctype _ _ _ _ _ _ H1 (conv_sym _ _ Hc) HA1 HT).
    (* the eliminator of Void *)
    - destruct (inv_elim_void S sg _ _ _ _ H) as (s & HC1 & He & HT).
      pose proof (T_ElimVoid _ _ _ _ _ _ (IH _ _ _ HC1) He) as H1.
      eapply typed_conv_ctype; [exact H1 | | exact (T_App _ _ _ _ _ _ _ HC1 He) | exact HT].
      apply conv_sym, red_conv, rt_step, R_AppFun, red1_rename, HC.
    - destruct (inv_elim_void S sg _ _ _ _ H) as (s & HC & He1 & HT).
      pose proof (T_ElimVoid _ _ _ _ _ _ HC (IH _ _ _ He1)) as H1.
      eapply typed_conv_ctype; [exact H1 | | exact (T_App _ _ _ _ _ _ _ HC He1) | exact HT].
      apply conv_sym, red_conv, rt_step, R_AppArg, red1_rename, He.
    (* the eliminator of Unit *)
    - destruct (inv_elim_unit S sg _ _ _ _ _ H) as (s & HC1 & Hc1 & Hu & HT).
      pose proof (IH _ _ _ HC1) as HC2.
      assert (Hr1 : red1 sg (rename r C) (rename r C')) by (apply red1_rename, HC).
      destruct (validity_type S sg Hsig _ _ _ Hc1 (fun s E => ltac:(discriminate E))) as [s' Hs'].
      pose proof (T_Conv _ _ _ _ _ _ _ Hc1 (app_replace _ _ _ _ _ Hs' (IH r G)) (red_conv _ _ (rt_step _ _ _ _ (R_AppFun _ _ _ _ Hr1)))) as Hc2.
      pose proof (T_ElimUnit _ _ _ _ _ _ _ HC2 Hc2 Hu) as H1.
      eapply typed_conv_ctype; [exact H1 | | exact (T_App _ _ _ _ _ _ _ HC1 Hu) | exact HT].
      apply conv_sym, red_conv, rt_step, R_AppFun, Hr1.
    - destruct (inv_elim_unit S sg _ _ _ _ _ H) as (s & HC1 & Hc1 & Hu & HT).
      exact (ctype_typed S sg _ _ _ _ (T_ElimUnit _ _ _ _ _ _ _ HC1 (IH _ _ _ Hc1) Hu) HT).
    - destruct (inv_elim_unit S sg _ _ _ _ _ H) as (s & HC1 & Hc1 & Hu1 & HT).
      pose proof (T_ElimUnit _ _ _ _ _ _ _ HC1 Hc1 (IH _ _ _ Hu1)) as H1.
      eapply typed_conv_ctype; [exact H1 | | exact (T_App _ _ _ _ _ _ _ HC1 Hu1) | exact HT].
      apply conv_sym, red_conv, rt_step, R_AppArg, red1_rename, Hu.
    (* the eliminator of Bool *)
    - destruct (inv_elim_bool S sg _ _ _ _ _ _ H) as (s & HC1 & Ht1 & Hf1 & Hb1 & HT).
      pose proof (IH _ _ _ HC1) as HC2.
      assert (Hr1 : red1 sg (rename r C) (rename r C')) by (apply red1_rename, HC).
      destruct (validity_type S sg Hsig _ _ _ Ht1 (fun s E => ltac:(discriminate E))) as [st Hst].
      destruct (validity_type S sg Hsig _ _ _ Hf1 (fun s E => ltac:(discriminate E))) as [sf Hsf].
      pose proof (T_Conv _ _ _ _ _ _ _ Ht1 (app_replace _ _ _ _ _ Hst (IH r G)) (red_conv _ _ (rt_step _ _ _ _ (R_AppFun _ _ _ _ Hr1)))) as Ht2.
      pose proof (T_Conv _ _ _ _ _ _ _ Hf1 (app_replace _ _ _ _ _ Hsf (IH r G)) (red_conv _ _ (rt_step _ _ _ _ (R_AppFun _ _ _ _ Hr1)))) as Hf2.
      pose proof (T_ElimBool _ _ _ _ _ _ _ _ HC2 Ht2 Hf2 Hb1) as H1.
      eapply typed_conv_ctype; [exact H1 | | exact (T_App _ _ _ _ _ _ _ HC1 Hb1) | exact HT].
      apply conv_sym, red_conv, rt_step, R_AppFun, Hr1.
    - destruct (inv_elim_bool S sg _ _ _ _ _ _ H) as (s & HC1 & Ht1 & Hf1 & Hb1 & HT).
      exact (ctype_typed S sg _ _ _ _ (T_ElimBool _ _ _ _ _ _ _ _ HC1 (IH _ _ _ Ht1) Hf1 Hb1) HT).
    - destruct (inv_elim_bool S sg _ _ _ _ _ _ H) as (s & HC1 & Ht1 & Hf1 & Hb1 & HT).
      exact (ctype_typed S sg _ _ _ _ (T_ElimBool _ _ _ _ _ _ _ _ HC1 Ht1 (IH _ _ _ Hf1) Hb1) HT).
    - destruct (inv_elim_bool S sg _ _ _ _ _ _ H) as (s & HC1 & Ht1 & Hf1 & Hb1 & HT).
      pose proof (T_ElimBool _ _ _ _ _ _ _ _ HC1 Ht1 Hf1 (IH _ _ _ Hb1)) as H1.
      eapply typed_conv_ctype; [exact H1 | | exact (T_App _ _ _ _ _ _ _ HC1 Hb1) | exact HT].
      apply conv_sym, red_conv, rt_step, R_AppArg, red1_rename, Hb.
    (* Σ *)
    - destruct (inv_sigma S sg _ _ _ _ H) as (s1 & s2 & s3 & HA1 & HB1 & Hr & HT).
      pose proof (IH r G _ HA1) as HA2.
      assert (Hc : rename r A ≡ rename r A') by (apply red_conv, rt_step, red1_rename, HA).
      exact (ctype_typed S sg _ _ _ _ (T_Sigma _ _ _ _ _ _ _ _ HA2 (ctx_conv1 S sg _ _ _ _ _ _ HB1 HA2 Hc) Hr) HT).
    - destruct (inv_sigma S sg _ _ _ _ H) as (s1 & s2 & s3 & HA1 & HB1 & Hr & HT).
      exact (ctype_typed S sg _ _ _ _ (T_Sigma _ _ _ _ _ _ _ _ HA1 (IH _ _ _ HB1) Hr) HT).
    - destruct (inv_pair S sg _ _ _ _ H) as (A & B & s & HS & Ha1 & Hb1 & HT).
      pose proof (IH _ _ _ Ha1) as Ha2.
      destruct (inv_sigma S sg _ _ _ _ HS) as (s1 & s2 & _ & _ & HB & _ & _).
      pose proof (typing_subst1 S sg _ _ _ _ _ Ha2 HB) as HB2. change (subst1 (Srt s2) _) with (Srt s2) in HB2.
      pose proof (T_Conv _ _ _ _ _ _ _ Hb1 HB2 (red_conv _ _ (red_subst1_arg _ _ _ (rt_step _ _ _ _ (red1_rename _ _ _ Ha))))) as Hb2.
      exact (ctype_typed S sg _ _ _ _ (T_Pair _ _ _ _ _ _ _ _ HS Ha2 Hb2) HT).
    - destruct (inv_pair S sg _ _ _ _ H) as (A & B & s & HS & Ha1 & Hb1 & HT).
      exact (ctype_typed S sg _ _ _ _ (T_Pair _ _ _ _ _ _ _ _ HS Ha1 (IH _ _ _ Hb1)) HT).
    - destruct (inv_fst S sg _ _ _ H) as (A & B & Hp1 & HT).
      exact (ctype_typed S sg _ _ _ _ (T_Fst _ _ _ _ _ _ (IH _ _ _ Hp1)) HT).
    - destruct (inv_snd S sg _ _ _ H) as (A & B & Hp1 & HT).
      pose proof (T_Snd _ _ _ _ _ _ (IH _ _ _ Hp1)) as H1.
      destruct (sigma_cod_typed _ _ _ _ _ Hp1 (T_Fst _ _ _ _ _ _ Hp1)) as [s HB].
      eapply typed_conv_ctype; [exact H1 | | exact HB | exact HT].
      apply conv_sym, red_conv, red_subst1_arg, rt_step, R_Fst, red1_rename, Hp.
    (* match *)
    - destruct (inv_case S sg _ _ _ _ _ _ _ H) as (d & ps & us & Hdec & Hd & Hel & Hlp & Hlu & Hx & HP1 & Hbs & HT).
      assert (Hr1 : red1 sg (rename r P) (rename r P')) by (apply red1_rename, HP).
      assert (HPn : forall n G' H, typed G' (lift n (rename r P)) H -> typed G' (lift n (rename r P')) H).
      { intros n G' H0 H1. unfold lift in *. rewrite rename_rename in H1 |- *. exact (IH _ _ _ H1). }
      pose proof (T_Case _ _ _ _ _ _ _ _ _ _ _ Hdec Hd Hel Hlp Hlu Hx (IH _ _ _ HP1)
                    (branches_motive _ _ _ _ _ _ _ Hbs Hr1 HPn)) as H1.
      destruct (validity_type S sg Hsig _ _ _ Hx (fun s1 => apps_const_not_srt _ _ s1)) as [sx HX].
      pose proof (case_type_typed S sg Hsig _ _ _ _ _ _ _ _ _ Hd Hlp Hlu Hx HP1 HX) as HPT.
      eapply typed_conv_ctype; [exact H1 | | exact HPT | exact HT].
      apply conv_sym, red_conv, rt_step, red1_apps_head, Hr1.
    - destruct (inv_case S sg _ _ _ _ _ _ _ H) as (d & ps & us & Hdec & Hd & Hel & Hlp & Hlu & Hx1 & HP & Hbs & HT).
      pose proof (T_Case _ _ _ _ _ _ _ _ _ _ _ Hdec Hd Hel Hlp Hlu (IH _ _ _ Hx1) HP Hbs) as H1.
      destruct (validity_type S sg Hsig _ _ _ Hx1 (fun s1 => apps_const_not_srt _ _ s1)) as [sx HX].
      pose proof (case_type_typed S sg Hsig _ _ _ _ _ _ _ _ _ Hd Hlp Hlu Hx1 HP HX) as HPT.
      eapply typed_conv_ctype; [exact H1 | | exact HPT | exact HT].
      rewrite !apps_snoc. apply conv_sym, red_conv, rt_step, R_AppArg, red1_rename, Hx.
    - rewrite map_app in H |- *. cbn [map] in H |- *.
      destruct (inv_case S sg _ _ _ _ _ _ _ H) as (d & ps & us & Hdec & Hd & Hel & Hlp & Hlu & Hx & HP & Hbs & HT).
      exact (ctype_typed S sg _ _ _ _ (T_Case _ _ _ _ _ _ _ _ _ _ _ Hdec Hd Hel Hlp Hlu Hx HP
               (branches_replace _ _ _ _ _ _ _ _ _ Hbs (IH r G))) HT).
    (* fix *)
    - destruct (inv_fix S sg _ _ _ _ _ H) as (s & D & HA1 & Hsa & Hne & Hb & Hg & HT).
      pose proof (IH r G _ HA1) as HA2.
      assert (Hr1 : red1 sg (rename r A) (rename r A')) by (apply red1_rename, HA).
      assert (Hc : rename r A ≡ rename r A') by (apply red_conv, rt_step, Hr1).
      pose proof (ctx_conv1 S sg _ _ _ _ _ _ Hb HA2 Hc) as Hb1.
      pose proof (typing_weaken1 S sg _ _ _ _ _ HA2 HA2) as HL. change (lift 1 (Srt s)) with (Srt s) in HL.
      pose proof (T_Conv _ _ _ _ _ _ _ Hb1 HL (conv_rename (Nat.add 1) _ _ Hc)) as Hb2.
      pose proof (T_Fix _ _ _ _ _ _ _ _ HA2 (struct_arg_red _ _ _ _ Hsa _ (rt_step _ _ _ _ Hr1)) Hne Hb2 Hg) as H1.
      exact (typed_conv_ctype _ _ _ _ _ _ H1 (conv_sym _ _ Hc) HA1 HT).
    - destruct (inv_fix S sg _ _ _ _ _ H) as (s & D & HA & Hsa & Hne & Hb1 & Hg & HT).
      pose proof (fix_guarded_red1 _ _ _ _ Hg (red1_rename _ _ (up_ren r) Hb)) as Hg'.
      exact (ctype_typed S sg _ _ _ _ (T_Fix _ _ _ _ _ _ _ _ HA Hsa Hne (IH _ _ _ Hb1) Hg') HT).
    (* δ, ι of an instance, unfolding of a fix, ι of a match *)
    - rewrite (delta_closed_rename sg g b r Hd). exact (sr_delta _ _ _ _ Hd H).
    - exact (sr_spine _ _ _ _ (spine_iota_rename sg r t u Hsp) H).
    - exact (sr_case_iota _ _ _ _ (case_iota_rename sg r t u Hca) H).
  Qed.

  Theorem subject_red1 : forall G t t' T, typed G t T -> red1 sg t t' -> typed G t' T.
  Proof.
    intros G t t' T H Hr. rewrite <- (rename_id t) in H. rewrite <- (rename_id t').
    exact (subject_red1_ren _ _ Hr _ _ _ H).
  Qed.

  Theorem subject_red : forall G t t' T, typed G t T -> red sg t t' -> typed G t' T.
  Proof.
    intros G t t' T H Hr. revert H. induction Hr as [t t' Hr | t | t u v _ IH1 _ IH2]; intros H.
    - exact (subject_red1 _ _ _ _ H Hr).
    - exact H.
    - exact (IH2 (IH1 H)).
  Qed.
End SubjectRed.
