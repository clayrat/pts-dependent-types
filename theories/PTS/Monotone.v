(** * Monotonicity in the signature and in the table

    A signature [sg'] extends [sg] ([sig_le]) when it gives every
    constant of [sg] the same type, every declaration and δ-body of [sg]
    the same, and every instance with active rules of [sg] the same type
    with active rules.  It may add constants, and it may activate the
    rules of an instance that [sg] has without them: a registration
    checks the rules of an instance in a signature where it is inactive,
    then adds it active.  Reduction and conversion grow with the
    signature, and so do the declarative judgments ([typing_sig_mono]).

    The guard of a [fix] reads the constructors of the type a match
    eliminates; in a typed body every match is on a declared type, which
    [sg'] declares alike ([guarded_sig_mono]).

    A table [S'] contains [S] ([spec_le] of PTS.Spec): the annotated
    judgments of [S] are judgments of [S'] ([bidir_spec_mono]). *)

From Stdlib Require Import List Bool Arith Lia Relations.
From Stdlib Require String.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Telescope Spec Signature Reduction Guard Typing Bidir.

Local Open Scope list_scope.

(** ** Extension of signatures *)

Record sig_le (sg sg' : signature) : Prop := {
  le_type : forall g A, sig_type sg g = Some A -> sig_type sg' g = Some A;
  le_ind : forall D d, sig_ind sg D = Some d -> sig_ind sg' D = Some d;
  le_delta : forall g b, sig_delta sg g = Some b -> sig_delta sg' g = Some b;
  le_elim : forall D s A, sig_elim sg D s = Some (A, true) -> sig_elim sg' D s = Some (A, true);
}.

Lemma sig_le_refl : forall sg, sig_le sg sg.
Proof. intros sg. constructor; auto. Qed.

Lemma sig_le_trans : forall sg1 sg2 sg3, sig_le sg1 sg2 -> sig_le sg2 sg3 -> sig_le sg1 sg3.
Proof.
  intros sg1 sg2 sg3 [H1 H2 H3 H4] [H1' H2' H3' H4']. constructor; auto.
Qed.

(** Signatures with the same entries. *)
Lemma sig_le_entries : forall sg sg', sig_entries sg = sig_entries sg' -> sig_le sg sg'.
Proof.
  intros sg sg' E.
  assert (Hi : forall D, sig_ind sg D = sig_ind sg' D) by (intros D; unfold sig_ind; rewrite E; reflexivity).
  assert (He : forall D s, sig_elim sg D s = sig_elim sg' D s) by (intros D s; unfold sig_elim; rewrite E; reflexivity).
  assert (Hd : forall f, sig_def sg f = sig_def sg' f) by (intros f; unfold sig_def; rewrite E; reflexivity).
  constructor.
  - intros [D | D c | D s | f] A H; cbn [sig_type] in *; [rewrite <- Hi | rewrite <- Hi | rewrite <- He | rewrite <- Hd];
      exact H.
  - intros D d H. rewrite <- Hi. exact H.
  - intros [D | D c | D s | f] b H; cbn [sig_delta] in *; try discriminate H. rewrite <- Hd. exact H.
  - intros D s A H. rewrite <- He. exact H.
Qed.

Section Extension.
  Variables sg sg' : signature.
  Hypothesis Hle : sig_le sg sg'.

  Lemma elim_view_mono : forall t e, elim_view sg t = Some e -> elim_view sg' t = Some e.
  Proof.
    intros t e H. unfold elim_view, elim_head in *.
    destruct (spine_head t) as [ | | | | | | | | | | | | | | | | | | | [ | | D s | ] | | ]; try discriminate H.
    destruct (sig_elim sg D s) as [[A [|]]|] eqn:E; try discriminate H.
    destruct (sig_ind sg D) as [d|] eqn:Ed; try discriminate H.
    rewrite (le_elim _ _ Hle _ _ _ E), (le_ind _ _ Hle _ _ Ed). exact H.
  Qed.

  Lemma iota_mono : forall t u, iota sg t = Some u -> iota sg' t = Some u.
  Proof.
    intros t u H. unfold iota in *.
    destruct (elim_view sg t) as [e|] eqn:E; [ | discriminate H].
    rewrite (elim_view_mono _ _ E). exact H.
  Qed.

  Lemma fix_unfold_iota : forall sg0 t u, fix_unfold t = Some u -> iota sg0 t = None.
  Proof.
    intros sg0 t u H. unfold fix_unfold, fix_view in H. unfold iota, elim_view, elim_head.
    destruct (spine_head t); try discriminate H; reflexivity.
  Qed.

  Lemma spine_iota_mono : forall t u, spine_iota sg t = Some u -> spine_iota sg' t = Some u.
  Proof.
    intros t u H. unfold spine_iota in *.
    destruct (iota sg t) as [v|] eqn:E.
    - rewrite (iota_mono _ _ E). exact H.
    - rewrite (fix_unfold_iota sg' t u H). exact H.
  Qed.

  Lemma case_iota_mono : forall t u, case_iota sg t = Some u -> case_iota sg' t = Some u.
  Proof.
    intros t u H. unfold case_iota in *. destruct t; try discriminate H.
    destruct (sig_ind sg s) as [d|] eqn:E; [ | discriminate H].
    rewrite (le_ind _ _ Hle _ _ E). exact H.
  Qed.

  Lemma red1_mono : forall t u, red1 sg t u -> red1 sg' t u.
  Proof.
    intros t u H. induction H; try (constructor; assumption).
    - apply R_Delta. exact (le_delta _ _ Hle _ _ H).
    - apply R_Spine. exact (spine_iota_mono _ _ H).
    - apply R_Case. exact (case_iota_mono _ _ H).
  Qed.

  Lemma red_mono : forall t u, red sg t u -> red sg' t u.
  Proof.
    intros t u H. induction H as [t u H | t | t u v _ IH1 _ IH2].
    - apply rt_step, red1_mono, H.
    - apply rt_refl.
    - exact (rt_trans _ _ _ _ _ IH1 IH2).
  Qed.

  Lemma conv_mono : forall t u, conv sg t u -> conv sg' t u.
  Proof.
    intros t u H. induction H as [t u H | t | t u _ IH | t u v _ IH1 _ IH2].
    - apply rst_step, red1_mono, H.
    - apply rst_refl.
    - apply rst_sym, IH.
    - exact (rst_trans _ _ _ _ _ IH1 IH2).
  Qed.

  Lemma struct_arg_mono : forall A k D, struct_arg sg A k D -> struct_arg sg' A k D.
  Proof.
    intros A k D H. induction H as [A T B D us H1 H2 | A T B k D H1 _ IH].
    - exact (SA_Here _ _ _ _ _ _ (red_mono _ _ H1) (red_mono _ _ H2)).
    - exact (SA_Next _ _ _ _ _ _ (red_mono _ _ H1) IH).
  Qed.
End Extension.

(** ** Matches on declared types *)

(** [D] is a family of [sg]. *)
Definition declared (sg : signature) (D : String.string) : bool :=
  match sig_ind sg D with Some _ => true | None => false end.

(** Terms whose matches are all on families of [sg]: [allnodes] of
    PTS.Syntax with every constant allowed. *)
Notation decl_cases sg := (cases_in (declared sg)).

Section Guard.
  Variables sg sg' : signature.
  Hypothesis Hle : sig_le sg sg'.
  Variable k : nat.

  Lemma branch_fields_mono : forall ms D x, sig_ind sg D <> None ->
    branch_fields sg ms D x = branch_fields sg' ms D x.
  Proof.
    intros ms D x HD. unfold branch_fields.
    destruct (sig_ind sg D) as [d|] eqn:E; [ | contradiction].
    rewrite (le_ind _ _ Hle _ _ E). reflexivity.
  Qed.

  Theorem guarded_sig_mono : forall ms t, Guarded sg k ms t -> decl_cases sg t = true -> Guarded sg' k ms t.
  Proof.
    induction 1 as
      [ms i args Hself Hk Hsub _ IH | ms i Hi | ms f a Hs _ IHf _ IHa | ms b _ IHb
      | ms A B _ IHA _ IHB | ms A B _ IHA _ IHB | ms A k' b _ IHA _ IHb
      | ms u A _ IHu _ IHA | ms C e _ IHC _ IHe | ms a b _ IHa _ IHb
      | ms C c u _ IHC _ IHc _ IHu | ms C t f b _ IHC _ IHt _ IHf _ IHb
      | ms p _ IHp | ms p _ IHp
      | ms D s P x bs _ IHP _ IHx _ IHbs | ms t Ht ]; intros Hd; cbn [allnodes] in Hd;
      repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [? ?] end.
    - rewrite an_apps in Hd. apply andb_prop in Hd as [_ Hd]. rewrite forallb_forall in Hd.
      apply G_Call; [exact Hself | exact Hk | exact Hsub | ]. intros a Ha. exact (IH a Ha (Hd a Ha)).
    - apply G_Var, Hi.
    - apply G_App; auto.
    - apply G_Lam; auto.
    - apply G_Pi; auto.
    - apply G_Sigma; auto.
    - apply G_Fix; auto.
    - apply G_Ann; auto.
    - apply G_ElimVoid; auto.
    - apply G_Pair; auto.
    - apply G_ElimUnit; auto.
    - apply G_ElimBool; auto.
    - apply G_Fst; auto.
    - apply G_Snd; auto.
    - assert (HD : sig_ind sg D <> None) by (unfold declared in *; intros E; rewrite E in *; discriminate).
      apply G_Case; [auto | auto | ]. intros j b Hj.
      rewrite <- (branch_fields_mono ms D x HD).
      apply (IHbs j b Hj). apply an_peel.
      match goal with H : forallb _ bs = true |- _ => rewrite forallb_forall in H; apply H end.
      exact (nth_error_In _ _ Hj).
    - apply G_Atom, Ht.
  Qed.

  Corollary fix_guarded_sig_mono : forall b, fix_guarded sg k b -> decl_cases sg b = true -> fix_guarded sg' k b.
  Proof.
    intros b (body & -> & H) Hd. exists body. split; [reflexivity | ].
    rewrite an_lams in Hd. exact (guarded_sig_mono _ _ H Hd).
  Qed.
End Guard.

(** ** Typed terms match on declared types *)

Section Declared.
  Variable S : spec.
  Variable sg : signature.

  Theorem typed_decl_cases :
    (forall G, wf_ctx S sg G -> True) /\
    (forall G t A, has_type S sg G t A -> decl_cases sg t = true) /\
    (forall G d ps P cs bs, has_branches S sg G d ps P cs bs -> forallb (decl_cases sg) bs = true).
  Proof.
    apply typing_mutind; intros; cbn [allnodes forallb]; auto;
      repeat match goal with H : ?x = true |- context [?x] => rewrite H end; auto.
    - (* a match *)
      unfold declared. match goal with H : sig_ind sg _ = Some _ |- _ => rewrite H end.
      repeat match goal with H : ?x = true |- context [?x] => rewrite H end. reflexivity.
  Qed.
End Declared.

(** ** The declarative judgments grow with the signature *)

Section Typing.
  Variable S : spec.
  Variables sg sg' : signature.
  Hypothesis Hle : sig_le sg sg'.

  Theorem typing_sig_mono :
    (forall G, wf_ctx S sg G -> wf_ctx S sg' G) /\
    (forall G t A, has_type S sg G t A -> has_type S sg' G t A) /\
    (forall G d ps P cs bs, has_branches S sg G d ps P cs bs -> has_branches S sg' G d ps P cs bs).
  Proof.
    apply typing_mutind; intros; try (econstructor; eassumption).
    - eapply T_Conv; [eassumption | eassumption | exact (conv_mono _ _ Hle _ _ c)].
    - eapply T_Const; [eassumption | eassumption | exact (le_type _ _ Hle _ _ e0)].
    - eapply T_Case; try eassumption. exact (le_ind _ _ Hle _ _ e0).
    - eapply T_Fix; [eassumption | exact (struct_arg_mono _ _ Hle _ _ _ s0) | | eassumption | ].
      + intros E. destruct (sig_ind sg D) as [d|] eqn:Ed; [ | contradiction].
        rewrite (le_ind _ _ Hle _ _ Ed) in E. discriminate E.
      + apply (fix_guarded_sig_mono _ _ Hle _ _ f).
        rewrite <- an_lams with (n := 0). exact (proj1 (proj2 (typed_decl_cases S sg)) _ _ _ h0).
  Qed.

  Corollary typed_sig_mono : forall G t A, has_type S sg G t A -> has_type S sg' G t A.
  Proof. exact (proj1 (proj2 typing_sig_mono)). Qed.
End Typing.

(** ** The annotated judgments grow with the table *)

Section Table.
  Variables S S' : spec.
  Variable sg : signature.
  Hypothesis Hle : spec_le S S'.

  Lemma allows_elimination_mono : forall cls s,
    allows_elimination S cls s = true -> allows_elimination S' cls s = true.
  Proof.
    intros cls s H. unfold allows_elimination in *. apply andb_prop in H as [H1 H2].
    rewrite (sle_sort _ _ Hle _ H1). exact H2.
  Qed.

  Theorem bidir_spec_mono :
    (forall G t A, synth S sg G t A -> synth S' sg G t A) /\
    (forall G t A, chk S sg G t A -> chk S' sg G t A) /\
    (forall G d ps P cs bs, chk_branches S sg G d ps P cs bs -> chk_branches S' sg G d ps P cs bs).
  Proof.
    apply synth_chk_mut; intros;
      repeat match goal with
      | H : spec_axiom (spec_table S) _ = _ |- _ => apply (sle_axiom _ _ Hle) in H
      | H : spec_rule (spec_table S) _ _ = _ |- _ => apply (sle_rule _ _ Hle) in H
      | H : spec_sigma (spec_table S) _ _ = _ |- _ => apply (sle_sigma _ _ Hle) in H
      | H : spec_prim (spec_table S) = _ |- _ => apply (sle_prim _ _ Hle) in H
      | H : spec_decls (spec_table S) = true |- _ => apply (sle_decls _ _ Hle) in H
      | H : allows_elimination (spec_table S) _ _ = true |- _ => apply allows_elimination_mono in H
      end;
      econstructor; eassumption.
  Qed.

  Lemma bwf_spec_mono : forall G, bwf_ctx S sg G -> bwf_ctx S' sg G.
  Proof.
    induction 1; econstructor; [eassumption | exact (proj1 bidir_spec_mono _ _ _ H0) | eassumption].
  Qed.

  Lemma btype_spec_mono : forall G A, btype S sg G A -> btype S' sg G A.
  Proof.
    intros G A [(s & -> & Hs) | (T & s & HT & Hr)].
    - left. exists s. split; [reflexivity | exact (sle_sort _ _ Hle _ Hs)].
    - right. exists T, s. split; [exact (proj1 bidir_spec_mono _ _ _ HT) | exact Hr].
  Qed.
End Table.
