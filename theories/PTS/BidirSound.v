(** * Soundness of the annotated kernel for the declarative rules

    A term that synthesizes [A] in an admissible context ([bwf_ctx]) has
    the type [A] by the rules of PTS.Typing, and the context is
    well-formed ([bidir_sound], [bwf_wf]).  A term checked against an
    expected type that is a type, or a sort, has that type.

    The proof is an induction over the three judgments.  Unfolding a
    type by [⇝*] keeps it a type (subject reduction, PTS.SubjectRed),
    and the declarative rule [T_Conv] goes back to it; an expected type
    that is a sort without a type, the top sort △ of U⁻, is reached from
    the synthesized type by reduction, since a sort reduces only to
    itself.

    ** Two premises for [match]

    [S_Case] builds the type of the motive, [Πθ̄:Θ̄[ps]. D ps θ̄ → s], and
    the type of each branch from the description of D and checks the
    motive and the branches against them; it does not check that they are
    types.  [T_Case] needs them to be (validity), and they are types
    when
    - the table is full ([full_table] of PTS.Spec): every sort has a type and every
      pair of sorts a Π-rule.  Otherwise the motive type is not formed:
      with a top sort □, [λ_. ∗ ⇓ Π_:D. □] holds while [Π_:D. □] has no
      type; a missing rule [(s_D, s')] for [s : s'] does the same.  The
      predicative hierarchies, the tables where constants are on, are
      full (Configs.Predicative);
    - the constructors of a type have distinct names ([ctors_distinct]).
      The constant [Ctor D c] has the type of the first constructor
      named [c] ([find_ctor]), the one [signature_typed] covers, while
      the branch of a second one applies it to the fields of the second,
      whose types nothing checks.  The registration of a declaration
      refuses two constructors with one name.

    The motive type is formed from the type of D instantiated at the
    parameters, which the type of the scrutinee gives ([motive_typed]);
    the type of a branch from the type of the constructor, the fields
    taken as variables, and the motive ([branch_typed]).  Both swap the
    codomain of a telescope of types for another type ([pis_swap]), which
    needs the rules of a full table. *)

From Stdlib Require Import List Bool Arith Lia Relations.
From Stdlib Require String.
Import ListNotations.
From DepTypes.Common Require Import Lists.
From DepTypes.PTS Require Import Syntax Telescope Spec Signature Reduction SubstLaws Confluence Guard
  Typing TypingSubst Inversion SubjectRed Bidir.

Local Open Scope list_scope.

(** ** The premise on signatures

    [full_table], the premise on tables, is in PTS.Spec. *)

Definition ctors_distinct (sg : signature) : Prop :=
  forall D d, sig_ind sg D = Some d -> NoDup (map ctor_name (ind_ctors d)).

Lemma find_ctor_nodup : forall cs c, NoDup (map ctor_name cs) -> In c cs ->
  exists i, find_ctor cs (ctor_name c) = Some (i, c).
Proof.
  induction cs as [|c' cs IH]; intros c Hnd Hin; [destruct Hin | ].
  cbn [map] in Hnd. apply NoDup_cons_iff in Hnd as [Hnotin Hnd].
  cbn [find_ctor]. destruct Hin as [-> | Hin].
  - rewrite String.eqb_refl. exists 0. reflexivity.
  - destruct (String.eqb (ctor_name c') (ctor_name c)) eqn:E.
    + apply String.eqb_eq in E. exfalso. apply Hnotin. rewrite E. apply in_map. exact Hin.
    + destruct (IH c Hnd Hin) as [i Hi]. rewrite Hi. exists (S i). reflexivity.
Qed.

(** ** Syntax *)

Lemma apps_app : forall h l1 l2, apps h (l1 ++ l2) = apps (apps h l1) l2.
Proof. intros h l1 l2. unfold apps. apply fold_left_app. Qed.

Lemma lift_apps_const : forall n g l, lift n (apps (Const g) l) = apps (Const g) (map (lift n) l).
Proof. intros n g l. unfold lift. rewrite rename_apps. reflexivity. Qed.

Lemma lift_add : forall m n t, lift m (lift n t) = lift (m + n) t.
Proof. intros m n t. unfold lift. rewrite rename_rename. apply rename_ext. intros i. lia. Qed.

Lemma lift_app : forall n f a, lift n (App f a) = App (lift n f) (lift n a).
Proof. reflexivity. Qed.

Lemma lift_var : forall n i, lift n (Var i) = Var (n + i).
Proof. reflexivity. Qed.

Lemma map_upn_vars : forall n sb p,
  map (subst (upn n sb)) (vars n p) = map (lift n) (map (subst sb) (vars 0 p)).
Proof.
  intros n sb p. induction p as [|p IH]; [reflexivity | ].
  cbn [vars map subst]. rewrite IH, upn_ge. reflexivity.
Qed.

Lemma lift_case_motive_type : forall n d ps s, tele_closed (length ps) (ind_indices d) = true ->
  lift n (case_motive_type d ps s) = case_motive_type d (map (lift n) ps) s.
Proof. intros n d ps s H. exact (rename_case_motive_type d ps s (Nat.add n) H). Qed.

(** The motive type, its telescope substituted at once. *)
Lemma case_motive_type_tsub : forall sg D d ps s, sig_ind sg D = Some d ->
  length ps = length (ind_params d) ->
  case_motive_type d ps s =
  pis (subst_tele (tsub ps) (ind_indices d))
      (Pi (apps (Const (Ind D)) (map (lift (length (ind_indices d))) ps ++ vars 0 (length (ind_indices d))))
          (Srt s)).
Proof.
  intros sg D d ps s Hd Hlp. unfold case_motive_type, inst_tele. cbv zeta.
  rewrite (sig_ind_name _ _ _ Hd). f_equal.
  apply (inst_tele_tsub _ ps 0). rewrite Hlp. exact (proj1 (sig_ind_closed _ _ _ Hd)).
Qed.

(** The type of a constructor, its parameters apart. *)
Lemma ctor_type_split : forall sg D d c, sig_ind sg D = Some d ->
  ctor_type d c =
  pis (ind_params d)
      (pis (field_types D (length (ind_params d)) 0 (ctor_fields c))
           (apps (Const (Ind D)) (vars (length (ctor_fields c)) (length (ind_params d)) ++ ctor_indices c))).
Proof.
  intros sg D d c Hd. unfold ctor_type. cbv zeta. rewrite (sig_ind_name _ _ _ Hd). apply pis_app.
Qed.

(** The type of a branch, the parameters substituted at once. *)
Lemma case_branch_type_tsub : forall sg D d ps P c, sig_ind sg D = Some d -> In c (ind_ctors d) ->
  length ps = length (ind_params d) ->
  let n := length (ctor_fields c) in
  case_branch_type d ps P c =
  pis (subst_tele (tsub ps) (field_types D (length (ind_params d)) 0 (ctor_fields c)))
      (apps (lift n P)
         (map (subst (upn n (tsub ps))) (ctor_indices c) ++
          [apps (Const (Ctor D (ctor_name c))) (map (lift n) ps ++ vars 0 n)])).
Proof.
  intros sg D d ps P c Hd Hin Hlp n.
  pose proof (proj2 (sig_ind_closed _ _ _ Hd)) as Hcs. rewrite forallb_forall in Hcs.
  pose proof (Hcs c Hin) as Hc. unfold ctor_closed in Hc. apply andb_prop in Hc as [Hf Hi].
  unfold case_branch_type. cbv zeta. rewrite (sig_ind_name _ _ _ Hd). f_equal.
  - apply (inst_tele_tsub _ ps 0). cbn [Nat.add]. rewrite Hlp.
    pose proof (field_types_closed D (length (ind_params d)) (ctor_fields c) 0) as H.
    rewrite Nat.add_0_r in H. exact (H Hf).
  - f_equal. f_equal. apply map_ext_in. intros v Hv. apply inst_env_tsub.
    rewrite Hlp, Nat.add_comm. rewrite forallb_forall in Hi. exact (Hi v Hv).
Qed.

(** ** Terms without reducts *)

Section Fixed.
  Variable sg : signature.

  Lemma red_fixed : forall a, (forall u, ~ red1 sg a u) -> forall u, red sg a u -> u = a.
  Proof.
    intros a Ha u H. unfold red in H. apply clos_rt_rt1n in H.
    destruct H as [|y z Hr _]; [reflexivity | exfalso; exact (Ha _ Hr)].
  Qed.

  Lemma conv_fixed : forall a t, (forall u, ~ red1 sg a u) -> conv sg t a -> red sg t a.
  Proof.
    intros a t Ha H. destruct (church_rosser sg t a H) as (w & Ht & Hw).
    rewrite (red_fixed a Ha w Hw) in Ht. exact Ht.
  Qed.

  Lemma red1_srt : forall s u, ~ red1 sg (Srt s) u.
  Proof. intros s u H. inversion H; subst; cbn in *; discriminate. Qed.

  Lemma red1_void : forall u, ~ red1 sg Void u.
  Proof. intros u H. inversion H; subst; cbn in *; discriminate. Qed.

  Lemma red1_unit : forall u, ~ red1 sg Unit u.
  Proof. intros u H. inversion H; subst; cbn in *; discriminate. Qed.

  Lemma red1_bool : forall u, ~ red1 sg Bool u.
  Proof. intros u H. inversion H; subst; cbn in *; discriminate. Qed.

  Lemma red_srt_inv : forall s u, red sg (Srt s) u -> u = Srt s.
  Proof. intros s. exact (red_fixed _ (red1_srt s)). Qed.

  Lemma conv_srt_red : forall t s, conv sg t (Srt s) -> red sg t (Srt s).
  Proof. intros t s. exact (conv_fixed _ _ (red1_srt s)). Qed.

  Lemma conv_srt_inj : forall s s', conv sg (Srt s) (Srt s') -> s = s'.
  Proof.
    intros s s' H. pose proof (red_srt_inv _ _ (conv_srt_red _ _ H)) as E.
    injection E as ->. reflexivity.
  Qed.

  Lemma conv_pi_srt : forall A B s, ~ conv sg (Pi A B) (Srt s).
  Proof.
    intros A B s H. destruct (red_pi_inv sg _ _ _ (conv_srt_red _ _ H)) as (A' & B' & E & _).
    discriminate E.
  Qed.

  Lemma conv_pis_srt : forall Ts R s, Ts <> [] -> ~ conv sg (pis Ts R) (Srt s).
  Proof. intros [|T Ts] R s HTs; [contradiction | exact (conv_pi_srt _ _ _)]. Qed.
End Fixed.

(** ** Uniqueness of synthesized types

    A term that synthesizes [A] has only types convertible to [A].  A λ
    synthesizes nothing, so the domain-free λ of the declarative rules,
    whose types are not unique, is never met: the subterms that decide
    the synthesized type synthesize in turn, and those in checking
    positions enter it only by substitution. *)

Section Unique.
  Variable S : spec.
  Variable sg : signature.
  Local Notation typed := (has_type S sg).
  Local Notation "t ≡ u" := (conv sg t u).

  Theorem synth_unique : forall G t A, synth S sg G t A -> forall T, typed G t T -> A ≡ T.
  Proof.
    intros G t A H. induction H as
      [ G s s' Hax
      | G n A Hl
      | G A B TA TB s1 s2 s3 HA IHA RA HB IHB RB Hr
      | G f u F A B Hf IHf RF Hu
      | G t A T s HA IHA RT Ht
      | G s0 Hp | G s0 Hp | G s0 Hp | G s0 Hp | G s0 Hp | G s0 Hp
      | G C e TC D K s s0 Hp HC IHC RTC HD RK He
      | G C c u TC D K s s0 Hp HC IHC RTC HD RK Hc Hu
      | G C t f b TC D K s s0 Hp HC IHC RTC HD RK Ht Hf Hb
      | G A B TA TB s1 s2 s3 HA IHA RA HB IHB RB Hr
      | G p P A B Hp IHp RP
      | G p P A B Hp IHp RP
      | G g A Hdecl Hg
      | G D s P x bs X d ps us Hdecl Hd Hel Hx IHx RX Hlp Hlu HP Hbs
      | G A k b T s D HA IHA RT Hsa Hne Hb Hgd ]; intros T0 HT0.
    - destruct (inv_sort S sg _ _ _ HT0) as (s'' & Hax' & Hc). rewrite Hax in Hax'. injection Hax' as <-.
      exact (ctype_conv_of S sg _ _ _ Hc).
    - destruct (inv_var S sg _ _ _ HT0) as (A' & Hl' & Hc). rewrite Hl in Hl'. injection Hl' as <-.
      exact (ctype_conv_of S sg _ _ _ Hc).
    - destruct (inv_pi S sg _ _ _ _ HT0) as (s1' & s2' & s3' & HA' & HB' & Hr' & Hc).
      assert (E1 : s1 = s1').
      { apply (conv_srt_inj sg). eapply conv_trans; [apply conv_sym, red_conv, RA | exact (IHA _ HA')]. }
      assert (E2 : s2 = s2').
      { apply (conv_srt_inj sg). eapply conv_trans; [apply conv_sym, red_conv, RB | exact (IHB _ HB')]. }
      subst s1' s2'. rewrite Hr in Hr'. injection Hr' as <-. exact (ctype_conv_of S sg _ _ _ Hc).
    - destruct (inv_app S sg _ _ _ _ HT0) as (A0 & B0 & Hf0 & _ & Hc).
      assert (Hpi : Pi A B ≡ Pi A0 B0) by (eapply conv_trans; [apply conv_sym, red_conv, RF | exact (IHf _ Hf0)]).
      apply pi_inj in Hpi as [_ HB0].
      eapply conv_trans; [unfold subst1; apply conv_subst; exact HB0 | exact (ctype_conv_of S sg _ _ _ Hc)].
    - destruct (inv_ann S sg _ _ _ _ HT0) as (s' & _ & _ & Hc). exact (ctype_conv_of S sg _ _ _ Hc).
    - destruct (inv_prim S sg _ _ _ HT0 (or_introl eq_refl)) as (s1 & Hp' & Hc).
      rewrite Hp in Hp'. injection Hp' as <-. exact (ctype_conv_of S sg _ _ _ Hc).
    - destruct (inv_prim S sg _ _ _ HT0 (or_intror (or_introl eq_refl))) as (s1 & Hp' & Hc).
      rewrite Hp in Hp'. injection Hp' as <-. exact (ctype_conv_of S sg _ _ _ Hc).
    - exact (ctype_conv_of S sg _ _ _ (inv_tt S sg _ _ HT0)).
    - destruct (inv_prim S sg _ _ _ HT0 (or_intror (or_intror eq_refl))) as (s1 & Hp' & Hc).
      rewrite Hp in Hp'. injection Hp' as <-. exact (ctype_conv_of S sg _ _ _ Hc).
    - exact (ctype_conv_of S sg _ _ _ (inv_bool_value S sg _ _ _ HT0 (or_introl eq_refl))).
    - exact (ctype_conv_of S sg _ _ _ (inv_bool_value S sg _ _ _ HT0 (or_intror eq_refl))).
    - destruct (inv_elim_void S sg _ _ _ _ HT0) as (s' & _ & _ & Hc0). exact (ctype_conv_of S sg _ _ _ Hc0).
    - destruct (inv_elim_unit S sg _ _ _ _ _ HT0) as (s' & _ & _ & _ & Hc0). exact (ctype_conv_of S sg _ _ _ Hc0).
    - destruct (inv_elim_bool S sg _ _ _ _ _ _ HT0) as (s' & _ & _ & _ & _ & Hc0).
      exact (ctype_conv_of S sg _ _ _ Hc0).
    - destruct (inv_sigma S sg _ _ _ _ HT0) as (s1' & s2' & s3' & HA' & HB' & Hr' & Hc).
      assert (E1 : s1 = s1').
      { apply (conv_srt_inj sg). eapply conv_trans; [apply conv_sym, red_conv, RA | exact (IHA _ HA')]. }
      assert (E2 : s2 = s2').
      { apply (conv_srt_inj sg). eapply conv_trans; [apply conv_sym, red_conv, RB | exact (IHB _ HB')]. }
      subst s1' s2'. rewrite Hr in Hr'. injection Hr' as <-. exact (ctype_conv_of S sg _ _ _ Hc).
    - destruct (inv_fst S sg _ _ _ HT0) as (A0 & B0 & Hp0 & Hc).
      assert (Hs : Sigma A B ≡ Sigma A0 B0) by (eapply conv_trans; [apply conv_sym, red_conv, RP | exact (IHp _ Hp0)]).
      apply sigma_inj in Hs as [HA0 _]. exact (conv_trans _ _ _ HA0 (ctype_conv_of S sg _ _ _ Hc)).
    - destruct (inv_snd S sg _ _ _ HT0) as (A0 & B0 & Hp0 & Hc).
      assert (Hs : Sigma A B ≡ Sigma A0 B0) by (eapply conv_trans; [apply conv_sym, red_conv, RP | exact (IHp _ Hp0)]).
      apply sigma_inj in Hs as [_ HB0].
      eapply conv_trans; [unfold subst1; apply conv_subst; exact HB0 | exact (ctype_conv_of S sg _ _ _ Hc)].
    - exact (conv_sym _ _ (const_head S sg _ _ _ Hg _ HT0)).
    - destruct (inv_case S sg _ _ _ _ _ _ _ HT0)
        as (d0 & ps0 & us0 & _ & Hd0 & _ & Hlp0 & Hlu0 & Hx0 & _ & _ & Hc).
      rewrite Hd in Hd0. injection Hd0 as <-.
      assert (Hsp : Forall2 (conv sg) (ps ++ us) (ps0 ++ us0)).
      { apply (conv_ind_spine sg D). eapply conv_trans; [apply conv_sym, red_conv, RX | exact (IHx _ Hx0)]. }
      apply forall2_app_split in Hsp as [_ Hus]; [ | lia].
      eapply conv_trans; [ | exact (ctype_conv_of S sg _ _ _ Hc)]. apply conv_apps; [apply conv_refl | ].
      apply Forall2_app; [exact Hus | constructor; [apply conv_refl | constructor]].
    - destruct (inv_fix S sg _ _ _ _ _ HT0) as (s' & D' & _ & _ & _ & _ & _ & Hc). exact (ctype_conv_of S sg _ _ _ Hc).
  Qed.
End Unique.

Section Sound.
  Variable S : spec.
  Variable sg : signature.
  Hypothesis Hsig : signature_typed S sg.
  Local Notation typed := (has_type S sg).
  Local Notation wf := (wf_ctx S sg).
  Local Notation "t ≡ u" := (conv sg t u).
  Local Notation "t ⇝* u" := (red sg t u).

  (** An expected type: a sort, or a term with a sort for type. *)
  Definition tyok (G : ctx) (T : term) : Prop :=
    (exists s, T = Srt s) \/ (exists s, typed G T (Srt s)).

  (** ** Unfolding a type *)

  Lemma typed_red_srt : forall G t T s, typed G t T -> T ⇝* Srt s -> typed G t (Srt s).
  Proof.
    intros G t T s H Hr.
    destruct (validity S sg Hsig _ _ _ H) as [[s' ->] | [s0 HT]].
    - rewrite (red_srt_inv sg _ _ Hr). exact H.
    - exact (T_Conv _ _ _ _ _ _ _ H (subject_red S sg Hsig _ _ _ _ HT Hr) (red_conv _ _ Hr)).
  Qed.

  Lemma typed_red_type : forall G t T U, typed G t T -> T ⇝* U -> (forall s, U <> Srt s) ->
    typed G t U /\ exists s, typed G U (Srt s).
  Proof.
    intros G t T U H Hr HU.
    destruct (validity S sg Hsig _ _ _ H) as [[s' ->] | [s0 HT]].
    - exfalso. exact (HU s' (red_srt_inv sg _ _ Hr)).
    - pose proof (subject_red S sg Hsig _ _ _ _ HT Hr) as HU'.
      split; [exact (T_Conv _ _ _ _ _ _ _ H HU' (red_conv _ _ Hr)) | exists s0; exact HU'].
  Qed.

  Lemma typed_conv_tyok : forall G t A B, typed G t A -> A ≡ B -> tyok G B -> typed G t B.
  Proof.
    intros G t A B H Hc [[s ->] | [s HB]].
    - exact (typed_red_srt _ _ _ _ H (conv_srt_red sg _ _ Hc)).
    - exact (T_Conv _ _ _ _ _ _ _ H HB Hc).
  Qed.

  (** ** Telescopes of types *)

  Inductive tele_ok : ctx -> list term -> Prop :=
  | TO_Nil : forall G, tele_ok G []
  | TO_Cons : forall G T Ts s, typed G T (Srt s) -> spec_sort S s = true ->
      tele_ok (T :: G) Ts -> tele_ok G (T :: Ts).

  Lemma pis_tele_ok : forall Ts G R s, typed G (pis Ts R) (Srt s) -> tele_ok G Ts.
  Proof.
    induction Ts as [|T Ts IH]; intros G R s H; [constructor | ].
    cbn [pis] in H. destruct (inv_pi S sg _ _ _ _ H) as (s1 & s2 & s3 & HT & HB & Hr & _).
    econstructor; [exact HT | exact (proj1 (spec_rule_sorts S _ _ _ Hr)) | exact (IH _ _ _ HB)].
  Qed.

  Lemma typed_tele_ok : forall G h Ts R, typed G h (pis Ts R) -> tele_ok G Ts.
  Proof.
    intros G h [|T Ts] R H; [constructor | ].
    destruct (validity_type S sg Hsig _ _ _ H (fun s E => ltac:(discriminate E))) as [s HP].
    exact (pis_tele_ok _ _ _ _ HP).
  Qed.

  Lemma tele_weaken : forall G Ts, tele_ok G Ts -> forall t A, typed G t A ->
    typed (rev Ts ++ G) (lift (length Ts) t) (lift (length Ts) A).
  Proof.
    intros G Ts H. induction H as [G | G T Ts s HT Hs _ IH]; intros t A Ht.
    - cbn [rev app length]. rewrite !lift_zero. exact Ht.
    - pose proof (IH _ _ (typing_weaken1 S sg _ _ _ _ _ Ht HT)) as H2.
      cbn [rev length]. rewrite <- app_assoc. cbn [app].
      rewrite !lift_add, Nat.add_1_r in H2. exact H2.
  Qed.

  (** A function of type [Π Ts. R] applied to the variables of [Ts]. *)
  Lemma typed_vars : forall G Ts, tele_ok G Ts -> forall h R, typed G h (pis Ts R) ->
    typed (rev Ts ++ G) (apps (lift (length Ts) h) (vars 0 (length Ts))) R.
  Proof.
    intros G Ts H. induction H as [G | G T Ts s HT Hs _ IH]; intros h R Hh.
    - cbn [rev app length vars]. unfold apps. cbn [fold_left]. rewrite lift_zero. exact Hh.
    - cbn [pis] in Hh. pose proof (typing_weaken1 S sg _ _ _ _ _ Hh HT) as H1.
      unfold lift at 2 in H1. cbn [rename] in H1.
      assert (H0 : typed (T :: G) (Var 0) (lift 1 T)).
      { apply T_Var; [exact (W_Cons _ _ _ _ _ HT) | apply lookup_cons_0]. }
      pose proof (T_App _ _ _ _ _ _ _ H1 H0) as H2. rewrite subst_shift_back in H2.
      pose proof (IH _ _ H2) as H3.
      rewrite lift_app, lift_var, lift_add, Nat.add_0_r, Nat.add_1_r in H3.
      cbn [rev length]. rewrite <- app_assoc. cbn [app].
      change (vars 0 (Datatypes.S (length Ts))) with (Var (length Ts) :: vars 0 (length Ts)). exact H3.
  Qed.

  (** The codomain of a telescope of types replaced by another type. *)
  Lemma pis_swap : full_table S -> forall G Ts, tele_ok G Ts -> forall R s,
    typed (rev Ts ++ G) R (Srt s) -> spec_sort S s = true ->
    exists s', typed G (pis Ts R) (Srt s') /\ spec_sort S s' = true.
  Proof.
    intros [_ Hrule] G Ts H. induction H as [G | G T Ts s1 HT Hs1 _ IH]; intros R s HR Hs.
    - exists s. split; [exact HR | exact Hs].
    - cbn [rev] in HR. rewrite <- app_assoc in HR. cbn [app] in HR.
      destruct (IH _ _ HR Hs) as (s2 & H2 & Hs2).
      destruct (Hrule _ _ Hs1 Hs2) as [s3 Hr].
      exists s3. split; [exact (T_Pi _ _ _ _ _ _ _ _ HT H2 Hr) | exact (proj2 (proj2 (spec_rule_sorts S _ _ _ Hr)))].
  Qed.

  Lemma pis_srt_sort : forall Ts G s s0, typed G (pis Ts (Srt s)) (Srt s0) -> spec_sort S s = true.
  Proof.
    induction Ts as [|T Ts IH]; intros G s s0 H; cbn [pis] in H.
    - exact (typed_sort_in_spec _ _ _ _ _ H).
    - destruct (inv_pi S sg _ _ _ _ H) as (s1 & s2 & s3 & _ & HB & _ & _). exact (IH _ _ _ HB).
  Qed.

  (** ** Spines of an inductive type *)

  Lemma apps_prefix_typed : forall l2 l1 G h T, typed G (apps h (l1 ++ l2)) T ->
    exists T', typed G (apps h l1) T'.
  Proof.
    induction l2 as [|a l2 IH] using rev_ind; intros l1 G h T H.
    - rewrite app_nil_r in H. exists T. exact H.
    - rewrite app_assoc, apps_snoc in H. destruct (inv_app S sg _ _ _ _ H) as (A & B & Hf & _ & _).
      exact (IH _ _ _ _ Hf).
  Qed.

  (** A spine of a sort applies its head to the whole telescope. *)
  Lemma spine_length : forall args G h Ts s0 s1 s,
    typed G (apps h args) (Srt s) -> (forall H, typed G h H -> H ≡ pis Ts (Srt s0)) ->
    typed G (pis Ts (Srt s0)) (Srt s1) -> length args = length Ts.
  Proof.
    intros args G h Ts s0 s1 s H Hh HT.
    destruct (Nat.le_gt_cases (length args) (length Ts)) as [Hle | Hgt].
    - rewrite <- (firstn_skipn (length args) Ts) in Hh, HT. rewrite pis_app in Hh, HT.
      destruct (apps_inv S sg args G h _ _ _ _ (firstn_length_le _ Hle) H Hh HT) as [_ Hc].
      rewrite subst_pis in Hc. cbn [subst] in Hc.
      destruct (skipn (length args) Ts) as [|T Ts'] eqn:E.
      + pose proof (f_equal (@length term) E) as El. rewrite length_skipn in El. cbn in El. lia.
      + exfalso. exact (conv_pi_srt _ _ _ _ Hc).
    - exfalso. rewrite <- (firstn_skipn (length Ts) args) in H.
      destruct (skipn (length Ts) args) as [|a rest] eqn:E.
      + pose proof (f_equal (@length term) E) as El. rewrite length_skipn in El. cbn in El. lia.
      + change (a :: rest) with ([a] ++ rest) in H. rewrite app_assoc in H.
        destruct (apps_prefix_typed _ _ _ _ _ H) as [T' HT']. rewrite apps_snoc in HT'.
        destruct (inv_app S sg _ _ _ _ HT') as (A & B & Hf & _ & _).
        assert (Hl : length Ts = length (firstn (length Ts) args)) by (rewrite firstn_length_le; lia).
        destruct (apps_inv S sg _ G h _ _ _ _ Hl Hf Hh HT) as [_ Hc]. cbn [subst] in Hc.
        exact (conv_pi_srt _ _ _ _ (conv_sym _ _ Hc)).
  Qed.

  (** [D ps] has the type of D instantiated at the parameters. *)
  Lemma ind_params_typed : spec_decls S = true -> forall G D d ps, sig_ind sg D = Some d -> wf G ->
    length ps = length (ind_params d) -> args_typed S sg G (ind_params d) ps ->
    typed G (apps (Const (Ind D)) ps) (pis (subst_tele (tsub ps) (ind_indices d)) (Srt (ind_sort d))).
  Proof.
    intros Hdecl G D d ps Hd HG Hlp Hps.
    pose proof (T_Const _ _ _ _ _ HG Hdecl (sig_type_ind _ _ _ Hd)) as HD. unfold ind_type in HD.
    rewrite pis_app in HD. pose proof (typed_apps _ _ _ _ _ _ _ Hps HD) as H.
    rewrite subst_pis in H. exact H.
  Qed.

  Lemma ind_sort_spec : forall D d, sig_ind sg D = Some d -> spec_sort S (ind_sort d) = true.
  Proof.
    intros D d Hd. destruct Hsig as [Hty _]. destruct (Hty _ _ (sig_type_ind _ _ _ Hd)) as [s0 Hs0].
    exact (pis_srt_sort _ _ _ _ Hs0).
  Qed.

  (** ** The types built by [S_Case] are types *)

  Lemma motive_typed : full_table S -> spec_decls S = true -> forall G D d ps s,
    sig_ind sg D = Some d -> wf G -> length ps = length (ind_params d) ->
    args_typed S sg G (ind_params d) ps -> spec_sort S s = true ->
    exists s', typed G (case_motive_type d ps s) (Srt s').
  Proof.
    intros Hfull Hdecl G D d ps s Hd HG Hlp Hps Hs.
    pose proof (ind_params_typed Hdecl _ _ _ _ Hd HG Hlp Hps) as Hh.
    pose proof (typed_tele_ok _ _ _ _ Hh) as Hto.
    pose proof (typed_vars _ _ Hto _ _ Hh) as HX.
    rewrite subst_tele_length, lift_apps_const, <- apps_app in HX.
    pose proof (ind_sort_spec _ _ Hd) as HsD.
    destruct Hfull as [Hax Hrule].
    destruct (Hax s Hs) as [sa Hsa]. pose proof (proj2 (spec_axiom_sorts S _ _ Hsa)) as Hsa'.
    destruct (Hrule _ _ HsD Hsa') as [s3 Hr].
    assert (HPi : typed (rev (subst_tele (tsub ps) (ind_indices d)) ++ G)
                    (Pi (apps (Const (Ind D)) (map (lift (length (ind_indices d))) ps ++
                                               vars 0 (length (ind_indices d)))) (Srt s)) (Srt s3)).
    { apply (T_Pi _ _ _ _ _ _ sa _ HX); [ | exact Hr]. apply T_Sort; [exact (W_Cons _ _ _ _ _ HX) | exact Hsa]. }
    destruct (pis_swap (conj Hax Hrule) _ _ Hto _ _ HPi (proj2 (proj2 (spec_rule_sorts S _ _ _ Hr))))
      as (s' & H' & _).
    exists s'. rewrite (case_motive_type_tsub _ _ _ _ _ Hd Hlp). exact H'.
  Qed.

  Lemma branch_typed : full_table S -> spec_decls S = true -> forall G D d ps P s c,
    sig_ind sg D = Some d -> NoDup (map ctor_name (ind_ctors d)) -> In c (ind_ctors d) ->
    length ps = length (ind_params d) -> args_typed S sg G (ind_params d) ps ->
    typed G P (case_motive_type d ps s) -> spec_sort S s = true ->
    exists s', typed G (case_branch_type d ps P c) (Srt s').
  Proof.
    intros Hfull Hdecl G D d ps P s c Hd Hnd Hin Hlp Hps HP Hs.
    pose proof (typed_wf _ _ _ _ _ HP) as HG.
    set (p := length (ind_params d)) in *.
    set (n := length (ctor_fields c)).
    set (Fs := field_types D p 0 (ctor_fields c)).
    (* the constructor, applied to the parameters *)
    destruct (find_ctor_nodup _ _ Hnd Hin) as [i Hi].
    assert (Hc : sig_type sg (Ctor D (ctor_name c)) = Some (ctor_type d c)).
    { cbn [sig_type]. rewrite Hd, Hi. reflexivity. }
    pose proof (T_Const _ _ _ _ _ HG Hdecl Hc) as HC.
    rewrite (ctor_type_split _ _ _ c Hd) in HC.
    pose proof (typed_apps _ _ _ _ _ _ _ Hps HC) as Hh.
    rewrite subst_pis, subst_apps, map_app in Hh. cbn [subst] in Hh. fold p n Fs in Hh.
    assert (En : length Fs = n) by apply field_types_length.
    rewrite En, map_upn_vars, <- Hlp, map_tsub_vars0 in Hh.
    set (Fs' := subst_tele (tsub ps) Fs) in *.
    set (idx := map (subst (upn n (tsub ps))) (ctor_indices c)) in *.
    assert (En' : length Fs' = n) by (unfold Fs'; rewrite subst_tele_length; exact En).
    pose proof (typed_tele_ok _ _ _ _ Hh) as Hto.
    (* the constructor applied to the fields as variables *)
    pose proof (typed_vars _ _ Hto _ _ Hh) as Hx.
    rewrite En', lift_apps_const, <- apps_app in Hx.
    pose proof (typed_wf _ _ _ _ _ Hx) as HG'.
    destruct (validity_type S sg Hsig _ _ _ Hx (apps_const_not_srt _ _)) as [sY HY].
    (* the indices of its type are typed against those of D *)
    pose proof (sig_type_ind _ _ _ Hd) as Hty.
    destruct (const_type_typed S sg Hsig _ _ _ HG' Hty) as [s0 Hs0]. unfold ind_type in Hs0.
    pose proof (const_head S sg (rev Fs' ++ G) _ _ Hty) as Hhd. unfold ind_type in Hhd.
    pose proof (spine_length _ _ _ _ _ _ _ HY Hhd Hs0) as Hl. symmetry in Hl.
    destruct (apps_inv S sg _ _ _ _ _ _ _ Hl HY Hhd Hs0) as [Hargs _].
    assert (Hlp' : length (ind_params d) = length (map (lift n) ps)) by (rewrite length_map; exact (eq_sym Hlp)).
    destruct (proj1 (args_typed_app S sg _ _ _ _ _ Hlp') Hargs) as [_ Hidx].
    assert (Hq : length (ind_indices d) = length idx).
    { rewrite <- (subst_tele_length _ (tsub (map (lift n) ps))). exact (args_typed_length _ _ _ _ _ Hidx). }
    (* the motive, under the fields, applied to the indices and to the constructor *)
    pose proof (tele_weaken _ _ Hto _ _ HP) as HP'. rewrite En' in HP'.
    rewrite lift_case_motive_type in HP' by (rewrite Hlp; exact (proj1 (sig_ind_closed _ _ _ Hd))).
    rewrite (case_motive_type_tsub _ _ _ _ _ Hd ltac:(rewrite length_map; exact Hlp)) in HP'.
    pose proof (typed_apps _ _ _ _ _ _ _ Hidx HP') as HPi.
    cbn [subst] in HPi. rewrite subst_apps, map_app, Hq, map_tsub_lift, map_tsub_vars0 in HPi.
    cbn [subst] in HPi.
    pose proof (T_App _ _ _ _ _ _ _ HPi Hx) as HR. rewrite <- apps_snoc in HR.
    destruct (pis_swap Hfull _ _ Hto _ _ HR Hs) as (s' & H' & _).
    exists s'. rewrite (case_branch_type_tsub _ _ _ _ _ _ Hd Hin Hlp). exact H'.
  Qed.

  (** ** Soundness *)

  Hypothesis Hfull : spec_decls S = true -> full_table S.
  Hypothesis Hdist : ctors_distinct sg.

  Theorem bidir_sound :
    (forall G t A, synth S sg G t A -> wf G -> typed G t A) /\
    (forall G t B, chk S sg G t B -> wf G -> tyok G B -> typed G t B) /\
    (forall G d ps P cs bs, chk_branches S sg G d ps P cs bs -> wf G ->
       (forall c, In c cs -> tyok G (case_branch_type d ps P c)) -> has_branches S sg G d ps P cs bs).
  Proof.
    apply synth_chk_mut.
    - (* S_Sort *) intros G s s' Hax HG. exact (T_Sort _ _ _ _ _ HG Hax).
    - (* S_Var *) intros G n A Hl HG. exact (T_Var _ _ _ _ _ HG Hl).
    - (* S_Pi *) intros G A B TA TB s1 s2 s3 _ IHA HA _ IHB HB Hr HG.
      pose proof (typed_red_srt _ _ _ _ (IHA HG) HA) as HA'.
      pose proof (typed_red_srt _ _ _ _ (IHB (W_Cons _ _ _ _ _ HA')) HB) as HB'.
      exact (T_Pi _ _ _ _ _ _ _ _ HA' HB' Hr).
    - (* S_App *) intros G f u F A B _ IHf HF _ IHu HG.
      destruct (typed_red_type _ _ _ _ (IHf HG) HF (fun s E => ltac:(discriminate E))) as [Hf [s0 HPi]].
      destruct (inv_pi S sg _ _ _ _ HPi) as (s1 & s2 & s3 & HA & _ & _ & _).
      exact (T_App _ _ _ _ _ _ _ Hf (IHu HG (or_intror (ex_intro _ s1 HA)))).
    - (* S_Ann *) intros G t A T s _ IHA HT _ IHt HG.
      pose proof (typed_red_srt _ _ _ _ (IHA HG) HT) as HA.
      exact (T_Ann _ _ _ _ _ _ HA (IHt HG (or_intror (ex_intro _ s HA)))).
    - intros G s0 Hp HG. exact (T_Void _ _ _ _ HG Hp).
    - intros G s0 Hp HG. exact (T_Unit _ _ _ _ HG Hp).
    - intros G s0 Hp HG. exact (T_Tt _ _ _ _ HG Hp).
    - intros G s0 Hp HG. exact (T_Bool _ _ _ _ HG Hp).
    - intros G s0 Hp HG. exact (T_True _ _ _ _ HG Hp).
    - intros G s0 Hp HG. exact (T_False _ _ _ _ HG Hp).
    - (* S_ElimVoid *) intros G C e TC D K s s0 Hp _ IHC HTC HD HK _ IHe HG.
      assert (Hr : TC ⇝* Pi Void (Srt s)).
      { eapply rt_trans; [exact HTC | apply red_pi; [exact (conv_fixed sg _ _ (red1_void sg) HD) | exact HK]]. }
      destruct (typed_red_type _ _ _ _ (IHC HG) Hr (fun s' E => ltac:(discriminate E))) as [HC _].
      exact (T_ElimVoid _ _ _ _ _ _ HC (IHe HG (or_intror (ex_intro _ s0 (T_Void _ _ _ _ HG Hp))))).
    - (* S_ElimUnit *) intros G C c u TC D K s s0 Hp _ IHC HTC HD HK _ IHc _ IHu HG.
      assert (Hr : TC ⇝* Pi Unit (Srt s)).
      { eapply rt_trans; [exact HTC | apply red_pi; [exact (conv_fixed sg _ _ (red1_unit sg) HD) | exact HK]]. }
      destruct (typed_red_type _ _ _ _ (IHC HG) Hr (fun s' E => ltac:(discriminate E))) as [HC _].
      pose proof (T_App _ _ _ _ _ _ _ HC (T_Tt _ _ _ _ HG Hp)) as HCt.
      exact (T_ElimUnit _ _ _ _ _ _ _ HC (IHc HG (or_intror (ex_intro _ s HCt)))
               (IHu HG (or_intror (ex_intro _ s0 (T_Unit _ _ _ _ HG Hp))))).
    - (* S_ElimBool *) intros G C t f b TC D K s s0 Hp _ IHC HTC HD HK _ IHt _ IHf _ IHb HG.
      assert (Hr : TC ⇝* Pi Bool (Srt s)).
      { eapply rt_trans; [exact HTC | apply red_pi; [exact (conv_fixed sg _ _ (red1_bool sg) HD) | exact HK]]. }
      destruct (typed_red_type _ _ _ _ (IHC HG) Hr (fun s' E => ltac:(discriminate E))) as [HC _].
      pose proof (T_App _ _ _ _ _ _ _ HC (T_True _ _ _ _ HG Hp)) as HCt.
      pose proof (T_App _ _ _ _ _ _ _ HC (T_False _ _ _ _ HG Hp)) as HCf.
      exact (T_ElimBool _ _ _ _ _ _ _ _ HC (IHt HG (or_intror (ex_intro _ s HCt)))
               (IHf HG (or_intror (ex_intro _ s HCf)))
               (IHb HG (or_intror (ex_intro _ s0 (T_Bool _ _ _ _ HG Hp))))).
    - (* S_Sigma *) intros G A B TA TB s1 s2 s3 _ IHA HA _ IHB HB Hr HG.
      pose proof (typed_red_srt _ _ _ _ (IHA HG) HA) as HA'.
      pose proof (typed_red_srt _ _ _ _ (IHB (W_Cons _ _ _ _ _ HA')) HB) as HB'.
      exact (T_Sigma _ _ _ _ _ _ _ _ HA' HB' Hr).
    - (* S_Fst *) intros G p P A B _ IHp HP HG.
      destruct (typed_red_type _ _ _ _ (IHp HG) HP (fun s E => ltac:(discriminate E))) as [Hp _].
      exact (T_Fst _ _ _ _ _ _ Hp).
    - (* S_Snd *) intros G p P A B _ IHp HP HG.
      destruct (typed_red_type _ _ _ _ (IHp HG) HP (fun s E => ltac:(discriminate E))) as [Hp _].
      exact (T_Snd _ _ _ _ _ _ Hp).
    - (* S_Const *) intros G g A Hd Hg HG. exact (T_Const _ _ _ _ _ HG Hd Hg).
    - (* S_Case *) intros G D s P x bs X d ps us Hdecl Hd Hel _ IHx HX Hlp Hlu _ IHP _ IHbs HG.
      destruct (typed_red_type _ _ _ _ (IHx HG) HX (apps_const_not_srt _ _)) as [Hx [sX HXt]].
      pose proof (sig_type_ind _ _ _ Hd) as Hty.
      destruct (const_type_typed S sg Hsig G _ _ HG Hty) as [s0 Hs0]. unfold ind_type in Hs0.
      assert (Hl : length (ind_params d ++ ind_indices d) = length (ps ++ us)) by (rewrite !length_app; lia).
      destruct (apps_inv S sg (ps ++ us) G (Const (Ind D)) _ _ _ _ Hl HXt (const_head S sg _ _ _ Hty) Hs0)
        as [Hargs _].
      destruct (proj1 (args_typed_app S sg ps G _ _ us (eq_sym Hlp)) Hargs) as [Hps _].
      assert (Hs : spec_sort S s = true) by (unfold allows_elimination in Hel; apply andb_prop in Hel as [Hs _]; exact Hs).
      destruct (motive_typed (Hfull Hdecl) Hdecl G D d ps s Hd HG Hlp Hps Hs) as [sm Hm].
      pose proof (IHP HG (or_intror (ex_intro _ sm Hm))) as HPt.
      pose proof (IHbs HG (fun c Hc => or_intror
        (branch_typed (Hfull Hdecl) Hdecl G D d ps P s c Hd (Hdist D d Hd) Hc Hlp Hps HPt Hs))) as Hbs.
      exact (T_Case _ _ _ _ _ _ _ _ _ _ _ Hdecl Hd Hel Hlp Hlu Hx HPt Hbs).
    - (* S_Fix *) intros G A k b T s D _ IHA HT Hsa Hne _ IHb Hgd HG.
      pose proof (typed_red_srt _ _ _ _ (IHA HG) HT) as HA.
      pose proof (typing_weaken1 S sg _ _ _ _ _ HA HA) as HA1.
      exact (T_Fix _ _ _ _ _ _ _ _ HA Hsa Hne (IHb (W_Cons _ _ _ _ _ HA) (or_intror (ex_intro _ s HA1))) Hgd).
    - (* C_Lam *) intros G b T A B HT _ IHb HG [[s0 ->] | [s0 HTt]].
      + exfalso. pose proof (red_srt_inv sg _ _ HT) as E. discriminate E.
      + pose proof (subject_red S sg Hsig _ _ _ _ HTt HT) as HPi.
        destruct (inv_pi S sg _ _ _ _ HPi) as (s1 & s2 & s3 & HA & HB & _ & _).
        pose proof (IHb (W_Cons _ _ _ _ _ HA) (or_intror (ex_intro _ s2 HB))) as Hb.
        exact (T_Conv _ _ _ _ _ _ _ (T_Lam _ _ _ _ _ _ _ Hb HPi) HTt (conv_sym _ _ (red_conv _ _ HT))).
    - (* C_Pair *) intros G a b T A B HT _ IHa _ IHb HG [[s0 ->] | [s0 HTt]].
      + exfalso. pose proof (red_srt_inv sg _ _ HT) as E. discriminate E.
      + pose proof (subject_red S sg Hsig _ _ _ _ HTt HT) as HS.
        destruct (inv_sigma S sg _ _ _ _ HS) as (s1 & s2 & s3 & HA & HB & _ & _).
        pose proof (IHa HG (or_intror (ex_intro _ s1 HA))) as Ha.
        pose proof (typing_subst1 S sg _ _ _ _ _ Ha HB) as HBa.
        pose proof (IHb HG (or_intror (ex_intro _ s2 HBa))) as Hb.
        exact (T_Conv _ _ _ _ _ _ _ (T_Pair _ _ _ _ _ _ _ _ HS Ha Hb) HTt (conv_sym _ _ (red_conv _ _ HT))).
    - (* C_Synth *) intros G t A B _ IHt Hc HG HB. exact (typed_conv_tyok _ _ _ _ (IHt HG) Hc HB).
    - (* CB_Nil *) intros. constructor.
    - (* CB_Cons *) intros G d ps P c cs b bs _ IHb _ IHbs HG Hok. constructor.
      + exact (IHb HG (Hok c (or_introl eq_refl))).
      + exact (IHbs HG (fun c' Hc' => Hok c' (or_intror Hc'))).
  Qed.

  Lemma bwf_wf : forall G, bwf_ctx S sg G -> wf G.
  Proof.
    induction 1 as [|G A T s _ IH HA HT]; [constructor | ].
    exact (W_Cons _ _ _ _ _ (typed_red_srt _ _ _ _ (proj1 bidir_sound _ _ _ HA IH) HT)).
  Qed.

  Corollary synth_sound : forall G t A, bwf_ctx S sg G -> synth S sg G t A -> wf G /\ typed G t A.
  Proof. intros G t A HG H. pose proof (bwf_wf _ HG) as HG'. exact (conj HG' (proj1 bidir_sound _ _ _ H HG')). Qed.

  (** Checking against an admissible expected type ([btype]). *)
  Corollary chk_sound : forall G t T, bwf_ctx S sg G -> btype S sg G T -> chk S sg G t T -> typed G t T.
  Proof.
    intros G t T HG HT H. pose proof (bwf_wf _ HG) as HG'.
    apply (proj1 (proj2 bidir_sound) _ _ _ H HG').
    destruct HT as [(s & -> & _) | (T' & s & HT & Hr)]; [left; exists s; reflexivity | right].
    exists s. exact (typed_red_srt _ _ _ _ (proj1 bidir_sound _ _ _ HT HG') Hr).
  Qed.
End Sound.
