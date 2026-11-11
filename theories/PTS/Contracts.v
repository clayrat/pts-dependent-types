(** * Contracts of the kernel

    The guarantees of the kernel, stated as [Prop] definitions so that
    their exact form is kernel-checked independently of their proofs.  A
    contract followed by a theorem [..._holds] is proved; one without a
    theorem is an open obligation, stated precisely but not proved.  None of
    the proved contracts rests on an axiom: checks/Assumptions.v prints
    their assumptions, and [make assumptions] fails otherwise.

    The proved contracts hold for every specification and every
    signature: reduction, normal order, the evaluator and the checker take
    one, and its δ- and ι-contractions are among the steps.  They are
    stated with the signature as an explicit argument.  A signature
    guarantees only closedness, so validity, subject reduction and the
    open obligations that relate the kernel to the declarative rules or
    to evaluation assume a type-correct one ([signature_typed] of
    PTS.Typing).

    This file depends on the kernel alone, so that the projects built on
    it can import its contracts without the PCF translation and
    strictness-pcf.  The contracts of the developments of lecture 6 (the
    looping combinator, numerals, the translation, the minimal MLTT) are
    in theories/Contracts.v, which re-exports this file. *)

From Stdlib Require Import List Relations Arith.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Spec Signature Reduction SubstLaws Confluence NormalOrder Eval
  EvalSrc Guard GuardSound Typing TypingSubst Inversion SubjectRed Bidir BidirSound Check CheckSound.

(** ** Substitution (level 1) *)

(** The syntactic correctness of substitution: lifting then substituting
    is the identity, substitution commutes with single substitution, and
    substitutions compose. *)
Definition substitution_laws : Prop :=
  (forall t u, subst1 (lift 1 t) u = t) /\
  (forall sb b u, subst sb (subst1 b u) = subst1 (subst (up_sub sb) b) (subst sb u)) /\
  (forall sb sb' t, subst sb (subst sb' t) = subst (fun n => subst sb (sb' n)) t) /\
  (forall t, subst Var t = t).

Theorem substitution_laws_holds : substitution_laws.
Proof. split; [exact subst1_lift | split; [exact subst_subst1 | split; [intros sb sb' t; apply subst_subst | exact subst_var]]]. Qed.

(** Reduction and conversion are stable under substitution, and reducing
    the argument of a substitution reduces the result, in every
    signature: δ unfolds closed bodies, and ι commutes with substitution. *)
Definition reduction_stable_under_substitution : Prop :=
  forall sg,
  (forall sb t u, red1 sg t u -> red1 sg (subst sb t) (subst sb u)) /\
  (forall sb t u, conv sg t u -> conv sg (subst sb t) (subst sb u)) /\
  (forall b u u', red sg u u' -> red sg (subst1 b u) (subst1 b u')).

Theorem reduction_stable_under_substitution_holds : reduction_stable_under_substitution.
Proof.
  intros sg.
  split; [intros sb t u H; exact (red1_subst t u H sb) | split; [exact conv_subst | exact red_subst1_arg]].
Qed.

(** ** Normal order and the evaluator (level 1) *)

(** The executable step is exactly the normal-order relation. *)
Definition classify_correct : Prop :=
  forall sg t u, classify sg t = Steps u <-> nstep sg t u.

Theorem classify_correct_holds : classify_correct.
Proof.
  intros sg t u. split.
  - intros H. pose proof (classify_spec (sg := sg) t) as Hs. rewrite H in Hs. exact Hs.
  - apply classify_complete.
Qed.

Definition normal_order_deterministic : Prop :=
  forall sg t u v, nstep sg t u -> nstep sg t v -> u = v.

Theorem normal_order_deterministic_holds : normal_order_deterministic.
Proof. intros sg. exact nstep_det. Qed.

(** A normal form found by [normalize] is reached by normal order. *)
Definition normalize_sound : Prop :=
  forall sg fuel t v, normalize sg fuel t = NormalForm v ->
  clos_refl_trans term (nstep sg) t v /\ nf sg v.

Theorem normalize_sound_holds : normalize_sound.
Proof.
  intros sg fuel t v H. pose proof (normalize_spec (sg := sg) fuel t) as [Hr Hs].
  rewrite H in Hr, Hs. split; assumption.
Qed.

(** ... and every normal form reached by normal order is found, with
    enough fuel, and more fuel does not change it. *)
Definition normalize_complete_contract : Prop :=
  forall sg t v, clos_refl_trans term (nstep sg) t v -> nf sg v ->
  exists n, forall m, n <= m -> normalize sg m t = NormalForm v.

Theorem normalize_complete_holds : normalize_complete_contract.
Proof. intros sg. exact normalize_complete. Qed.

Definition whnf_sound : Prop :=
  forall sg fuel t v, whnf sg fuel t = HeadForm v -> clos_refl_trans term (nstep sg) t v.

Theorem whnf_sound_holds : whnf_sound.
Proof. intros sg. exact whnf_reduces. Qed.

(** An equality reported by [convert] is conversion. *)
Definition convert_sound : Prop :=
  forall sg fuel t u v, convert sg fuel t u = ConvEqual v -> conv sg t u.

Theorem convert_sound_holds : convert_sound.
Proof. intros sg. exact convert_equal_sound. Qed.

(** A stuck answer of [convert] is a stuck normalization of one of two
    syntactically different terms. *)
Definition convert_stuck_contract : Prop :=
  forall sg fuel t u, convert sg fuel t u = ConvStuck ->
  t <> u /\ exists v, normalize sg fuel t = StuckTerm v \/ normalize sg fuel u = StuckTerm v.

Theorem convert_stuck_holds : convert_stuck_contract.
Proof. intros sg. exact convert_stuck_sound. Qed.

(** ** The checker (level 1) *)

(** An accepted run of either entry point, for every specification, every
    signature and any fuel, gives a well-formed context and the judgment
    of the annotated kernel. *)
Definition checker_sound : Prop :=
  (forall S sg fuel G t A, snd (run_infer S sg fuel G t) = Accepted A ->
     bwf_ctx S sg G /\ synth S sg G t A) /\
  (forall S sg fuel G t T u, snd (run_check S sg fuel G t T) = Accepted u ->
     bwf_ctx S sg G /\ btype S sg G T /\ chk S sg G t T).

Theorem checker_sound_holds : checker_sound.
Proof. split; [exact run_infer_sound | exact run_check_sound]. Qed.

(** An accepted [infer_spine], the types that erasure asks for in a
    context taken as checked, has one type per prefix of the application,
    outermost first ([spine_prefixes]: never empty, one more than the
    arguments), each the judgment of the annotated kernel for its prefix. *)
Definition infer_spine_contract : Prop :=
  forall S sg fuel G t Ts, snd (run_answer (infer_spine S sg fuel G t)) = Accepted Ts ->
  Forall2 (synth S sg G) (spine_prefixes t) Ts.

Theorem infer_spine_holds : infer_spine_contract.
Proof.
  intros S sg fuel G t Ts H. apply run_answer_accepted in H as [log H].
  exact (infer_spine_typed S sg fuel t G nil log Ts H).
Qed.

(** A match the kernel accepts eliminates into a sort that the category
    of its type allows: the one check [allows_elimination] that the
    registration of eliminator instances uses too. *)
Definition match_respects_elimination : Prop :=
  forall S sg G D s P x bs A, synth S sg G (Case D s P x bs) A ->
  exists d, sig_ind sg D = Some d /\ allows_elimination S (ind_elim d) s = true.

Theorem match_respects_elimination_holds : match_respects_elimination.
Proof. intros S sg G D s P x bs A H. inversion H; subst. eexists; split; eassumption. Qed.

(** ** The guard of fix (level 1) *)

(** The executable guard implies the rules of the judgment [Guarded]: a
    body accepted by [guard_fix] starts with its [k + 1] λ and is guarded
    after them. *)
Definition guard_sound_contract : Prop :=
  forall sg k b, guard_fix sg k b = Ok tt -> fix_guarded sg k b.

Theorem guard_sound_holds : guard_sound_contract.
Proof. intros sg k b. exact (guard_fix_sound sg k b). Qed.

(** The marks mean what they say, for the strict subterm relation of the
    descriptions, defined without them: a substitution of the variables
    respects the marks for the value [v] of the structural argument at
    the entry of the body, under every binder, and in the branch a
    guarded match on a structural origin takes once its scrutinee
    reduces to a constructor; and the structural argument of a call the
    guard accepts is then a strict subterm of [v]. *)
Definition guard_invariants : Prop :=
  forall sg,
  (forall k σ v, σ 0 = v -> respects sg (entry_marks k) σ v) /\
  (forall ms σ v u, respects sg ms σ v -> respects sg (Large :: ms) (scons u σ) v) /\
  (forall k ms σ v D s P x bs w d i cd xs b body,
     Guarded sg k ms (Case D s P x bs) -> respects sg ms σ v -> origin ms x = true ->
     red sg (subst σ x) w -> sig_ind sg D = Some d -> ctor_view D d w = Some (i, cd, xs) ->
     nth_error bs i = Some b -> b = lams (length (ctor_fields cd)) body ->
     Guarded sg k (rev (map field_mark (ctor_fields cd)) ++ ms) body /\
     respects sg (rev (map field_mark (ctor_fields cd)) ++ ms) (with_fields xs σ) v) /\
  (forall ms σ v a, respects sg ms σ v -> sub_arg ms a = true -> strict_sub sg (subst σ a) v).

Theorem guard_invariants_holds : guard_invariants.
Proof.
  intros sg. split; [exact (respects_entry sg) | split; [exact (respects_binder sg) | split]].
  - exact (case_step sg).
  - exact (call_decreases sg).
Qed.

(** ** Call-by-value evaluation (level 1) *)

(** A value found by the evaluator of source programs is a reduct. *)
Definition eval_src_sound : Prop :=
  forall sg fuel t v, eval_src sg fuel t = CbvValue v -> red sg t v.

Theorem eval_src_sound_holds : eval_src_sound.
Proof. intros sg. exact eval_src_reduces. Qed.

(** ** Confluence (level 1)

    Reduction is confluent for every signature, by parallel reduction
    and complete development (PTS.Confluence); the injectivity of Π
    follows, since a Π reduces only to a Π and convertible terms have a
    common reduct. *)
Definition confluence : Prop :=
  forall sg t u v, red sg t u -> red sg t v -> exists w, red sg u w /\ red sg v w.

Theorem confluence_holds : confluence.
Proof. intros sg. exact (red_confluent sg). Qed.

Definition pi_injective : Prop :=
  forall sg A B A' B', conv sg (Pi A B) (Pi A' B') -> conv sg A A' /\ conv sg B B'.

Theorem pi_injective_holds : pi_injective.
Proof. intros sg. exact (pi_inj sg). Qed.

(** ** Weakening and substitution for the declarative rules (level 1)

    The typing half of the correctness of substitution, for every
    specification and signature (PTS.TypingSubst): weakening by a
    well-sorted type, and the substitution lemma.  Both are instances of
    the stability of typing under renamings and substitutions that keep
    the types of the variables.  They rest on the closedness of the
    signature, which gives the types of constants and the types of the
    branches of a match, and on the marks of the guard, which give every
    variable outside a [fix] the mark [Large]. *)
Definition typing_weakening : Prop :=
  forall S sg G t A B s, has_type S sg G t A -> has_type S sg G B (Srt s) ->
  has_type S sg (B :: G) (lift 1 t) (lift 1 A).

Theorem typing_weakening_holds : typing_weakening.
Proof. intros S sg. exact (typing_weaken1 S sg). Qed.

Definition typing_substitution : Prop :=
  forall S sg G u A t B, has_type S sg G u A -> has_type S sg (A :: G) t B ->
  has_type S sg G (subst1 t u) (subst1 B u).

Theorem typing_substitution_holds : typing_substitution.
Proof. intros S sg. exact (typing_subst1 S sg). Qed.

(** ** Validity and subject reduction (level 1)

    In a type-correct signature, the type of a typed term is a sort or a
    type of some sort (PTS.Inversion), and a reduct of a term has every
    type of the term, after any number of steps in any position, under
    binders and in the body of a [fix] included (PTS.SubjectRed).  Both
    rest on weakening and substitution, on the inversion of the rules,
    and on confluence through the injectivity of Π, of Σ and of the
    spines of a family, which matches the indices of a constructor with
    those of the scrutinee of a match.  Subject reduction rests also on
    context conversion, for a step in the domain of a binder, and on the
    stability of the guard of [fix] under reduction (PTS.GuardRed).  Of
    [signature_typed] they use the three conditions: the types of the
    constants are types, the δ-bodies have them, and the ι of the
    eliminator instances keeps the type of the redex. *)
Definition typing_validity : Prop :=
  forall S sg G t T, signature_typed S sg -> has_type S sg G t T ->
  (exists s, T = Srt s) \/ (exists s, has_type S sg G T (Srt s)).

Theorem typing_validity_holds : typing_validity.
Proof. intros S sg G t T Hsig H. exact (validity S sg Hsig G t T H). Qed.

Definition subject_reduction : Prop :=
  forall S sg G t u T, signature_typed S sg -> has_type S sg G t T -> red sg t u ->
  has_type S sg G u T.

Theorem subject_reduction_holds : subject_reduction.
Proof. intros S sg G t u T Hsig H Hr. exact (subject_red S sg Hsig G t u T H Hr). Qed.

(** The annotated kernel is sound for the declarative PTS rules, in a
    type-correct signature.  The checker trusts the types of constants:
    with [c : (tt → tt) → Bool] it accepts [c (λx. x)], which the
    declarative rules reject, since [T_Lam] needs [tt → tt] to be a type
    (MLTT/Constants.v).  A [match] is checked against types the kernel
    builds from a description without checking them, so two more
    premises: when constants are on, the table is full, and the
    constructors of a type have distinct names.  Without the first, a
    table with a top sort □ accepts the motive [λ_. ∗ ⇓ Π_:D. □], whose
    type has no type; without the second, the branch of a second
    constructor named [c] is checked against fields that nothing types
    (PTS.BidirSound).  The predicative hierarchies are full
    (Configs.Predicative), and the registration of a declaration refuses
    two constructors with one name. *)
Definition bidir_declarative_sound : Prop :=
  forall S sg G t A, signature_typed S sg -> (spec_decls S = true -> full_table S) ->
  ctors_distinct sg -> bwf_ctx S sg G -> synth S sg G t A ->
  wf_ctx S sg G /\ has_type S sg G t A.

Theorem bidir_declarative_sound_holds : bidir_declarative_sound.
Proof. intros S sg G t A Hsig Hfull Hdist HG H. exact (synth_sound S sg Hsig Hfull Hdist G t A HG H). Qed.

(** ** Open obligations

    Stated, not proved.  Each is a separate task, and none is a condition
    of the executable kernel of level 1. *)

(** Progress for normal order: a well-typed term never gets stuck, in a
    type-correct signature.  An ill-typed δ-body breaks it: with
    [f := tt] at [Bool → Bool], [f true] synthesizes [Bool] and reaches
    the stuck [tt true] (MLTT/Constants.v). *)
Definition progress : Prop :=
  forall S sg G t A, signature_typed S sg -> bwf_ctx S sg G -> synth S sg G t A -> ~ stuck sg t.

(** Progress for call-by-value evaluation: a well-typed closed program
    of a type-correct signature does not get stuck, whatever the budget.
    That it reaches a value needs normalization, below. *)
Definition eval_src_progress : Prop :=
  forall S sg fuel t A, signature_typed S sg -> synth S sg nil t A ->
  forall u, eval_src sg fuel t <> CbvStuck u.

(** The strict subterm relation is well founded on the well-typed
    closed terms of a type-correct signature, so that the invariants of
    the guard make every guarded fixpoint terminate.  It rests on the
    normalization of the theory. *)
Definition strict_sub_well_founded : Prop :=
  forall S sg, signature_typed S sg -> forall v A, synth S sg nil v A ->
  Acc (fun u w => strict_sub sg u w) v.

(** The other answers of [convert]: [ConvDifferent] really means that the
    terms are not convertible, and convertible terms with normal forms are
    found equal with enough fuel.  Both rest on confluence, proved
    above. *)
Definition convert_different_sound : Prop :=
  forall sg fuel t u, convert sg fuel t u = ConvDifferent -> ~ conv sg t u.

Definition convert_complete : Prop :=
  forall sg t u v w, clos_refl_trans term (nstep sg) t v -> nf sg v ->
  clos_refl_trans term (nstep sg) u w -> nf sg w -> conv sg t u ->
  exists n, forall m, n <= m -> exists c, convert sg m t u = ConvEqual c.

(** Completeness of the checker, for both entry points, up to conversion
    and with enough fuel, under the normalization premise of PTS.Bidir. *)
Definition checker_complete : Prop :=
  forall S sg, normalizing_types S sg ->
  (forall G t A, bwf_ctx S sg G -> synth S sg G t A ->
     exists n, forall m, n <= m ->
     exists A', snd (run_infer S sg m G t) = Accepted A' /\ conv sg A' A) /\
  (forall G t T, bwf_ctx S sg G -> btype S sg G T -> chk S sg G t T ->
     exists n, forall m, n <= m -> snd (run_check S sg m G t T) = Accepted tt).
