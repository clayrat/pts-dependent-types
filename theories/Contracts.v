(** * Contracts of the development

    The guarantees of the development, stated as [Prop] definitions so that
    their exact form is kernel-checked independently of their proofs.  A
    contract followed by a theorem [..._holds] is proved; one without a
    theorem is an open obligation, stated precisely but not proved.  None of
    the proved contracts rests on an axiom: checks/Assumptions.v prints
    their assumptions, and [make assumptions] fails otherwise.

    The proved contracts of the kernel hold for every signature:
    reduction, normal order, the evaluator and the checker take one, and
    its δ- and ι-contractions are among the steps.  They are stated with
    the signature as an explicit argument.  A signature guarantees only
    closedness, so the open obligations that relate the kernel to the
    declarative rules or to evaluation assume a type-correct one
    ([signature_typed] of PTS.Typing).  The contracts of the developments
    of lecture 6 are about the empty signature [∅], in the notations of
    PTS.EmptySig.

    The plan's readiness levels:
    1. an executable kernel with fuel, extraction, regressions and proved
       soundness of acceptance: reached;
    2. type preservation of the PCF translation and local computational
       properties of the encodings: reached;
    3. full adequacy of the translation and a decision procedure for each
       configuration: open.

    Trusted beyond the Rocq kernel: the extraction to OCaml, with natural
    numbers as machine integers and strings as OCaml strings
    (extraction/Extract.v); the OCaml printer and demos; and the pinned
    modules of strictness-pcf, whose own results are axiom-free.  The
    hand-written reference in reference/ is not covered by these proofs;
    differential tests compare it with the extract. *)

From Stdlib Require Import String List Relations Arith.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Spec Signature Reduction SubstLaws NormalOrder Eval
  Typing Bidir Check CheckSound EmptySig.
From DepTypes.Configs Require Import Finite Predicative.
From DepTypes.SystemU Require Import Looping Encodings EncodingsCompute.
From DepTypes.PCFTranslation Require Import Translate TranslateSound Programs.
From DepTypes.MLTT Require Import Choose Eliminators.
From PCF Require Ty Syntax Context Checker OperationalSemantics.

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

(** ** The looping combinator (stage 4) *)

Definition looping_typed_upto_3 : Prop :=
  forall n, n <= 3 -> system_u_minus ;; [] ⊢ looping n ⇑ looping_ty.

Theorem looping_typed_upto_3_holds : looping_typed_upto_3.
Proof. exact looping_typed. Qed.

Definition looping_unfolds_upto_2 : Prop :=
  forall n, n <= 2 -> looping_applied n ≡ App (Var 0) (looping_applied (S n)).

Theorem looping_unfolds_upto_2_holds : looping_unfolds_upto_2.
Proof. exact looping_unfolds. Qed.

(** ** Numerals (stage 5) *)

Definition omega_nat_typed_contract : Prop :=
  system_u_minus ;; [] ⊢ church omega_nat ⇑ church CNat.

Theorem omega_nat_typed_holds : omega_nat_typed_contract.
Proof. exact omega_nat_typed. Qed.

(** A numeric observation is the normal form of that numeral. *)
Definition observe_sound : Prop :=
  forall fuel t k, observe fuel t = ObsNumeral k -> t ⇝ₙ* church_nf k /\ nf ∅ (church_nf k).

Theorem observe_sound_holds : observe_sound.
Proof. exact observe_numeral_sound. Qed.

(** The encodings compute on every numeral, by reduction: [succ cₖ ⇝*
    cₖ₊₁], [pred cₖ₊₁ ⇝* cₖ], [pred c₀ ⇝* c₀], and the strict test
    tells zero from a successor. *)
Definition encodings_compute : Prop :=
  forall k,
    App (church csucc) (church (numeral k)) ⇝* church_nf (S k) /\
    App (church cpred) (church (numeral (S k))) ⇝* church_nf k /\
    App (church cpred) (church czero) ⇝* church_nf 0 /\
    App (church is_zero) (church (numeral 0)) ≡ church ctrue /\
    App (church is_zero) (church (numeral (S k))) ≡ church cfalse.

Theorem encodings_compute_holds : encodings_compute.
Proof. exact encodings_compute_proved. Qed.

(** ** The PCF translation (stage 6, level 2) *)

(** Type preservation: PCF's bidirectional judgment gives a translation
    checked against the translated type in the translated context. *)
Definition translation_preserves_typing_contract : Prop :=
  forall G t A, PCF.Checker.chk G t A ->
  exists u, translate G t A = Ok (tctx G, u) /\ system_u_minus ;; tctx G ⊢ u ⇓ translated_type A.

Theorem translation_preserves_typing_holds : translation_preserves_typing_contract.
Proof. exact translation_preserves_typing. Qed.

(** Whatever the translator outputs is typed. *)
Definition translate_sound_contract : Prop :=
  forall G t A G' u, translate G t A = Ok (G', u) ->
  G' = tctx G /\ bwf_ctx system_u_minus ∅ G' /\ btype system_u_minus ∅ G' (translated_type A) /\
  system_u_minus ;; G' ⊢ u ⇓ translated_type A.

Theorem translate_sound_holds : translate_sound_contract.
Proof. exact translate_sound. Qed.

(** The checked entry point: accepted by the U⁻ checker, hence typed by
    its soundness, independently of type preservation. *)
Definition translate_checked_contract : Prop :=
  forall fuel G t A G' u, translate_checked fuel G t A = Ok (G', u) ->
  system_u_minus ;; G' ⊢ u ⇓ translated_type A.

Theorem translate_checked_holds : translate_checked_contract.
Proof.
  intros fuel G t A G' u H. exact (proj2 (proj2 (proj2 (translate_checked_sound _ _ _ _ _ _ H)))).
Qed.

(** The source side of the regression programs: the expected number, or
    divergence in PCF. *)
Definition pcf_programs_source : Prop :=
  Forall (fun c => source_behaviour (snd c) (snd (fst c))) pcf_cases.

Theorem pcf_programs_source_holds : pcf_programs_source.
Proof. exact pcf_cases_source. Qed.

(** ** The minimal MLTT (stage 7) *)

Definition choose_contract : Prop :=
  predicative ;; in_ctx types_ctx ⊢ term_in types_ctx choose ⇓ term_in types_ctx choose_ty /\
  predicative ;; in_ctx args_ctx ⊢ term_in args_ctx (choose_at NTrue) ⇓ term_in args_ctx (NVar "A") /\
  predicative ;; in_ctx args_ctx ⊢ term_in args_ctx (choose_at NFalse) ⇓ term_in args_ctx (NVar "B").

Theorem choose_holds : choose_contract.
Proof. split; [exact choose_typed | split; [exact choose_true_typed | exact choose_false_typed]]. Qed.

Definition eliminators_contract : Prop :=
  predicative ;; in_ctx void_ctx ⊢ term_in void_ctx void_elim ⇓ term_in void_ctx (NVar "A") /\
  predicative ;; [] ⊢ build [] (unit_elim NTt) ⇓ Bool.

Theorem eliminators_holds : eliminators_contract.
Proof. split; [exact void_elim_typed | exact unit_elim_typed]. Qed.

(** ** Open obligations

    Stated, not proved.  Each is a separate task, and none is a condition
    of the executable kernel of level 1. *)

(** The looping combinator: every [Lₙ] is typed, and every unfolding holds
    (Lemma 3 of Geuvers–Verkoelen). *)
Definition looping_typed_all : Prop :=
  forall n, system_u_minus ;; [] ⊢ looping n ⇑ looping_ty.

Definition looping_unfolds_all : Prop :=
  forall n, looping_applied n ≡ App (Var 0) (looping_applied (S n)).

(** The typing half of the correctness of substitution, for the
    declarative rules: weakening by a well-sorted type, and the
    substitution lemma. *)
Definition typing_weakening : Prop :=
  forall S sg G t A B s, has_type S sg G t A -> has_type S sg G B (Srt s) ->
  has_type S sg (B :: G) (lift 1 t) (lift 1 A).

Definition typing_substitution : Prop :=
  forall S sg G u A t B, has_type S sg G u A -> has_type S sg (A :: G) t B ->
  has_type S sg G (subst1 t u) (subst1 B u).

(** Metatheory of reduction: confluence, and the injectivity of Π that
    follows from it. *)
Definition confluence : Prop :=
  forall sg t u v, red sg t u -> red sg t v -> exists w, red sg u w /\ red sg v w.

Definition pi_injective : Prop :=
  forall sg A B A' B', conv sg (Pi A B) (Pi A' B') -> conv sg A A' /\ conv sg B B'.

(** Progress for normal order: a well-typed term never gets stuck, in a
    type-correct signature.  An ill-typed δ-body breaks it: with
    [f := tt] at [Bool → Bool], [f true] synthesizes [Bool] and reaches
    the stuck [tt true] (MLTT/Constants.v). *)
Definition progress : Prop :=
  forall S sg G t A, signature_typed S sg -> bwf_ctx S sg G -> synth S sg G t A -> ~ stuck sg t.

(** The annotated kernel is sound for the declarative PTS rules, in a
    type-correct signature.  The checker trusts the types of constants:
    with [c : (tt → tt) → Bool] it accepts [c (λx. x)], which the
    declarative rules reject, since [T_Lam] needs [tt → tt] to be a type
    (MLTT/Constants.v). *)
Definition bidir_declarative_sound : Prop :=
  forall S sg G t A, signature_typed S sg -> bwf_ctx S sg G -> synth S sg G t A ->
  wf_ctx S sg G /\ has_type S sg G t A.

(** The other answers of [convert]: [ConvDifferent] really means that the
    terms are not convertible, and convertible terms with normal forms are
    found equal with enough fuel.  Both rest on confluence. *)
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

(** The normalization premise for the configurations of lecture 6: for
    U⁻ through the embedding of its type level into λ2 (Geuvers–Verkoelen,
    JFP, Corollary 3.1), for the predicative hierarchy by normalization of
    MLTT. *)
Definition normalizing_u_minus : Prop := normalizing_types system_u_minus ∅.
Definition normalizing_predicative : Prop := normalizing_types predicative ∅.

(** Adequacy of the PCF translation, with the observation of a closed
    program of type ℕ: PCF yields [k] if and only if the translation
    reaches the numeral [k] by normal order. *)
Definition translation_adequate : Prop :=
  forall t k, PCF.Checker.chk [] t PCF.Ty.tnat ->
  (exists fuel, PCF.OperationalSemantics.evalFuel fuel t = PCF.OperationalSemantics.Value (PCF.Syntax.tnum k))
  <-> (exists u, translate_program t = Ok u /\ u ⇝ₙ* church_nf k).
