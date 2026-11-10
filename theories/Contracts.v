(** * Contracts of the development

    The guarantees of the developments of lecture 6, stated as [Prop]
    definitions so that their exact form is kernel-checked independently
    of their proofs.  A contract followed by a theorem [..._holds] is
    proved; one without a theorem is an open obligation, stated precisely
    but not proved.  None of the proved contracts rests on an axiom:
    checks/Assumptions.v prints their assumptions, and [make assumptions]
    fails otherwise.

    The contracts of the kernel itself — substitution, normal order and
    the evaluator, conversion, checker soundness and the obligations about
    the declarative rules — are in PTS/Contracts.v, which depends on the
    kernel alone and is re-exported here.  The contracts below are about
    the empty signature [∅], in the notations of PTS.EmptySig.

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
  Typing Bidir Check CheckSound EmptySig Build.
From DepTypes.Configs Require Import Finite Predicative.
From DepTypes.SystemU Require Import Looping Encodings EncodingsCompute.
From DepTypes.PCFTranslation Require Import Translate TranslateSound Programs.
From DepTypes.MLTT Require Import Choose Eliminators.
From PCF Require Ty Syntax Context Checker OperationalSemantics.
From DepTypes.PTS Require Export Contracts.

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
