(** * Regression tests for the base definitions

    Substitution under several binders without capture, open terms, the
    sort tables of U⁻ and of the predicative hierarchy, normal order, and
    the gap between declarative typing and the annotated kernel. *)

From Stdlib Require Import List Relations.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Spec Reduction NormalOrder Eval Typing Bidir Check Named.
From DepTypes.Configs Require Import Finite Predicative.
From DepTypes Require Import Examples.

(** ** Substitution *)

(** [(λ. λ. 2 1 0)[u/0]] with an open [u = Var 5]: the free index 0
    becomes [u] lifted past both binders, the bound indices stay. *)
Example subst_under_two_binders :
  subst1 (Lam (Lam (App (App (Var 2) (Var 1)) (Var 0)))) (Var 5)
  = Lam (Lam (App (App (Var 7) (Var 1)) (Var 0))).
Proof. reflexivity. Qed.

(** Substituting a term with a free variable under a binder does not
    capture it: [(λ. 1)[0/0]] is [λ. 1], not the identity [λ. 0]. *)
Example subst_no_capture :
  subst1 (Lam (Var 1)) (Var 0) = Lam (Var 1).
Proof. reflexivity. Qed.

(** The other free variables are decremented. *)
Example subst_decrements :
  subst1 (App (Var 0) (Var 3)) (Srt Star) = App (Srt Star) (Var 2).
Proof. reflexivity. Qed.

(** Substitution into the codomain of a Π: [(Πx:0. 1)[Bool/0]]. *)
Example subst_pi :
  subst1 (Pi (Var 0) (Var 1)) Bool = Pi Bool Bool.
Proof. reflexivity. Qed.

Example arrow_lifts :
  arrow (Var 0) (Var 0) = Pi (Var 0) (Var 1).
Proof. reflexivity. Qed.

Example lookup_lifts :
  lookup [Var 0; Srt Star] 0 = Some (Var 1).
Proof. reflexivity. Qed.

(** ** U⁻: all allowed and forbidden pairs *)

Definition named_sorts : list sort := [Star; Box; Tri].

Example u_minus_rules :
  map (fun s1 => map (spec_rule system_u_minus s1) named_sorts) named_sorts
  = [ [Some Star; None;     None];     (* (∗,∗) *)
      [Some Star; Some Box; None];     (* (□,∗), (□,□) *)
      [None;      Some Box; None] ].   (* (△,□) *)
Proof. reflexivity. Qed.

Example u_rules :
  map (fun s1 => map (spec_rule system_u s1) named_sorts) named_sorts
  = [ [Some Star; None;     None];
      [Some Star; Some Box; None];
      [Some Star; Some Box; None] ].   (* (△,∗) added *)
Proof. reflexivity. Qed.

Example u_minus_axioms :
  map (spec_axiom system_u_minus) named_sorts = [Some Box; Some Tri; None].
Proof. reflexivity. Qed.

Example u_minus_no_univ : spec_sort system_u_minus (Univ 0) = false.
Proof. reflexivity. Qed.

Example u_minus_no_prims : spec_prim system_u_minus = None.
Proof. reflexivity. Qed.

(** ** The predicative hierarchy *)

Example univ_axiom_3 : spec_axiom predicative (Univ 3) = Some (Univ 4).
Proof. reflexivity. Qed.

Example univ_rule_max : spec_rule predicative (Univ 1) (Univ 0) = Some (Univ 1).
Proof. reflexivity. Qed.

Example univ_rule_max' : spec_rule predicative (Univ 0) (Univ 2) = Some (Univ 2).
Proof. reflexivity. Qed.

Example predicative_no_star : spec_sort predicative Star = false.
Proof. reflexivity. Qed.

(** Quantifying over Type_0 lifts the product to Type_1: the rule (□,∗)
    of U⁻ becomes (Type_1, Type_0, Type_1) after renaming. *)
Example renamed_box_star :
  spec_rule pure_predicative (u_to_univ Box) (u_to_univ Star) = Some (Univ 1).
Proof. reflexivity. Qed.

Example map_sorts_pi :
  map_sorts u_to_univ (Pi (Srt Star) (arrow (Var 0) (Var 0)))
  = Pi (Srt (Univ 0)) (Pi (Var 0) (Var 1)).
Proof. reflexivity. Qed.

(** ** Normal order *)

(** An unused argument is dropped without being reduced: in
    [(λ. 0') ((λ. 0) Tt)], where [0'] is the outer variable [Var 1] seen
    from under the binder, normal order contracts the outer redex first. *)
Example nstep_drops_argument :
  App (Lam (Var 1)) (App (Lam (Var 0)) Tt) ⇝ₙ Var 0.
Proof. apply N_Beta. Qed.

(** Under a neutral head the argument is reduced, but only after the
    head. *)
Example nstep_neutral_head :
  App (Var 0) (Ann Tt Unit) ⇝ₙ App (Var 0) Tt.
Proof. apply N_AppArg; constructor. Qed.

(** Without η, [λx. f x] is a normal form distinct from [f]. *)
Example eta_not_reduced : nf (Lam (App (Var 1) (Var 0))).
Proof. repeat constructor. Qed.

(** Without a normal-order step a raw term need not be normal:
    [Tt] applied to [Ann Tt Unit] has a [red1]-redex in the argument, but
    [Tt] is neither a λ nor neutral, so normal order is stuck. *)
Example stuck_app_tt :
  stuck (App Tt (Ann Tt Unit)) /\ App Tt (Ann Tt Unit) ⇝ App Tt Tt.
Proof.
  split; [split | apply R_AppArg, R_Ann].
  - intros H. inversion H; subst.
    match goal with Hn : ne (App _ _) |- _ => inversion Hn; subst end.
    match goal with Hn : ne Tt |- _ => inversion Hn end.
  - intros u H. inversion H; subst;
      match goal with
      | Hs : Tt ⇝ₙ _ |- _ => inversion Hs
      | Hn : ne Tt |- _ => inversion Hn
      end.
Qed.

(** ** Bounded evaluation and conversion *)

Example eval_under_binder :
  normalize 1 (Lam (Ann (Var 0) Bool)) = NormalForm (Lam (Var 0)).
Proof. reflexivity. Qed.

Example eval_open_neutral :
  normalize 1 (App (Var 0) (Ann Tt Unit)) =
  NormalForm (App (Var 0) Tt).
Proof. reflexivity. Qed.

Example eval_discards_argument :
  normalize 1 (App (Lam (Var 1)) (Ann Tt Unit)) = NormalForm (Var 0).
Proof. reflexivity. Qed.

Example eval_annotation_before_beta :
  normalize 2 (App (Ann (Lam (Var 0)) (Pi Unit Unit)) Tt) = NormalForm Tt.
Proof. reflexivity. Qed.

Example eval_bool_selected_branch :
  normalize 1 (ElimBool (Lam Bool) BTrue BFalse BFalse) = NormalForm BFalse.
Proof. reflexivity. Qed.

Example eval_stuck_raw_term :
  normalize 1 (App Tt (Ann Tt Unit)) = StuckTerm (App Tt (Ann Tt Unit)).
Proof. reflexivity. Qed.

Example eval_fuel_boundary :
  normalize 0 (App (Lam (Var 0)) Tt) = OutOfFuel (App (Lam (Var 0)) Tt) /\
  normalize 0 Tt = NormalForm Tt.
Proof. split; reflexivity. Qed.

Example eval_trace_includes_endpoints :
  normalize_trace 2 (App (Ann (Lam (Var 0)) (Pi Unit Unit)) Tt) =
    ([App (Ann (Lam (Var 0)) (Pi Unit Unit)) Tt;
      App (Lam (Var 0)) Tt; Tt], NormalForm Tt).
Proof. reflexivity. Qed.

Example whnf_ignores_argument :
  whnf 0 (App (Var 0) (Ann Tt Unit)) =
    HeadForm (App (Var 0) (Ann Tt Unit)).
Proof. reflexivity. Qed.

(** The scrutinee of [ElimVoid] is in head position, as for the other
    eliminators. *)
Example whnf_elim_void_scrutinee :
  whnf 1 (ElimVoid Void (Ann (Var 0) Void)) = HeadForm (ElimVoid Void (Var 0)).
Proof. reflexivity. Qed.

Example conv_has_no_eta :
  convert 0 (Var 0) (Lam (App (Var 1) (Var 0))) = ConvDifferent.
Proof. reflexivity. Qed.

Example conv_timeout_and_stuck :
  convert 0 (App (Lam (Var 0)) Tt) Tt = ConvOutOfFuel /\
  convert 1 (App Tt (Ann Tt Unit)) Tt = ConvStuck.
Proof. split; reflexivity. Qed.

(** ** Declarative typing versus the annotated kernel *)

(** The unannotated redex [(λx. x) true] is typable declaratively... *)
Example beta_redex_typable :
  predicative ;; [] ⊢ App (Lam (Var 0)) BTrue ∈ Bool.
Proof.
  assert (Hctx : wf_ctx predicative [Bool]).
  { eapply W_Cons with (s := Univ 0). eapply T_Bool; [constructor | reflexivity]. }
  change (predicative ;; [] ⊢ App (Lam (Var 0)) BTrue ∈ subst1 Bool BTrue).
  eapply T_App with (A := Bool).
  - eapply T_Lam with (s := Univ 0).
    + apply T_Var; [exact Hctx | reflexivity].
    + eapply T_Pi with (s1 := Univ 0) (s2 := Univ 0); [ | | reflexivity ];
        eapply T_Bool; eauto using W_Nil.
  - eapply T_True; [constructor | reflexivity].
Qed.

(** ...but does not synthesize: a λ only checks. *)
Example beta_redex_not_synth : forall A,
  ~ predicative ;; [] ⊢ App (Lam (Var 0)) BTrue ⇑ A.
Proof.
  intros A H. inversion H; subst.
  match goal with Hf : synth _ _ (Lam _) _ |- _ => inversion Hf end.
Qed.

(** With the annotation it does. *)
Example beta_redex_ann_synth :
  predicative ;; [] ⊢ App (Ann (Lam (Var 0)) (Pi Bool Bool)) BTrue ⇑ Bool.
Proof.
  change (predicative ;; [] ⊢ App (Ann (Lam (Var 0)) (Pi Bool Bool)) BTrue
            ⇑ subst1 Bool BTrue).
  eapply S_App.
  - eapply S_Ann.
    + eapply S_Pi; try (eapply S_Bool; reflexivity); try apply rt_refl; reflexivity.
    + apply rt_refl.
    + eapply C_Lam; [apply rt_refl | ].
      eapply C_Synth; [apply S_Var; reflexivity | apply conv_refl].
  - apply rt_refl.
  - eapply C_Synth; [eapply S_True; reflexivity | apply conv_refl].
Qed.

(** Synthesis is not functional.  In λ∗, with
    [f : Πx:∗. (∗ : ∗)] in the context, the type of [f] unfolds to a Π
    either as it is or after erasing the annotation in the codomain, so
    [f ∗] synthesizes both [Ann (Srt Star) (Srt Star)] and [Srt Star].
    They are convertible but syntactically different. *)
Definition ann_codomain_ctx : ctx := [Pi (Srt Star) (Ann (Srt Star) (Srt Star))].

Lemma ann_codomain_arg : lambda_star ;; ann_codomain_ctx ⊢ Srt Star ⇓ Srt Star.
Proof. eapply C_Synth; [apply S_Sort; reflexivity | apply conv_refl]. Qed.

Example synth_ann_codomain :
  lambda_star ;; ann_codomain_ctx ⊢ App (Var 0) (Srt Star) ⇑ Ann (Srt Star) (Srt Star).
Proof.
  change (Ann (Srt Star) (Srt Star)) with (subst1 (Ann (Srt Star) (Srt Star)) (Srt Star)).
  eapply S_App; [apply S_Var; reflexivity | apply rt_refl | apply ann_codomain_arg].
Qed.

Example synth_erased_codomain :
  lambda_star ;; ann_codomain_ctx ⊢ App (Var 0) (Srt Star) ⇑ Srt Star.
Proof.
  change (Srt Star) with (subst1 (Srt Star) (Srt Star)) at 2.
  eapply S_App;
    [ apply S_Var; reflexivity
    | apply rt_step, R_PiCod, R_Ann
    | apply ann_codomain_arg ].
Qed.

Example synth_types_convertible :
  Ann (Srt Star) (Srt Star) ≡ Srt Star /\ Ann (Srt Star) (Srt Star) <> Srt Star.
Proof. split; [apply rst_step, R_Ann | discriminate]. Qed.

(** ** Admissible expected types *)

(** Erasing the annotation, [true] checks against [Ann Bool (Var 0)] in
    the empty context, although [Var 0] is unbound... *)
Example chk_unbound_annotation :
  predicative ;; [] ⊢ BTrue ⇓ Ann Bool (Var 0).
Proof.
  eapply C_Synth; [eapply S_True; reflexivity | apply rst_sym, rst_step, R_Ann].
Qed.

(** ...but that expected type is not admissible. *)
Example unbound_annotation_not_btype :
  ~ btype predicative [] (Ann Bool (Var 0)).
Proof.
  intros [(s & Hs & _) | (T & s & H & _)]; [discriminate | ].
  inversion H; subst.
  match goal with Hv : synth _ _ (Var 0) _ |- _ => inversion Hv; subst end.
  discriminate.
Qed.

(** The top sort △ of U⁻ has no type, yet [□ ⇓ △] holds, and △ is an
    admissible expected type. *)
Example chk_box_tri : system_u_minus ;; [] ⊢ Srt Box ⇓ Srt Tri.
Proof. eapply C_Synth; [apply S_Sort; reflexivity | apply conv_refl]. Qed.

Example tri_untyped : forall T, ~ system_u_minus ;; [] ⊢ Srt Tri ⇑ T.
Proof. intros T H. inversion H; subst. discriminate. Qed.

Example tri_btype : btype system_u_minus [] (Srt Tri).
Proof. left. now exists Tri. Qed.

(** The raw term Ω of Examples.v has no normal form.  It does
    not synthesize in the annotated kernel, for any specification and
    context ([omega_not_synth]: its head is an unannotated λ).  Whether it
    is declaratively typable is not settled here.  So it illustrates the
    evaluator and the fast path of [convert], not the normalization
    premise of PTS.Bidir.
    Compared with itself it is equal without any fuel; with an annotation
    on one side, the terms are convertible but only normalization could
    tell, and it runs out of fuel. *)

Example omega_not_synth : forall S G A, ~ S ;; G ⊢ raw_omega ⇑ A.
Proof.
  intros S G A H. unfold raw_omega, self_app in H. inversion H; subst.
  match goal with Hf : synth _ _ (Lam _) _ |- _ => inversion Hf end.
Qed.

Example convert_omega_syntactic : convert 0 raw_omega raw_omega = ConvEqual raw_omega.
Proof. reflexivity. Qed.

Example convert_omega_annotated :
  convert 50 raw_omega (Ann raw_omega (Srt Star)) = ConvOutOfFuel.
Proof. vm_compute. reflexivity. Qed.

(** The fast path of [convert] does not diagnose stuckness: the stuck raw
    term [App Tt (Ann Tt Unit)] is stuck for [normalize], yet equal to
    itself for [convert].  A syntactically different partner exposes it. *)
Example convert_identical_stuck :
  let x := App Tt (Ann Tt Unit) in
  normalize 1 x = StuckTerm x /\ convert 1 x x = ConvEqual x /\
  convert 1 x (App Tt Tt) = ConvStuck.
Proof. vm_compute. auto. Qed.

(** ** The checker

    One program, several specifications.  [ΠA:∗. A → A] and the
    polymorphic identity in U⁻; the same type after renaming the sorts is
    one universe too high for the predicative hierarchy. *)


Example check_id_u_minus : snd (run_infer system_u_minus 100 [] id_tm) = Accepted id_ty.
Proof. vm_compute. reflexivity. Qed.

Example check_id_ty_star : snd (run_infer system_u_minus 100 [] id_ty) = Accepted (Srt Star).
Proof. vm_compute. reflexivity. Qed.

(** The lecture trace of [id A x] with [A : ∗, x : A]: the context is
    validated entry by entry, then the term is typed.  The type of the
    function unfolds to a Π, the argument is checked against the domain,
    and only then substituted into the codomain. *)
Example check_id_applied :
  run_infer system_u_minus 100 [Var 0; Srt Star] (App (App id_tm (Var 1)) (Var 0)) =
  ([EvCtxEntry 0 (Srt Star); EvAxiom Star Box;
    EvCtxEntry 1 (Var 0);
    EvTerm (App (App id_tm (Var 1)) (Var 0));
    EvAxiom Star Box; EvRule Star Star Star; EvRule Box Star Star;
    EvUnfoldPi (Lam (Lam (Var 0))) id_ty (Srt Star) (Pi (Var 0) (Var 1));
    EvUnfoldPi (Lam (Var 0)) (Pi (Var 0) (Var 1)) (Var 0) (Var 1);
    EvConv (Var 1) (Var 1) (Var 1);
    EvUnfoldPi id_tm id_ty (Srt Star) (Pi (Var 0) (Var 1));
    EvConv (Srt Star) (Srt Star) (Srt Star); EvArg (Var 1) (Srt Star);
    EvSubst (Pi (Var 0) (Var 1)) (Var 1) (Pi (Var 1) (Var 2));
    EvUnfoldPi (App id_tm (Var 1)) (Pi (Var 1) (Var 2)) (Var 1) (Var 2);
    EvConv (Var 1) (Var 1) (Var 1); EvArg (Var 0) (Var 1);
    EvSubst (Var 2) (Var 0) (Var 1)],
   Accepted (Var 1)).
Proof. vm_compute. reflexivity. Qed.

(** Types do not depend on terms in U⁻: the rule (∗, □) is missing. *)
Example check_no_star_box :
  snd (run_infer system_u_minus 100 [Srt Star] (Pi (Var 0) (Srt Star))) = Rejected (ENoRule (Pi (Var 0) (Srt Star)) Star Box).
Proof. vm_compute. reflexivity. Qed.

Example check_id_ty_univ1 :
  snd (run_infer predicative 100 [] (map_sorts u_to_univ id_ty)) = Accepted (Srt (Univ 1)).
Proof. vm_compute. reflexivity. Qed.

Example check_id_ty_not_univ0 :
  snd (run_check predicative 100 [] (map_sorts u_to_univ id_ty) (Srt (Univ 0))) =
  Rejected (EMismatch (map_sorts u_to_univ id_ty) (Srt (Univ 0)) (Srt (Univ 1))).
Proof. vm_compute. reflexivity. Qed.

Example check_top_sort : snd (run_infer system_u_minus 100 [] (Srt Tri)) = Rejected (ETopSort Tri).
Proof. vm_compute. reflexivity. Qed.

Example check_foreign_sort :
  snd (run_infer system_u_minus 100 [] (Srt (Univ 0))) = Rejected (ENotInSystem (Univ 0)).
Proof. vm_compute. reflexivity. Qed.

Example check_no_primitives_u_minus :
  snd (run_infer system_u_minus 100 [] Bool) = Rejected (ENoPrimitives Bool).
Proof. vm_compute. reflexivity. Qed.

(** Large elimination with [type_family] of Examples.v. *)

Example check_large_elim_true :
  snd (run_check predicative 100 [] Tt (ElimBool type_family Unit Bool BTrue)) = Accepted tt.
Proof. vm_compute. reflexivity. Qed.

(** The lecture trace of large elimination: validating the expected type
    records the family into the universe Type_1, both branches compared
    with the computed [type_family true] and [type_family false], and the
    expected type unfolded to the sort Type_0; then [tt] is checked, its
    type [Unit] and the expected type both reaching [Unit]. *)
Example check_large_elim_trace :
  run_check predicative 100 [] Tt (ElimBool type_family Unit Bool BTrue) =
  ([EvExpected (ElimBool type_family Unit Bool BTrue);
    EvAxiom (Univ 1) (Univ 2); EvRule (Univ 0) (Univ 2) (Univ 2);
    EvUnfoldPi (Lam (Srt (Univ 0))) (Pi Bool (Srt (Univ 1))) Bool (Srt (Univ 1));
    EvAxiom (Univ 0) (Univ 1);
    EvConv (Srt (Univ 1)) (Srt (Univ 1)) (Srt (Univ 1));
    EvUnfoldPi type_family (Pi Bool (Srt (Univ 1))) Bool (Srt (Univ 1));
    EvFamily type_family Bool (Univ 1);
    EvConv (Srt (Univ 0)) (App type_family BTrue) (Srt (Univ 0));
    EvConv (Srt (Univ 0)) (App type_family BFalse) (Srt (Univ 0));
    EvConv Bool Bool Bool;
    EvUnfoldSort (ElimBool type_family Unit Bool BTrue) (App type_family BTrue) (Univ 0);
    EvTerm Tt;
    EvConv Unit (ElimBool type_family Unit Bool BTrue) Unit],
   Accepted tt).
Proof. vm_compute. reflexivity. Qed.

Example check_large_elim_false :
  snd (run_check predicative 100 [] BTrue (ElimBool type_family Unit Bool BFalse)) = Accepted tt.
Proof. vm_compute. reflexivity. Qed.

Example check_wrong_branch :
  snd (run_infer predicative 100 [] (ElimBool type_family Unit Tt BTrue)) =
  Rejected (EMismatch Tt (App type_family BFalse) Unit).
Proof. vm_compute. reflexivity. Qed.

(** With a free boolean the computed type stays neutral. *)
Example check_neutral_type :
  snd (run_check predicative 100 [Bool] Tt (ElimBool type_family Unit Bool (Var 0))) =
  Rejected (EMismatch Tt (ElimBool type_family Unit Bool (Var 0)) Unit).
Proof. vm_compute. reflexivity. Qed.

Example check_bad_family :
  snd (run_infer predicative 100 []
         (ElimBool (Ann (Lam Bool) (Pi Unit (Srt (Univ 0)))) BTrue BTrue BTrue)) =
  Rejected (EBadFamily (Ann (Lam Bool) (Pi Unit (Srt (Univ 0)))) Bool Unit).
Proof. vm_compute. reflexivity. Qed.

Example check_lam_needs_annotation :
  snd (run_infer predicative 100 [] (App (Lam (Var 0)) BTrue)) = Rejected (ECannotInfer (Lam (Var 0))).
Proof. vm_compute. reflexivity. Qed.

Example check_annotated_redex :
  snd (run_infer predicative 100 [] (App (Ann (Lam (Var 0)) (Pi Bool Bool)) BTrue)) = Accepted Bool.
Proof. vm_compute. reflexivity. Qed.

Example check_not_a_function :
  snd (run_infer predicative 100 [] (App BTrue Tt)) = Rejected (ENotAPi BTrue Bool).
Proof. vm_compute. reflexivity. Qed.

(** Without fuel the expected type cannot even be validated: its branch
    [Unit] is compared with the computed [type_family true].  The answer
    is undecided, not a rejection. *)
Example check_out_of_fuel :
  snd (run_check predicative 0 [] Tt (ElimBool type_family Unit Bool BTrue)) = Undecided Unit.
Proof. vm_compute. reflexivity. Qed.

(** ** Validation of inputs *)

(** The annotated kernel derives [true ⇓ Ann Bool (Var 0)] in the empty
    context (chk_unbound_annotation); the checker rejects the expected
    type first. *)
Example check_unbound_annotation :
  snd (run_check predicative 100 [] BTrue (Ann Bool (Var 0))) = Rejected (EUnboundVar 0).
Proof. vm_compute. reflexivity. Qed.

(** The top sort △ has no type, yet it is an admissible expected type. *)
Example check_box_tri : snd (run_check system_u_minus 100 [] (Srt Box) (Srt Tri)) = Accepted tt.
Proof. vm_compute. reflexivity. Qed.

Example check_expected_foreign_sort :
  snd (run_check system_u_minus 100 [] (Srt Star) (Srt (Univ 1))) = Rejected (ENotInSystem (Univ 1)).
Proof. vm_compute. reflexivity. Qed.

(** A context entry must be a type: [true] is a term of type Bool. *)
Example check_ctx_not_a_type :
  snd (run_infer predicative 100 [BTrue] (Var 0)) = Rejected (ENotASort BTrue Bool).
Proof. vm_compute. reflexivity. Qed.

(** Each entry is checked in the context behind it: [Var 0] has nothing
    to refer to as the last entry. *)
Example check_ctx_unbound :
  snd (run_infer system_u_minus 100 [Srt Star; Var 0] (Var 0)) = Rejected (EUnboundVar 0).
Proof. vm_compute. reflexivity. Qed.

(** ** Named terms *)

Section Named.
  Import Stdlib.Strings.String DepTypes.Common.Result.
  Open Scope string_scope.
  Open Scope nterm_scope.

  Example named_id :
    resolve [] ((λ "A", λ "x", "x") ∷ (Π "A" : ⋆, "A" ~> "A")) = Ok id_tm.
  Proof. reflexivity. Qed.

  (** A name refers to its nearest binder; an outer one stays reachable
      under a binder of another name. *)
  Example named_shadowing :
    resolve [] (λ "x", λ "x", "x") = Ok (Lam (Lam (Var 0))) /\
    resolve [] (λ "x", λ "y", "x") = Ok (Lam (Lam (Var 1))).
  Proof. split; reflexivity. Qed.

  (** The anonymous binder of an arrow shifts the outer names. *)
  Example named_arrow :
    resolve ["A"] ("A" ~> "A") = Ok (Pi (Var 0) (Var 1)).
  Proof. reflexivity. Qed.

  Example named_unbound : resolve ["x"] ("x" "y") = Err "y".
  Proof. reflexivity. Qed.

  Example named_anon_unreachable : resolve ["A"] ("A" ~> anon) = Err anon.
  Proof. reflexivity. Qed.

  Example named_context :
    resolve_ctx [("x", NVar "A"); ("A", ⋆)] = Ok (["x"; "A"], id_applied_ctx).
  Proof. reflexivity. Qed.

  Example named_id_applied :
    resolve ["x"; "A"] (((λ "A", λ "x", "x") ∷ (Π "A" : ⋆, "A" ~> "A")) "A" "x")
    = Ok id_applied.
  Proof. reflexivity. Qed.
End Named.
