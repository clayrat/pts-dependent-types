(** * Regression tests for the base definitions

    Substitution under several binders without capture, open terms, the
    sort tables of U⁻ and of the predicative hierarchy, normal order, and
    the gap between declarative typing and the annotated kernel. *)

From Stdlib Require Import List Relations.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Spec Reduction NormalOrder Eval Typing Bidir.
From DepTypes.Configs Require Import Finite Predicative.

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
  compare 0 (Var 0) (Lam (App (Var 1) (Var 0))) = ConvDifferent.
Proof. reflexivity. Qed.

Example conv_timeout_and_stuck :
  compare 0 (App (Lam (Var 0)) Tt) Tt = ConvOutOfFuel /\
  compare 1 (App Tt (Ann Tt Unit)) Tt = ConvStuck.
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

(** The raw term Ω = (λx. x x) (λx. x x) has no normal form.  It does
    not synthesize in the annotated kernel, for any specification and
    context ([omega_not_synth]: its head is an unannotated λ).  Whether it
    is declaratively typable is not settled here.  So it illustrates the
    evaluator and the fast path of [compare], not the normalization
    premise of PTS.Bidir.
    Compared with itself it is equal without any fuel; with an annotation
    on one side, the terms are convertible but only normalization could
    tell, and it runs out of fuel. *)
Definition self_app : term := Lam (App (Var 0) (Var 0)).
Definition omega : term := App self_app self_app.

Example omega_not_synth : forall S G A, ~ S ;; G ⊢ omega ⇑ A.
Proof.
  intros S G A H. unfold omega, self_app in H. inversion H; subst.
  match goal with Hf : synth _ _ (Lam _) _ |- _ => inversion Hf end.
Qed.

Example compare_omega_syntactic : compare 0 omega omega = ConvEqual.
Proof. reflexivity. Qed.

Example compare_omega_annotated :
  compare 50 omega (Ann omega (Srt Star)) = ConvOutOfFuel.
Proof. vm_compute. reflexivity. Qed.

(** The fast path of [compare] does not diagnose stuckness: the stuck raw
    term [App Tt (Ann Tt Unit)] is stuck for [normalize], yet equal to
    itself for [compare].  A syntactically different partner exposes it. *)
Example compare_identical_stuck :
  let x := App Tt (Ann Tt Unit) in
  normalize 1 x = StuckTerm x /\ compare 1 x x = ConvEqual /\
  compare 1 x (App Tt Tt) = ConvStuck.
Proof. vm_compute. auto. Qed.
