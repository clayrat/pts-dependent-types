(** * Prop beside the predicative hierarchy

    The configuration [predicative_prop] on the unchanged checker, in the
    empty signature.  Impredicativity comes from the table of products
    alone:
    - for [P : Type_i → Prop], the product [ΠA:Type_i. P A] is in Prop at
      every level [i], while the same product into Type₀ is one level up,
      in [Type_(i+1)];
    - [ΠP:Prop. P], the Church encoding of falsity, is a proposition.  It
      is not the empty inductive [False] of the declarations: the two have
      different eliminations, and only the inductive one is declared with
      its eliminator;
    - the identity on propositions, [ΠP:Prop. P → P], is itself a
      proposition and can be applied to its own type, as in the
      [impredicative_id] test of Hirrolot's CoC gist; the identity on
      Type₀ lives in Type₁, and the same application is rejected;
    - [Prop : Type₁], while [Type₀ : Type₀], [Prop : Prop] and, without
      cumulativity, [Prop : Type₀] are rejected; the predicative hierarchy
      without Prop does not know the sort.

    Σ has its own table and always lives in Type: all four combinations
    of Prop and Type₀ for the two components give a type, the pair of a
    witness and a proof [⟨a, p⟩ : Σx:A. P x] checks, its first projection
    extracts the witness as data, and the Σ itself is not a proposition. *)

From Stdlib Require Import String List Relations.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Spec Signature Reduction Eval Bidir Check CheckSound EmptySig Build Runs.
From DepTypes.Configs Require Import Finite Predicative.

Open Scope string_scope.
Open Scope nterm_scope.

Definition prop_fuel : nat := 100.

Definition NProp : nterm := NSrt Prp.

(** ** Impredicative products *)

(** [P : Type_i → Prop ⊢ ΠA:Type_i. P A]. *)
Definition pred_ctx (i : nat) : list (string * nterm) := [("P", Type@ i ~> NProp)].
Definition all_pred (i : nat) : nterm := Π "A" : Type@ i, "P" "A".

(** [F : Type_i → Type₀ ⊢ ΠA:Type_i. F A]. *)
Definition fam_ctx (i : nat) : list (string * nterm) := [("F", Type@ i ~> Type@ 0)].
Definition all_fam (i : nat) : nterm := Π "A" : Type@ i, "F" "A".

Definition levels : list nat := [0; 1; 2; 5].

Example all_pred_in_prop :
  map (fun i => infers predicative_prop ∅ prop_fuel (pred_ctx i) (all_pred i)) levels
  = map (fun _ => Accepted (Srt Prp)) levels.
Proof. vm_compute. reflexivity. Qed.

Example all_fam_one_level_up :
  map (fun i => infers predicative_prop ∅ prop_fuel (fam_ctx i) (all_fam i)) levels
  = map (fun i => Accepted (Srt (Univ (S i)))) levels.
Proof. vm_compute. reflexivity. Qed.

(** At every level, by the rules of the annotated kernel rather than by
    runs of the checker: the domain [Type_i : Type_(i+1)], the codomain
    [P A : Prop], and the rule [(Type_(i+1), Prop, Prop)]. *)
Theorem all_pred_every_level : forall i,
  predicative_prop ;; in_ctx (pred_ctx i) ⊢ term_in (pred_ctx i) (all_pred i) ⇑ Srt Prp.
Proof.
  intros i. vm_compute.
  eapply S_Pi with (s1 := Univ (S i)) (s2 := Prp).
  - apply S_Sort. reflexivity.
  - apply rt_refl.
  - eapply S_App.
    + apply S_Var. reflexivity.
    + apply rt_refl.
    + eapply C_Synth; [apply S_Var; reflexivity | apply conv_refl].
  - apply rt_refl.
  - reflexivity.
Qed.

Theorem all_fam_every_level : forall i,
  predicative_prop ;; in_ctx (fam_ctx i) ⊢ term_in (fam_ctx i) (all_fam i) ⇑ Srt (Univ (S i)).
Proof.
  intros i. vm_compute.
  eapply S_Pi with (s1 := Univ (S i)) (s2 := Univ 0).
  - apply S_Sort. reflexivity.
  - apply rt_refl.
  - eapply S_App.
    + apply S_Var. reflexivity.
    + apply rt_refl.
    + eapply C_Synth; [apply S_Var; reflexivity | apply conv_refl].
  - apply rt_refl.
  - reflexivity.
Qed.

(** [False^Ch := ΠP:Prop. P]. *)
Definition false_church : nterm := Π "P" : NProp, "P".

Example false_church_in_prop :
  infers predicative_prop ∅ prop_fuel [] false_church = Accepted (Srt Prp).
Proof. vm_compute. reflexivity. Qed.

(** ** The identity applied to its own type *)

Definition id_prop_ty : nterm := Π "P" : NProp, "P" ~> "P".
Definition id_prop : nterm := (λ "P", λ "x", "x") ∷ id_prop_ty.

Definition id0_ty : nterm := Π "X" : Type@ 0, "X" ~> "X".
Definition id0 : nterm := (λ "X", λ "x", "x") ∷ id0_ty.

Example id_prop_self_applied :
  infers predicative_prop ∅ prop_fuel [] (id_prop id_prop_ty id_prop)
  = Accepted (build [] id_prop_ty).
Proof. vm_compute. reflexivity. Qed.

Example id0_self_rejected :
  infers predicative_prop ∅ prop_fuel [] (id0 id0_ty id0)
  = Rejected (EMismatch (build [] id0_ty) (Srt (Univ 0)) (Srt (Univ 1))).
Proof. vm_compute. reflexivity. Qed.

(** ** Sorts *)

Example prop_in_type1 :
  snd (run_infer predicative_prop ∅ prop_fuel [] (Srt Prp)) = Accepted (Srt (Univ 1)).
Proof. vm_compute. reflexivity. Qed.

Example type0_type0_rejected :
  snd (run_check predicative_prop ∅ prop_fuel [] (Srt (Univ 0)) (Srt (Univ 0)))
  = Rejected (EMismatch (Srt (Univ 0)) (Srt (Univ 0)) (Srt (Univ 1))).
Proof. vm_compute. reflexivity. Qed.

Example prop_prop_rejected :
  snd (run_check predicative_prop ∅ prop_fuel [] (Srt Prp) (Srt Prp))
  = Rejected (EMismatch (Srt Prp) (Srt Prp) (Srt (Univ 1))).
Proof. vm_compute. reflexivity. Qed.

(** No cumulativity: Prop is not in Type₀. *)
Example prop_type0_rejected :
  snd (run_check predicative_prop ∅ prop_fuel [] (Srt Prp) (Srt (Univ 0)))
  = Rejected (EMismatch (Srt Prp) (Srt (Univ 0)) (Srt (Univ 1))).
Proof. vm_compute. reflexivity. Qed.

Example prop_unknown_predicative :
  snd (run_infer predicative ∅ prop_fuel [] (Srt Prp)) = Rejected (ENotInSystem Prp).
Proof. vm_compute. reflexivity. Qed.

(** ** Σ in Type *)

(** [Q R : Prop, A : Type₀, P : A → Prop], the innermost entry first. *)
Definition sig_ctx : list (string * nterm) :=
  [("P", "A" ~> NProp); ("A", Type@ 0); ("R", NProp); ("Q", NProp)].

Definition ex_sigma : nterm := Σ "x" : "A", "P" "x".

(** The four rows of the table, with the level of a component in Type
    kept: Type₀ and Type₁ for the domain [A] and for [Type₀]. *)
Example sigma_rows :
  map (fun t => infers predicative_prop ∅ prop_fuel sig_ctx t)
    [ Σ "x" : "A", "A";          (* (Type₀, Type₀) *)
      Σ "x" : "A", Type@ 0;      (* (Type₀, Type₁) *)
      ex_sigma;                  (* (Type₀, Prop) *)
      Σ "p" : "Q", "A";          (* (Prop, Type₀) *)
      Σ "p" : "Q", Type@ 0;      (* (Prop, Type₁) *)
      Σ "p" : "Q", "R" ]         (* (Prop, Prop) *)
  = [ Accepted (Srt (Univ 0)); Accepted (Srt (Univ 1)); Accepted (Srt (Univ 0));
      Accepted (Srt (Univ 0)); Accepted (Srt (Univ 1)); Accepted (Srt (Univ 0)) ].
Proof. vm_compute. reflexivity. Qed.

(** [a : A, p : P a ⊢ ⟨a, p⟩ ⇐ Σx:A. P x]. *)
Definition witness_ctx : list (string * nterm) := [("p", "P" "a"); ("a", NVar "A")] ++ sig_ctx.

Theorem witness_pair_typed :
  predicative_prop ;; in_ctx witness_ctx ⊢ term_in witness_ctx ⟨"a", "p"⟩ ⇓ term_in witness_ctx ex_sigma.
Proof. apply (accepted_check _ _ prop_fuel). vm_compute. reflexivity. Qed.

(** The witness comes out as data, the proof depends on it. *)
Definition pair_ctx : list (string * nterm) := ("s", ex_sigma) :: sig_ctx.

Example fst_witness :
  infers predicative_prop ∅ prop_fuel pair_ctx (NFst "s")
  = Accepted (term_in pair_ctx "A").
Proof. vm_compute. reflexivity. Qed.

Example snd_proof :
  infers predicative_prop ∅ prop_fuel pair_ctx (NSnd "s")
  = Accepted (term_in pair_ctx ("P" (NFst "s"))).
Proof. vm_compute. reflexivity. Qed.

Example fst_computes_to_witness :
  normalize ∅ prop_fuel (term_in witness_ctx (NFst (⟨"a", "p"⟩ ∷ ex_sigma)))
  = NormalForm (term_in witness_ctx "a").
Proof. vm_compute. reflexivity. Qed.

(** The Σ is a type of Type₀, not a proposition. *)
Example sigma_not_a_prop :
  snd (run_check predicative_prop ∅ prop_fuel (in_ctx sig_ctx) (term_in sig_ctx ex_sigma) (Srt Prp))
  = Rejected (EMismatch (term_in sig_ctx ex_sigma) (Srt Prp) (Srt (Univ 0))).
Proof. vm_compute. reflexivity. Qed.
