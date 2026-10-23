(** * Dependent pairs

    Σ in the predicative hierarchy, where [Σx:A. B : Type_(max i j)]:
    - the dependent pair [⟨true, tt⟩ : Σb:Bool. IsTrue b], with
      [IsTrue b = elimBool (λ_. Type₀) Unit Void b]: the type expected of
      the second component is computed from the first, and [⟨false, tt⟩]
      is rejected, since [IsTrue false] computes to [Void];
    - on a free [p : Σb:Bool. IsTrue b] the second projection has the type
      [IsTrue (fst p)], which stays neutral: the dependent [snd] that the
      Church encoding of lecture 6 could not express;
    - the projections compute on a pair, and there is no η for Σ;
    - the product [Bool × Bool] is Σ over a constant family;
    - a Σ over a universe lives a level up: [Σb:Bool. Type₀ : Type₁];
    - a pair only checks, and in U⁻ there is no Σ.
    No constants occur: the signature is empty. *)

From Stdlib Require Import String List Bool.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Spec Signature Reduction Eval Bidir Check CheckSound EmptySig.
From DepTypes.Configs Require Import Finite Predicative.
From DepTypes.SystemU Require Import Looping.
From DepTypes.MLTT Require Import Choose.

Open Scope string_scope.
Open Scope nterm_scope.

Definition pair_fuel : nat := 100.

(** [IsTrue b = elimBool (λ_. Type₀) Unit Void b]. *)
Definition is_true : nterm :=
  (λ "b", NElimBool ((λ "z", Type@ 0) ∷ (NBool ~> Type@ 1)) NUnit NVoid "b") ∷ (NBool ~> Type@ 0).
Definition true_sigma : nterm := Σ "b" : NBool, is_true "b".

Example pairs_resolve :
  resolves [] true_sigma && resolves [] ⟨NTrue, NTt⟩ && resolves [] (NBool ⨯ NBool) = true.
Proof. vm_compute. reflexivity. Qed.

(** ** The dependent pair *)

Theorem true_pair_typed : predicative ;; [] ⊢ build [] ⟨NTrue, NTt⟩ ⇓ build [] true_sigma.
Proof. apply (accepted_check _ pair_fuel). vm_compute. reflexivity. Qed.

Example false_pair_rejected :
  snd (run_check predicative ∅ pair_fuel [] (build [] ⟨NFalse, NTt⟩) (build [] true_sigma))
  = Rejected (EMismatch Tt (App (build [] is_true) BFalse) Unit).
Proof. vm_compute. reflexivity. Qed.

(** ** Projections *)

Definition sigma_ctx : ctx := [build [] true_sigma].

Example snd_dependent :
  snd (run_infer predicative ∅ pair_fuel sigma_ctx (Snd (Var 0)))
  = Accepted (App (build [] is_true) (Fst (Var 0))).
Proof. vm_compute. reflexivity. Qed.

Example snd_type_neutral :
  normalize ∅ pair_fuel (App (build [] is_true) (Fst (Var 0)))
  = NormalForm (ElimBool (Lam (Srt (Univ 0))) Unit Void (Fst (Var 0))).
Proof. vm_compute. reflexivity. Qed.

Example fst_computes :
  normalize ∅ pair_fuel (build [] (NFst (⟨NTrue, NFalse⟩ ∷ (NBool ⨯ NBool)))) = NormalForm BTrue.
Proof. vm_compute. reflexivity. Qed.

(** No η: a free pair is not the pair of its projections. *)
Example no_sigma_eta :
  convert ∅ pair_fuel (Var 0) (Pair (Fst (Var 0)) (Snd (Var 0))) = ConvDifferent.
Proof. vm_compute. reflexivity. Qed.

(** ** Products and levels *)

Theorem product_typed : predicative ;; [] ⊢ build [] ⟨NTrue, NFalse⟩ ⇓ build [] (NBool ⨯ NBool).
Proof. apply (accepted_check _ pair_fuel). vm_compute. reflexivity. Qed.

Example sigma_of_universe :
  snd (run_infer predicative ∅ pair_fuel [] (build [] (Σ "b" : NBool, Type@ 0)))
  = Accepted (Srt (Univ 1)).
Proof. vm_compute. reflexivity. Qed.

(** ** Rejections *)

Example pair_cannot_infer :
  snd (run_infer predicative ∅ pair_fuel [] (Pair BTrue BFalse))
  = Rejected (ECannotInfer (Pair BTrue BFalse)).
Proof. vm_compute. reflexivity. Qed.

Example fst_not_a_pair :
  snd (run_infer predicative ∅ pair_fuel [] (Fst Tt)) = Rejected (ENotASigma Tt Unit).
Proof. vm_compute. reflexivity. Qed.

Example sigma_u_minus_rejected :
  snd (run_infer system_u_minus ∅ pair_fuel [] (Sigma (Srt Star) (Var 0)))
  = Rejected (ENoSigmaRule (Sigma (Srt Star) (Var 0)) Box Star).
Proof. vm_compute. reflexivity. Qed.
