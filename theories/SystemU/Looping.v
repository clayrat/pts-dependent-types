(** * The looping combinator of λU⁻

    Hurkens' paradox in λU⁻, as formalized in Lego by Geuvers and Pollack
    and analysed by Geuvers–Verkoelen ("On Fixed point and Looping
    Combinators in Type Theory", §4), gives a closed term

      L₀ : Πβ:∗. (β → β) → β

    of pure U⁻: no axiom, no primitive recursion, no primitives.  It is a
    looping combinator: [Lₙ β f =β f (Lₙ₊₁ β f)] for a family [Lₙ] read
    off from its reduction (their Lemma 3).

    The Lego definitions are read as λU⁻ as in the paper: the bound [A] of
    [V], [sb] and [le] ranges over □, every other [Type] is ∗.  [V] and
    [U] are kinds, [sb], [le], [induct], [WF], [I] constructors, and
    [omega], [lemma], [lemma2] proof terms.  [I], [lemma], [lemma2] and
    [paradox] are open in [β : ∗, f : β → β], the context of the paper;
    no binder inside a definition is named [β] or [f].

    Definitions are pasted at the Rocq level by the builder of PTS.Named.
    A definition used as a function carries its type as an annotation,
    since a λ in a synthesizing position does not synthesize. *)

From Stdlib Require Import String List.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Reduction NormalOrder Eval Bidir Check CheckSound.
From DepTypes.Configs Require Import Finite Predicative.

Open Scope string_scope.
Open Scope nterm_scope.

(** ** Hurkens' paradox in λU⁻ *)

(** [V = ΠA:□. ((A → ∗) → A → ∗) → A → ∗] and [U = V → ∗]. *)
Definition V : nterm := Π "A" : □, (("A" ~> ⋆) ~> ("A" ~> ⋆)) ~> "A" ~> ⋆.
Definition U : nterm := V ~> ⋆.

Definition sb : nterm :=
  (λ "A", λ "r", λ "a", λ "z", "r" ("z" "A" "r") "a")
  ∷ (Π "A" : □, (("A" ~> ⋆) ~> ("A" ~> ⋆)) ~> "A" ~> U).

Definition le : nterm :=
  (λ "i", λ "x", "x" (λ "A", λ "r", λ "a", "i" (sb "A" "r" "a")))
  ∷ ((U ~> ⋆) ~> U ~> ⋆).

(** [Πx:U. le i x → i x] quantifies over the kind [U] and stays in ∗:
    the impredicative step, by the rule (□, ∗). *)
Definition induct_body : nterm := Π "x" : U, le "i" "x" ~> "i" "x".

Definition induct : nterm := (λ "i", induct_body) ∷ ((U ~> ⋆) ~> ⋆).

Definition WF : nterm := (λ "z", induct ("z" U le)) ∷ U.

(** [G = sb le : U → U], written [sb le] in the paper. *)
Definition G : nterm := sb U le.

Definition I : nterm :=
  (λ "x", (Π "i" : U ~> ⋆, le "i" "x" ~> "i" (G "x")) ~> "β") ∷ (U ~> ⋆).

Definition omega : nterm :=
  (λ "i", λ "y", "y" WF (λ "x", "y" (G "x")))
  ∷ (Π "i" : U ~> ⋆, induct "i" ~> "i" WF).

(** [lemma : induct I]; unannotated, as the argument of [lemma2]. *)
Definition lemma : nterm :=
  λ "x", λ "p", λ "q", "f" ("q" I "p" (λ "i", "q" (λ "y", "i" (G "y")))).

Definition lemma2 : nterm :=
  (λ "x", "x" I lemma (λ "i", "x" (λ "y", "i" (G "y"))))
  ∷ ((Π "i" : U ~> ⋆, induct "i" ~> "i" WF) ~> "β").

Definition paradox : nterm := lemma2 omega.

Definition L_ty : nterm := Π "β" : ⋆, ("β" ~> "β") ~> "β".

Definition L0 : nterm := (λ "β", λ "f", paradox) ∷ L_ty.

(** ** The family [Lₙ]

    [paradox] reduces to [lemma WF₁ P₁ Q₁], and by Lemma 3 of the paper
    [lemma WFₖ Pₖ Qₖ =β f (lemma WFₖ₊₁ Pₖ₊₁ Qₖ₊₁)], where

      WF₁ = WF,                 WFₖ₊₁ = G WFₖ,
      P₁ = λx. lemma (G x),     Pₖ₊₁ = λx. Pₖ (G x),
      Q₁ = λi. omega (λy. i (G y)),   Qₖ₊₁ = λi. Qₖ (λy. i (G y)).

    So [Lₙ = λβ f. lemma WFₙ₊₁ Pₙ₊₁ Qₙ₊₁] for [n ≥ 1].  As closed typed
    terms, the heads [lemma], [Pₖ] and [Qₖ] inside them are annotated
    with their types, [induct I], [le I WFₖ] and
    [Πi:U → ∗. le i WFₖ → i (G WFₖ)]; the reducts of [L₀] carry them bare.
    The two agree up to annotations, which conversion erases. *)

Definition lemma_ann : nterm := lemma ∷ (induct I).

Fixpoint WF_ (k : nat) : nterm :=
  match k with
  | 0 | 1 => WF
  | S k' => G (WF_ k')
  end.

Definition P_ty (k : nat) : nterm := le I (WF_ k).
Definition Q_ty (k : nat) : nterm := Π "i" : U ~> ⋆, le "i" (WF_ k) ~> "i" (G (WF_ k)).

Fixpoint P_ (k : nat) : nterm :=
  match k with
  | 0 | 1 => λ "x", lemma_ann (G "x")
  | S k' => λ "x", (P_ k' ∷ P_ty k') (G "x")
  end.

Fixpoint Q_ (k : nat) : nterm :=
  match k with
  | 0 | 1 => λ "i", omega (λ "y", "i" (G "y"))
  | S k' => λ "i", (Q_ k' ∷ Q_ty k') (λ "y", "i" (G "y"))
  end.

Definition L (n : nat) : nterm :=
  match n with
  | 0 => L0
  | S _ => (λ "β", λ "f", lemma_ann (WF_ (S n)) (P_ (S n)) (Q_ (S n))) ∷ L_ty
  end.

(** ** As de Bruijn terms *)

(** The resolved term, or ∗ if a name is unbound; [looping_resolves]
    shows that the latter does not happen for the terms below. *)
Definition build (names : list string) (t : nterm) : term :=
  match resolve names t with
  | Ok u => u
  | Err _ => Srt Star
  end.

Definition looping (n : nat) : term := build [] (L n).
Definition looping_ty : term := build [] L_ty.

Example looping_resolves :
  map (fun n => match resolve [] (L n) with Ok _ => true | Err _ => false end) [0; 1; 2; 3]
  = [true; true; true; true].
Proof. vm_compute. reflexivity. Qed.

(** ** Typing in U⁻

    The checker accepts [Lₙ] with the type [Πβ:∗. (β → β) → β], and its
    soundness turns the run into a derivation of the annotated kernel.
    The fuel bounds the normalization of the compared types: [L₀] needs
    about 150 steps, [L₃] about 900. *)

Definition looping_fuel : nat := 1000.

Lemma accepted_synth : forall S fuel t A,
  snd (run_infer S fuel [] t) = Accepted A -> S ;; [] ⊢ t ⇑ A.
Proof. intros S fuel t A H. exact (proj2 (run_infer_sound S fuel [] t A H)). Qed.

Theorem looping0_typed : system_u_minus ;; [] ⊢ looping 0 ⇑ looping_ty.
Proof. apply (accepted_synth _ looping_fuel). vm_compute. reflexivity. Qed.

Theorem looping_typed : forall n, n <= 3 ->
  system_u_minus ;; [] ⊢ looping n ⇑ looping_ty.
Proof.
  intros n Hn.
  do 4 (destruct n as [|n]; [apply (accepted_synth _ looping_fuel); vm_compute; reflexivity | ]).
  exfalso. repeat apply le_S_n in Hn. inversion Hn.
Qed.

(** As in the paper, [paradox : β] in the context [β : ∗, f : β → β]. *)
Example paradox_typed :
  snd (run_check system_u_minus looping_fuel [Pi (Var 0) (Var 1); Srt Star]
         (build ["f"; "β"] paradox) (Var 1)) = Accepted tt.
Proof. vm_compute. reflexivity. Qed.

(** ** Unfolding

    [Lₙ β f], with [β] and [f] free, reduces by normal order to [f M], and
    [M] meets [Lₙ₊₁ β f] in a common reduct up to annotations.  Hence
    [Lₙ β f =β f (Lₙ₊₁ β f)].  Both facts are found by bounded
    evaluation and certified by [whnf_reduces] and [joinable_sound]; it
    takes 11 steps from [L₀ β f] to [f M], and 7 from [Lₙ β f], n ≥ 1.

    This is checked for [n ≤ 2]; Lemma 3 of the paper is the argument for
    every [n].  Neither [Lₙ β f] nor [M] has a normal form, so [convert]
    could not decide this conversion. *)

(** [t] reduces to [f m], and [m] is joinable with [u]. *)
Definition unfolds_to (fuel : nat) (t f u : term) : bool :=
  match whnf fuel t with
  | HeadForm (App f' m) => term_eqb f' f && joinable fuel m u
  | _ => false
  end.

Lemma unfolds_to_sound : forall fuel t f u,
  unfolds_to fuel t f u = true -> t ≡ App f u.
Proof.
  intros fuel t f u H. unfold unfolds_to in H.
  destruct (whnf fuel t) as [v | v] eqn:W; [ | discriminate H].
  destruct v; try discriminate H.
  apply andb_prop in H as [Ef Hj]. apply term_eqb_eq in Ef. subst.
  apply conv_trans with (App f v2).
  - apply red_conv, nsteps_red, (whnf_reduces fuel), W.
  - apply conv_app_arg, (joinable_sound fuel), Hj.
Qed.

(** [Lₙ β f] in the context [β : ∗, f : β → β]: [β] is [Var 1], [f] is
    [Var 0]. *)
Definition looping_applied (n : nat) : term := App (App (looping n) (Var 1)) (Var 0).

Definition unfolding_fuel : nat := 100.

Theorem looping_unfolds : forall n, n <= 2 ->
  looping_applied n ≡ App (Var 0) (looping_applied (S n)).
Proof.
  intros n Hn. apply (unfolds_to_sound unfolding_fuel).
  do 3 (destruct n as [|n]; [vm_compute; reflexivity | ]).
  exfalso. repeat apply le_S_n in Hn. inversion Hn.
Qed.

(** ** The predicative hierarchy rejects it

    With ∗, □, △ read as Type₀, Type₁, Type₂, the checker of the
    predicative hierarchy rejects [L₀] at the body of [induct]:
    [Πx:U. le i x → i x] quantifies over [U : Type₂], so it lives in
    Type₂, not in the Type₀ that [induct : (U → Type₀) → Type₀] promises.
    This is a run of the checker, not a proof that no annotation would
    make [L₀] typable there: that needs completeness of the checker. *)

Example looping_predicative_rejected :
  snd (run_infer pure_predicative looping_fuel [] (map_sorts u_to_univ (looping 0)))
  = Rejected (EMismatch (map_sorts u_to_univ (build ["i"] induct_body))
                        (Srt (Univ 0)) (Srt (Univ 2))).
Proof. vm_compute. reflexivity. Qed.
