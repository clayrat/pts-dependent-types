(** * Numerals in U⁻ and the strictness of PCF

    The target of the PCF translation has no primitive data: ℕ becomes
    the Church numerals of System F, which live in ∗ in U⁻ by the rule
    (□, ∗).  Booleans are Church booleans, the predecessor is Kleene's,
    through pairs of numerals.

    ** Strictness

    PCF passes function arguments by name, but [succ], [pred] and the
    condition of [ifz] are strict: there is no value "succ of a divergent
    number", [succ Ω] diverges.  Church numerals do have such partial
    values: [λX f x. f (Ω X f x)] is the successor of a divergent number,
    and its outermost layer is visible without evaluating Ω.

    The observation of a closed program of type ℕ is the normal form of
    its translation under normal order, decoded to a number.  Normalizing
    a numeral evaluates all of it, so a partial numeral that reaches the
    observation diverges, as in PCF.  The only place where a number is
    inspected and then dropped is the condition of [ifz].  The usual
    Church test [n Bool (λ_. false) true] looks at the outermost layer
    only, like a test of lazy Peano naturals ([isZero (S ⊥) = False]), and
    answers [false] for [succ Ω] where PCF diverges.

    So [is_zero] is strict in the whole numeral: its step [λr. r Bool
    false false] uses the result of the inner layer, so the test runs
    through every layer down to zero and diverges on a partial numeral.
    Only the condition is forced: the branches stay unevaluated until one
    is chosen, and function arguments are still passed by name.  The lazy
    test [is_zero_lazy] is kept as the counterexample. *)

From Stdlib Require Import String List.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Reduction NormalOrder Eval Bidir Check CheckSound.
From DepTypes.Configs Require Import Finite.
From DepTypes.SystemU Require Import Looping.

Open Scope string_scope.
Open Scope nterm_scope.

(** ** Encodings *)

Definition CNat : nterm := Π "X" : ⋆, ("X" ~> "X") ~> "X" ~> "X".
Definition CBool : nterm := Π "X" : ⋆, "X" ~> "X" ~> "X".

Definition ctrue : nterm := (λ "X", λ "a", λ "b", "a") ∷ CBool.
Definition cfalse : nterm := (λ "X", λ "a", λ "b", "b") ∷ CBool.

Definition czero : nterm := (λ "X", λ "f", λ "x", "x") ∷ CNat.
Definition csucc : nterm :=
  (λ "n", λ "X", λ "f", λ "x", "f" ("n" "X" "f" "x")) ∷ (CNat ~> CNat).

Fixpoint iter_f (k : nat) : nterm :=
  match k with
  | 0 => "x"
  | S k' => "f" (iter_f k')
  end.

(** The numeral of a PCF literal. *)
Definition numeral (k : nat) : nterm := (λ "X", λ "f", λ "x", iter_f k) ∷ CNat.

(** Kleene's predecessor: iterate [(a, b) ↦ (b, b + 1)] from [(0, 0)]
    and take the first component, so [pred 0 = 0]. *)
Definition CPair : nterm := Π "X" : ⋆, (CNat ~> CNat ~> "X") ~> "X".
Definition cpair : nterm :=
  (λ "a", λ "b", λ "X", λ "k", "k" "a" "b") ∷ (CNat ~> CNat ~> CPair).
Definition cfst : nterm := (λ "p", "p" CNat (λ "a", λ "b", "a")) ∷ (CPair ~> CNat).
Definition csnd : nterm := (λ "p", "p" CNat (λ "a", λ "b", "b")) ∷ (CPair ~> CNat).
Definition cshift : nterm :=
  (λ "p", cpair (csnd "p") (csucc (csnd "p"))) ∷ (CPair ~> CPair).
Definition cpred : nterm :=
  (λ "n", cfst ("n" CPair cshift (cpair czero czero))) ∷ (CNat ~> CNat).

(** The test, strict in the whole numeral, and the usual lazy one. *)
Definition is_zero : nterm :=
  (λ "n", "n" CBool (λ "r", "r" CBool cfalse cfalse) ctrue) ∷ (CNat ~> CBool).
Definition is_zero_lazy : nterm :=
  (λ "n", "n" CBool (λ "r", cfalse) ctrue) ∷ (CNat ~> CBool).

(** [ifz c then a else b] at a result type [T]: the Church boolean picks a
    branch without evaluating the other. *)
Definition ifz (T c a b : nterm) : nterm := is_zero c T a b.
Definition ifz_lazy (T c a b : nterm) : nterm := is_zero_lazy c T a b.

(** The translation of [Ω_ℕ = fix_ℕ (λx:ℕ. x)], and of the same fixed
    point at the function type ℕ → ℕ. *)
Definition omega_nat : nterm := L0 CNat (λ "x", "x").
Definition omega_fun : nterm := L0 (CNat ~> CNat) (λ "g", "g").

(** ** Observation

    A Church numeral in normal form is [λX f x. fᵏ x]: [f] is [Var 1] and
    [x] is [Var 0] under the three binders. *)

Definition church_nf (k : nat) : term :=
  Lam (Lam (Lam (Nat.iter k (App (Var 1)) (Var 0)))).

Fixpoint count_f (t : term) : option nat :=
  match t with
  | Var 0 => Some 0
  | App (Var 1) u => option_map S (count_f u)
  | _ => None
  end.

Definition decode_nat (t : term) : option nat :=
  match t with
  | Lam (Lam (Lam b)) => count_f b
  | _ => None
  end.

Lemma count_f_sound : forall t k, count_f t = Some k -> t = Nat.iter k (App (Var 1)) (Var 0).
Proof.
  induction t; intros k H; cbn in H; try discriminate.
  - destruct n; [injection H as <-; reflexivity | discriminate].
  - destruct t1; try discriminate. destruct n as [|[|n]]; try discriminate.
    destruct (count_f t2) as [j|] eqn:E; [ | discriminate].
    injection H as <-. cbn. f_equal. apply IHt2. reflexivity.
Qed.

Lemma decode_nat_sound : forall t k, decode_nat t = Some k -> t = church_nf k.
Proof.
  intros t k H. unfold decode_nat in H.
  repeat (match type of H with context [match ?x with _ => _ end] => destruct x end;
          try discriminate).
  unfold church_nf. rewrite (count_f_sound _ _ H). reflexivity.
Qed.

Inductive observation : Type :=
| ObsNumeral : nat -> observation          (** a numeral: the result *)
| ObsOtherNormal : term -> observation     (** a normal form, not a numeral *)
| ObsStuck : term -> observation
| ObsOutOfFuel : term -> observation.      (** inconclusive *)

Definition observe (fuel : nat) (t : term) : observation :=
  match normalize fuel t with
  | NormalForm v => match decode_nat v with Some k => ObsNumeral k | None => ObsOtherNormal v end
  | StuckTerm v => ObsStuck v
  | OutOfFuel v => ObsOutOfFuel v
  end.

(** A numeric observation is the normal form of that numeral, reached by
    normal order. *)
Lemma observe_numeral_sound : forall fuel t k,
  observe fuel t = ObsNumeral k -> t ⇝ₙ* church_nf k /\ nf (church_nf k).
Proof.
  intros fuel t k H. unfold observe in H. pose proof (normalize_spec fuel t) as [Hr Hs].
  destruct (normalize fuel t) as [v|v|v]; try discriminate.
  destruct (decode_nat v) as [j|] eqn:E; [ | discriminate].
  injection H as <-. apply decode_nat_sound in E. subst. split; assumption.
Qed.

(** ** Typing in U⁻ *)

Definition church (t : nterm) : term := build [] t.

Definition encodings_typed : list (string * nterm * nterm) :=
  [ ("true", ctrue, CBool); ("false", cfalse, CBool);
    ("zero", czero, CNat); ("succ", csucc, CNat ~> CNat);
    ("numeral 3", numeral 3, CNat);
    ("pair", cpair, CNat ~> CNat ~> CPair); ("fst", cfst, CPair ~> CNat);
    ("snd", csnd, CPair ~> CNat); ("shift", cshift, CPair ~> CPair);
    ("pred", cpred, CNat ~> CNat);
    ("is_zero", is_zero, CNat ~> CBool); ("is_zero_lazy", is_zero_lazy, CNat ~> CBool);
    ("Ω_ℕ", omega_nat, CNat); ("Ω_ℕ→ℕ", omega_fun, CNat ~> CNat);
    ("ifz at ℕ → ℕ", ifz (CNat ~> CNat) czero csucc cpred, CNat ~> CNat) ].

Definition typed_in_u_minus (t A : nterm) : bool :=
  match snd (run_infer system_u_minus looping_fuel [] (church t)) with
  | Accepted B => term_eqb B (church A)
  | _ => false
  end.

Example encodings_accepted :
  forallb (fun '(_, t, A) => typed_in_u_minus t A) encodings_typed = true.
Proof. vm_compute. reflexivity. Qed.

Lemma typed_in_u_minus_sound : forall t A,
  typed_in_u_minus t A = true -> system_u_minus ;; [] ⊢ church t ⇑ church A.
Proof.
  intros t A H. unfold typed_in_u_minus in H.
  destruct (snd (run_infer system_u_minus looping_fuel [] (church t))) as [B| |] eqn:E;
    try discriminate.
  apply term_eqb_eq in H. subst. exact (accepted_synth _ _ _ _ E).
Qed.

(** The rest of stage 4: the translation of Ω_ℕ is a numeral program of
    U⁻, checked without running it. *)
Theorem omega_nat_typed : system_u_minus ;; [] ⊢ church omega_nat ⇑ church CNat.
Proof. apply typed_in_u_minus_sound. vm_compute. reflexivity. Qed.

(** ** Arithmetic on numerals *)

Definition observe_fuel : nat := 3000.

Fixpoint succs (k : nat) (t : nterm) : nterm :=
  match k with
  | 0 => t
  | S k' => csucc (succs k' t)
  end.

Example succ_observed :
  map (fun k => observe observe_fuel (church (succs k czero))) [0; 1; 2; 5]
  = [ObsNumeral 0; ObsNumeral 1; ObsNumeral 2; ObsNumeral 5].
Proof. vm_compute. reflexivity. Qed.

Example pred_observed :
  map (fun k => observe observe_fuel (church (cpred (numeral k)))) [0; 1; 2; 5]
  = [ObsNumeral 0; ObsNumeral 0; ObsNumeral 1; ObsNumeral 4].
Proof. vm_compute. reflexivity. Qed.

Example ifz_observed :
  map (fun k => observe observe_fuel (church (ifz CNat (numeral k) (numeral 7) (numeral 9))))
      [0; 1; 3]
  = [ObsNumeral 7; ObsNumeral 9; ObsNumeral 9].
Proof. vm_compute. reflexivity. Qed.

(** ** Strictness regressions

    The programs of the PCF regression table, written directly with the
    encodings.  Each is a program of type ℕ in U⁻.  An observation is
    compared with PCF by a three-valued [verdict]:
    - [Agrees]: the number PCF yields;
    - [NoResult]: no normal form within the fuel.  For a program that
      diverges in PCF this is the best a bounded run can say; it does not
      prove divergence, and it is also the answer for a terminating
      program given too little fuel;
    - [Contradicts]: a result PCF does not have.  A normal form found is a
      definite counterexample, whatever the fuel.
    The terminating programs agree, and the diverging ones have no result
    within the fuel.  That they diverge, and the adequacy of the encoding
    in general, are not proved here; the evaluation of [Ω_ℕ] never ends
    by the unfolding of the looping combinator, Lemma 3 of the paper. *)

(** [Some k]: the program yields [k]; [None]: it diverges in PCF. *)
Definition strictness_cases : list (string * nterm * option nat) :=
  [ ("(λx:ℕ. 0) Ω", ((λ "x", czero) ∷ (CNat ~> CNat)) omega_nat, Some 0);
    ("ifz (succ Ω) then 0 else 1", ifz CNat (csucc omega_nat) czero (numeral 1), None);
    ("ifz 0 then 7 else Ω", ifz CNat czero (numeral 7) omega_nat, Some 7);
    ("ifz 1 then Ω else 7", ifz CNat (numeral 1) omega_nat (numeral 7), Some 7);
    ("pred 0", cpred czero, Some 0);
    ("pred Ω", cpred omega_nat, None);
    ("ifz (pred (succ Ω)) then 0 else 1", ifz CNat (cpred (csucc omega_nat)) czero (numeral 1), None);
    ("succ Ω", csucc omega_nat, None);
    (* the result type of ifz is a function type *)
    ("(ifz 0 then succ else pred) 5", ifz (CNat ~> CNat) czero csucc cpred (numeral 5), Some 6);
    ("(ifz 1 then succ else pred) 5", ifz (CNat ~> CNat) (numeral 1) csucc cpred (numeral 5), Some 4);
    ("(ifz (succ Ω) then succ else pred) 5",
      ifz (CNat ~> CNat) (csucc omega_nat) csucc cpred (numeral 5), None);
    ("(ifz 0 then succ else Ω_ℕ→ℕ) 5", ifz (CNat ~> CNat) czero csucc omega_fun (numeral 5), Some 6) ].

Inductive verdict : Type := Agrees | NoResult | Contradicts.

Definition verdict_of (expected : option nat) (o : observation) : verdict :=
  match expected, o with
  | _, ObsOutOfFuel _ => NoResult
  | Some k, ObsNumeral j => if Nat.eqb k j then Agrees else Contradicts
  | _, _ => Contradicts
  end.

(** The best verdict a bounded run can give: [Agrees] for a terminating
    program, [NoResult] for a diverging one. *)
Definition best_verdict (expected : option nat) : verdict :=
  match expected with
  | Some _ => Agrees
  | None => NoResult
  end.

Definition verdict_eqb (v w : verdict) : bool :=
  match v, w with
  | Agrees, Agrees | NoResult, NoResult | Contradicts, Contradicts => true
  | _, _ => false
  end.

Example strictness_cases_typed :
  forallb (fun '(_, t, _) => typed_in_u_minus t CNat) strictness_cases = true.
Proof. vm_compute. reflexivity. Qed.

Example strictness_cases_observed :
  forallb (fun '(_, t, e) =>
             verdict_eqb (verdict_of e (observe observe_fuel (church t))) (best_verdict e))
          strictness_cases
  = true.
Proof. vm_compute. reflexivity. Qed.

(** [NoResult] alone says little: a terminating program with too little
    fuel gets it too. *)
Example no_result_is_not_divergence :
  verdict_of None (observe 0 (church (cpred (numeral 1)))) = NoResult.
Proof. vm_compute. reflexivity. Qed.

(** The lazy test gets the second case wrong: it answers 1, a definite
    contradiction. *)
Example lazy_test_answers_one :
  observe observe_fuel (church (ifz_lazy CNat (csucc omega_nat) czero (numeral 1))) = ObsNumeral 1
  /\ verdict_of None (ObsNumeral 1) = Contradicts.
Proof. split; vm_compute; reflexivity. Qed.
