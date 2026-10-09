(** * PCF programs and their translations

    The regression programs, written in PCF with the notations of
    strictness-pcf, together with [add], [mul] and [fact] of its
    Examples.v.  For each program:
    - the PCF checker accepts it at ℕ and the translator translates it;
    - the U⁻ checker, run on the translation, accepts it against [Nat]
      ([translate_program_checked]);
    - on the source side, the PCF evaluator yields the expected number,
      or the program diverges in PCF: [diverges t], proved from the
      divergence of Ω and the closure lemmas of strictness-pcf through
      the strict contexts [succ], [pred] and the condition of [ifz]
      ([pcf_cases_source]);
    - the translation, run by normal order, gets the best verdict a
      bounded run can give: the same number, or no result within the
      fuel.
    As in SystemU.Encodings, no result within the fuel is not a proof of
    divergence of the translation, and these runs are not a proof of
    adequacy: that the translation preserves and reflects convergence
    remains to be proved.

    [fact 4 = 24] takes about 1.4 million normal-order steps, out of reach
    of [vm_compute]; the OCaml extraction checks it as a slow test. *)

From Stdlib Require Import String List.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Syntax Eval Check.
From DepTypes.Configs Require Import Finite.
From DepTypes.SystemU Require Import Looping Encodings.
From DepTypes.PCFTranslation Require Import Translate.
From PCF Require Import Ty Syntax Examples OperationalSemantics.

Open Scope string_scope.
Open Scope pcf_scope.

(** ** Programs *)

Definition omega_pcf : PCF.Syntax.term := omega_at ℕ.
Definition omega_fun_pcf : PCF.Syntax.term := omega_at (ℕ ⇒ ℕ).
Definition succ_fun : PCF.Syntax.term := λ "n", tsucc (tvar "n").
Definition pred_fun : PCF.Syntax.term := λ "n", tpred (tvar "n").

(** [Some k]: the program yields [k]; [None]: it diverges in PCF. *)
Definition pcf_cases : list (string * PCF.Syntax.term * option nat) :=
  [ ("(λx:ℕ. 0) Ω", ((λ "x", # 0) ∷ ℕ ⇒ ℕ) · omega_pcf, Some 0);
    ("ifz (succ Ω) then 0 else 1", ifz tsucc omega_pcf then # 0 else # 1, None);
    ("ifz 0 then 7 else Ω", ifz # 0 then # 7 else omega_pcf, Some 7);
    ("ifz 1 then Ω else 7", ifz # 1 then omega_pcf else # 7, Some 7);
    ("pred 0", tpred (# 0), Some 0);
    ("pred Ω", tpred omega_pcf, None);
    ("ifz (pred (succ Ω)) then 0 else 1", ifz tpred (tsucc omega_pcf) then # 0 else # 1, None);
    ("succ Ω", tsucc omega_pcf, None);
    ("(ifz 0 then succ else pred) 5",
      ((ifz # 0 then succ_fun else pred_fun) ∷ ℕ ⇒ ℕ) · # 5, Some 6);
    ("(ifz 1 then succ else pred) 5",
      ((ifz # 1 then succ_fun else pred_fun) ∷ ℕ ⇒ ℕ) · # 5, Some 4);
    ("(ifz 0 then succ else Ω_ℕ→ℕ) 5",
      ((ifz # 0 then succ_fun else omega_fun_pcf) ∷ ℕ ⇒ ℕ) · # 5, Some 6);
    ("add 2 3", add · # 2 · # 3, Some 5);
    ("mul 2 3", mul · # 2 · # 3, Some 6);
    ("fact 0", fact · # 0, Some 1);
    ("fact 1", fact · # 1, Some 1);
    ("fact 2", fact · # 2, Some 2);
    ("fact 3", fact · # 3, Some 6);
    (* "_" is an ordinary variable name *)
    ("(λ_. _) 0", ((λ "_", tvar "_") ∷ ℕ ⇒ ℕ) · # 0, Some 0) ].

(** ** Checks *)

Definition pcf_fuel : nat := 10 * 1000.
(** Terminating programs get enough fuel for [fact 3] (about 35000
    steps).  A diverging program runs only [observe_fuel] steps: the
    looping combinator grows with each unfolding, and so does the cost of
    a step. *)
Definition translation_fuel : nat := 50 * 1000.

Definition fuel_for (expected : option nat) : nat :=
  match expected with
  | Some _ => translation_fuel
  | None => observe_fuel
  end.

Definition pcf_as_expected (expected : option nat) (t : PCF.Syntax.term) : bool :=
  match expected, evalFuel pcf_fuel t with
  | Some k, Value (tnum j) => Nat.eqb k j
  | None, Timeout => true
  | _, _ => false
  end.

(** The translation goes through [translate_program_checked]: the U⁻
    checker accepts each output before it is run. *)
Definition translation_as_expected (expected : option nat) (t : PCF.Syntax.term) : bool :=
  match translate_program_checked looping_fuel t with
  | Ok u => verdict_eqb (verdict_of expected (observe (fuel_for expected) u)) (best_verdict expected)
  | Err _ => false
  end.

(** ** The source side

    Ω diverges, as in strictness-pcf's Tests.v (not built here, since it
    needs the strictness analyser), and divergence passes out through
    [pred] as it does through [succ] and [ifz]. *)

Lemma omega_at_loop : forall A n,
  evalFuel n (omega_at A) = Timeout /\ evalFuel n ((λ "x", tvar "x") · omega_at A) = Timeout.
Proof. intros A n. induction n as [| n [IH1 IH2]]; split; simpl; auto. Qed.

Theorem omega_at_diverges : forall A, diverges (omega_at A).
Proof. intros A n. apply omega_at_loop. Qed.

Lemma diverges_pred1 : forall t, diverges t -> diverges (tpred t).
Proof.
  intros t Hdiv fuel. revert t Hdiv.
  induction fuel as [| fuel IH]; intros t Hdiv; [reflexivity |].
  destruct (diverges_next _ Hdiv) as (t' & Hstep & Hdiv').
  rewrite (evalFuel_step fuel (tpred t) (tpred t'));
    [apply IH, Hdiv' | apply S_Pred1, Hstep].
Qed.

(** What PCF does with each program: the expected number, or genuine
    divergence. *)
Definition source_behaviour (expected : option nat) (t : PCF.Syntax.term) : Prop :=
  match expected with
  | Some k => evalFuel pcf_fuel t = Value (tnum k)
  | None => diverges t
  end.

Theorem pcf_cases_source :
  Forall (fun c => source_behaviour (snd c) (snd (fst c))) pcf_cases.
Proof.
  unfold pcf_cases.
  repeat (apply Forall_cons;
    [ cbn [fst snd source_behaviour];
      lazymatch goal with
      | |- diverges _ =>
          repeat (first [apply diverges_ifz1 | apply diverges_succ1 | apply diverges_pred1]);
          apply omega_at_diverges
      | |- _ = _ => vm_compute; reflexivity
      end
    | ]).
  apply Forall_nil.
Qed.

(** The same, as a run for the OCaml side: a value, or no value within the
    fuel where Rocq has proved divergence. *)
Example pcf_cases_evaluate :
  forallb (fun '(_, t, e) => pcf_as_expected e t) pcf_cases = true.
Proof. vm_compute. reflexivity. Qed.

Example pcf_cases_translate :
  forallb (fun '(_, t, e) => translation_as_expected e t) pcf_cases = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Failures of the translator *)

(** An ill-typed program is not translated: the PCF checker's error. *)
Example translate_ill_typed :
  translate_program (# 0 · # 1) = Err (TrIllTyped (PCF.Checker.E_NotFun (# 0) ℕ)).
Proof. reflexivity. Qed.


