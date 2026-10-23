(** * Constants of a signature: ℕ by hand

    A signature written out by hand, as the lecture on inductive types will
    generate it: ℕ with the constructors [zero] and [succ], the instance
    [elimNat[0]] of its eliminator with active ι-rules, and the δ-constant
    [double = λn. elimNat (λ_. Nat) zero (λ_ r. succ (succ r)) n].  The
    type of the instance is written here, not generated; the kernel only
    checks it like any other term.

    - Constants are typed from the signature: [succ (succ zero) : Nat],
      [elimNat[0]] at its type, [double] at [Nat → Nat].  The body of
      [double] checks in the signature of ℕ and [elimNat[0]] alone, where
      a body mentioning [double] is rejected.
    - δ unfolds a δ-constant as a step of its own, and ι computes a full
      spine on a constructor in the order of [nat_rect]: on [succ m] the
      method gets [m] and then [elimNat P z s m].  So [double 1] reaches
      [succ (succ zero)].
    - The ι-rule holds on open terms:
      [elimNat P z s (succ n) ≡ s n (elimNat P z s n)].
    - The object of a full spine is evaluated first.
    - On a free [n : Nat] the spine is neutral at the type [P n].
    - An instance registered without the flag of active rules is an
      ordinary constant: its spines stay neutral.
    - A constant missing from the signature, or any constant in U⁻, is
      rejected.
    - A signature guarantees closedness, not types, and the checker trusts
      the types of constants: with [c : (tt → tt) → Bool] it accepts
      [c (λx. x)], and with the δ-constant [f := tt] at [Bool → Bool] it
      accepts [f true : Bool], which normal order takes to the stuck
      [tt true].  The declarative obligations of Contracts.v therefore
      assume a type-correct signature. *)

From Stdlib Require Import String List Bool.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Spec Signature Reduction Eval Bidir Check CheckSound.
From DepTypes.Configs Require Import Finite Predicative.
From DepTypes.SystemU Require Import Looping.
From DepTypes.MLTT Require Import Choose.

Open Scope string_scope.
Open Scope nterm_scope.

Definition const_fuel : nat := 100.

(** ** The signature *)

Definition nat_desc : ind_desc := {|
  ind_name := "Nat"; ind_params := []; ind_indices := []; ind_level := 0;
  ind_ctors := [ {| ctor_name := "zero"; ctor_fields := []; ctor_indices := [] |};
                 {| ctor_name := "succ"; ctor_fields := [FRec [] []]; ctor_indices := [] |} ] |}.

Definition Nat : nterm := NConst (Ind "Nat").
Definition zero : nterm := NConst (Ctor "Nat" "zero").
Definition succ : nterm := NConst (Ctor "Nat" "succ").
Definition elim_nat : nterm := NConst (Elim "Nat" 0).
Definition double : nterm := NConst (Def "double").

Definition elim_nat_ty : nterm :=
  Π "P" : (Nat ~> Type@ 0), "P" zero ~> (Π "n" : Nat, "P" "n" ~> "P" (succ "n")) ~> Π "n" : Nat, "P" "n".

Definition const_nat : nterm := (λ "_", Nat) ∷ (Nat ~> Type@ 0).
Definition double_body : nterm := λ "n", elim_nat const_nat zero (λ "m", λ "r", succ (succ "r")) "n".

(** ℕ and its eliminator: the signature in which the body of [double] is
    checked, before [double] is registered. *)
Definition base_entries (active : bool) : list entry :=
  [EElim "Nat" 0 (build [] elim_nat_ty) active; EInd nat_desc].

Definition nat_entries (active : bool) : list entry :=
  EDef "double" (build [] (Nat ~> Nat)) (build [] double_body) :: base_entries active.

Definition sg_nat_base : signature := {| sig_entries := base_entries true; sig_wf := eq_refl |}.
Definition sg_nat : signature := {| sig_entries := nat_entries true; sig_wf := eq_refl |}.
Definition sg_nat_inactive : signature := {| sig_entries := nat_entries false; sig_wf := eq_refl |}.

Lemma accepted_check_in : forall S sg fuel G t A,
  snd (run_check S sg fuel G t A) = Accepted tt -> chk S sg G t A.
Proof. intros S sg fuel G t A H. exact (proj2 (proj2 (run_check_sound S sg fuel G t A tt H))). Qed.

(** [sig_add] checks only the new entry: adding [double] to the base gives
    the entries of [sg_nat], and an entry with a free variable is refused. *)
Example sig_add_double :
  option_map sig_entries
    (sig_add sg_nat_base (EDef "double" (build [] (Nat ~> Nat)) (build [] double_body)))
  = Some (nat_entries true).
Proof. vm_compute. reflexivity. Qed.

Example sig_add_open_refused : sig_add sg_nat_base (EDef "bad" (Var 0) Tt) = None.
Proof. vm_compute. reflexivity. Qed.

(** ** Types from the signature *)

Example succ_type :
  sig_type sg_nat (Ctor "Nat" "succ") = Some (Pi (Const (Ind "Nat")) (Const (Ind "Nat"))).
Proof. vm_compute. reflexivity. Qed.

Theorem two_typed : chk predicative sg_nat [] (build [] (succ (succ zero))) (build [] Nat).
Proof. apply (accepted_check_in _ _ const_fuel). vm_compute. reflexivity. Qed.

Theorem elim_nat_typed : chk predicative sg_nat [] (build [] elim_nat) (build [] elim_nat_ty).
Proof. apply (accepted_check_in _ _ const_fuel). vm_compute. reflexivity. Qed.

(** The body of [double] checks in the signature without [double]... *)
Theorem double_body_typed :
  chk predicative sg_nat_base [] (build [] double_body) (build [] (Nat ~> Nat)).
Proof. apply (accepted_check_in _ _ const_fuel). vm_compute. reflexivity. Qed.

(** ... where a body that mentions [double] itself is rejected. *)
Example self_reference_rejected :
  snd (run_check predicative sg_nat_base const_fuel [] (build [] (λ "n", double "n")) (build [] (Nat ~> Nat)))
  = Rejected (EUnknownConst (Def "double")).
Proof. vm_compute. reflexivity. Qed.

Theorem double_one_typed : chk predicative sg_nat [] (build [] (double (succ zero))) (build [] Nat).
Proof. apply (accepted_check_in _ _ const_fuel). vm_compute. reflexivity. Qed.

(** ** δ and ι *)

Example double_one_computes :
  normalize sg_nat const_fuel (build [] (double (succ zero))) = NormalForm (build [] (succ (succ zero))).
Proof. vm_compute. reflexivity. Qed.

(** δ is the first step of its own. *)
Example delta_step :
  classify sg_nat (build [] (double (succ zero))) =
  Steps (App (build [] (λ "n", elim_nat const_nat zero (λ "m", λ "r", succ (succ "r")) "n"))
             (build [] (succ zero))).
Proof. vm_compute. reflexivity. Qed.

(** The ι-rule on open terms: [P z s n] are free. *)
Definition iota_ctx : list (string * nterm) :=
  [("n", Nat); ("s", Π "n" : Nat, "P" "n" ~> "P" (succ "n")); ("z", "P" zero); ("P", Nat ~> Type@ 0)].

Example iota_open :
  exists v, convert sg_nat const_fuel
    (term_in iota_ctx (elim_nat "P" "z" "s" (succ "n")))
    (term_in iota_ctx ("s" "n" (elim_nat "P" "z" "s" "n"))) = ConvEqual v.
Proof. eexists. vm_compute. reflexivity. Qed.

(** The object of a full spine is evaluated first: [double zero] unfolds
    while the annotation of the motive is still there. *)
Example object_first :
  classify sg_nat (build [] (elim_nat const_nat zero (λ "m", λ "r", "r") (double zero))) =
  Steps (App (build [] (elim_nat const_nat zero (λ "m", λ "r", "r")))
             (App (build [] (λ "n", elim_nat const_nat zero (λ "m", λ "r", succ (succ "r")) "n"))
                  (build [] zero))).
Proof. vm_compute. reflexivity. Qed.

(** On a free [n : Nat] the spine is neutral at [P n]. *)
Example open_spine :
  snd (run_infer predicative sg_nat const_fuel [build [] Nat]
         (App (build [] (elim_nat const_nat zero (λ "m", λ "r", "r"))) (Var 0)))
  = Accepted (App (build [] const_nat) (Var 0)) /\
  normalize sg_nat const_fuel (App (build [] (elim_nat const_nat zero (λ "m", λ "r", "r"))) (Var 0))
  = NormalForm (App (App (App (App (Const (Elim "Nat" 0)) (Lam (Const (Ind "Nat"))))
                                (Const (Ctor "Nat" "zero")))
                           (Lam (Lam (Var 0))))
                      (Var 0)).
Proof. split; vm_compute; reflexivity. Qed.

(** Without the flag the rules take no part: after δ the spine is
    neutral. *)
Example inactive_neutral :
  normalize sg_nat_inactive const_fuel (build [] (double (succ zero)))
  = NormalForm (App (App (App (App (Const (Elim "Nat" 0)) (Lam (Const (Ind "Nat"))))
                                (Const (Ctor "Nat" "zero")))
                           (Lam (Lam (App (Const (Ctor "Nat" "succ"))
                                          (App (Const (Ctor "Nat" "succ")) (Var 0))))))
                      (build [] (succ zero))).
Proof. vm_compute. reflexivity. Qed.

(** ** Rejections *)

Example unknown_constant :
  snd (run_infer predicative sg_nat const_fuel [] (Const (Ind "Bool2")))
  = Rejected (EUnknownConst (Ind "Bool2")).
Proof. vm_compute. reflexivity. Qed.

Example not_in_empty_signature :
  snd (run_infer predicative ∅ const_fuel [] (build [] zero))
  = Rejected (EUnknownConst (Ctor "Nat" "zero")).
Proof. vm_compute. reflexivity. Qed.

Example constants_off_in_u_minus :
  snd (run_infer system_u_minus sg_nat const_fuel [] (build [] zero))
  = Rejected (ENoDecls (Const (Ctor "Nat" "zero"))).
Proof. vm_compute. reflexivity. Qed.

(** ** Signatures without types *)

Definition sg_untyped : signature := {|
  sig_entries := [EDef "c" (Pi (Pi Tt Tt) Bool) (Lam BTrue); EDef "f" (Pi Bool Bool) Tt];
  sig_wf := eq_refl |}.

(** [tt → tt] is no type, yet the λ checks against it. *)
Example untyped_constant_accepted :
  snd (run_infer predicative sg_untyped const_fuel [] (App (Const (Def "c")) (Lam (Var 0))))
  = Accepted Bool.
Proof. vm_compute. reflexivity. Qed.

Example untyped_body_gets_stuck :
  snd (run_infer predicative sg_untyped const_fuel [] (App (Const (Def "f")) BTrue)) = Accepted Bool /\
  normalize sg_untyped const_fuel (App (Const (Def "f")) BTrue) = StuckTerm (App Tt BTrue).
Proof. split; vm_compute; reflexivity. Qed.
