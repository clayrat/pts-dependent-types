(** * match and fix in the kernel

    The primitive [match] and [fix] of PTS.Syntax on the hand-written
    signatures of ℕ (MLTT/Constants.v) and of vectors and W-types
    (MLTT/Families.v), with [plus] added as a δ-constant:

    - [nat_rect] written with [fix] and [match] checks against the type
      of [elimNat[j]] for several [j], and each of the two satisfies its
      own ι-equations on open terms.  The two implementations are not
      compared on a free argument: they are different terms, and only
      their equations are definitional;
    - [plus], [append] on vectors, whose index is computed by [plus],
      and [copy] on W, with the recursive call under a λ, are written
      directly and compute;
    - a [match] on a free variable and a [fix] on a free argument stay
      as they are;
    - the refusals: a missing or a repeated branch, a wrong motive, a
      motive into a sort the category of the type does not allow, a
      scrutinee of another type, a structural position past the
      telescope of the type, a structural argument that is not of an
      inductive type, and a body without enough λ;
    - the call-by-value evaluator [eval_src] runs the same programs to
      values and gets stuck on a free variable.

    Every [fix] here passes the guard of PTS/Guard.v, which refuses
    [fix f n := f n]: its call is on the structural argument itself.  The
    examples of the guard are in CIC/GuardExamples.v. *)

From Stdlib Require Import String List Bool.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Spec Signature Reduction Eval EvalSrc Guard Bidir Check CheckSound Build Runs.
From DepTypes.Configs Require Import Predicative.
From DepTypes.MLTT Require Import Constants Families.

Open Scope string_scope.
Open Scope nterm_scope.

Definition match_fuel : nat := 300.

(** ** nat_rect by fix and match *)

(** The type of [elimNat[j]] (MLTT/Constants.v). *)
Definition nat_rect_ty (j : nat) : nterm := elim_nat_ty_at j.

(** [fix F (P z s n) {struct n} := match n return P n with zero => z | succ m => s m (F P z s m)]. *)
Definition nat_rect (j : nat) : nterm :=
  NFix "F" (nat_rect_ty j) 3
    (λ "P", λ "z", λ "s", λ "n",
       NCase "Nat" (Univ j) (λ "m", "P" "m") "n"
         [NVar "z"; λ "m", "s" "m" ("F" "P" "z" "s" "m")]).

Example nat_rect_ty_is_elim_nat_ty : nat_rect_ty 0 = elim_nat_ty.
Proof. reflexivity. Qed.

(** [nat_rect] at the levels 0, 1 and 2 synthesizes its annotation, the
    type of [elimNat[j]]. *)
Example nat_rect_typed :
  map (fun j => infers predicative sg_nat match_fuel [] (nat_rect j)) [0; 1; 2]
  = map (fun j => Accepted (build [] (nat_rect_ty j))) [0; 1; 2].
Proof. vm_compute. reflexivity. Qed.

Definition rect_ctx (j : nat) : list (string * nterm) := iota_ctx_at j.

(** Each implementation satisfies its own ι-equations on open terms. *)
Example nat_rect_equations :
  forallb (fun j =>
    converts sg_nat match_fuel (rect_ctx j) (nat_rect j "P" "z" "s" zero) "z" &&
    converts sg_nat match_fuel (rect_ctx j) (nat_rect j "P" "z" "s" (succ "n")) ("s" "n" (nat_rect j "P" "z" "s" "n")))
    [0; 1] = true.
Proof. vm_compute. reflexivity. Qed.

Example elim_nat_equations :
  converts sg_nat match_fuel (rect_ctx 0) (elim_nat "P" "z" "s" zero) "z" &&
  converts sg_nat match_fuel (rect_ctx 0) (elim_nat "P" "z" "s" (succ "n")) ("s" "n" (elim_nat "P" "z" "s" "n")) = true.
Proof. vm_compute. reflexivity. Qed.

(** On a free [n], the fix does not unfold and the match does not
    reduce: both are their own normal forms.  The match synthesizes the
    motive applied to the scrutinee, [(λm. P m) n]. *)
Definition open_match : nterm :=
  NCase "Nat" (Univ 0) (λ "m", "P" "m") "n" [NVar "z"; λ "m", "s" "m" (nat_rect 0 "P" "z" "s" "m")].

Example open_terms_neutral :
  normalize sg_nat match_fuel (term_in (rect_ctx 0) (nat_rect 0 "P" "z" "s" "n"))
  = NormalForm (term_in (rect_ctx 0) (nat_rect 0 "P" "z" "s" "n")) /\
  normalize sg_nat match_fuel (term_in (rect_ctx 0) open_match)
  = NormalForm (term_in (rect_ctx 0) open_match) /\
  infers predicative sg_nat match_fuel (rect_ctx 0) open_match = Accepted (term_in (rect_ctx 0) ((λ "m", "P" "m") "n")).
Proof. vm_compute. repeat split. Qed.

(** ** plus, append, copy *)

Definition plus_fix : nterm :=
  NFix "plus" (Nat ~> Nat ~> Nat) 0
    (λ "n", λ "m", NCase "Nat" (Univ 0) (λ "_", Nat) "n" [NVar "m"; λ "k", succ ("plus" "k" "m")]).

Definition plus : nterm := NConst (Def "plus").

Definition match_entries : list entry :=
  EDef "plus" (build [] (Nat ~> Nat ~> Nat)) (build [] plus_fix) :: family_entries.

Definition sg_match : signature := {| sig_entries := match_entries; sig_wf := eq_refl |}.

Fixpoint nat_numeral (k : nat) : nterm :=
  match k with
  | O => zero
  | S k' => succ (nat_numeral k')
  end.

Example plus_typed_and_computes :
  infers predicative sg_nat match_fuel [] plus_fix = Accepted (build [] (Nat ~> Nat ~> Nat)) /\
  normalize sg_match match_fuel (build [] (plus (nat_numeral 2) (nat_numeral 3)))
  = NormalForm (build [] (nat_numeral 5)).
Proof. vm_compute. split; reflexivity. Qed.

(** [append : ΠA n m. Vec A n → Vec A m → Vec A (plus n m)], by
    recursion on the first vector.  The branch [nil] has the type
    [Vec A (plus zero m)], which computes to [Vec A m]; the branch [cons]
    has [Vec A (plus (succ k) m)], which computes to
    [Vec A (succ (plus k m))]. *)
Definition append_ty : nterm :=
  Π "A" : Type@ 0, Π "n" : Nat, Π "m" : Nat, Vec "A" "n" ~> Vec "A" "m" ~> Vec "A" (plus "n" "m").

Definition append : nterm :=
  NFix "app" append_ty 3
    (λ "A", λ "n", λ "m", λ "xs", λ "ys",
       NCase "Vec" (Univ 0) (λ "k", λ "_", Vec "A" (plus "k" "m")) "xs"
         [NVar "ys"; λ "k", λ "x", λ "xs'", vcons "A" (plus "k" "m") "x" ("app" "A" "k" "m" "xs'" "ys")]).

Definition one_true : nterm := vcons NBool zero NTrue (vnil NBool).
Definition one_false : nterm := vcons NBool zero NFalse (vnil NBool).

Example append_typed_and_computes :
  infers predicative sg_match match_fuel [] append = Accepted (build [] append_ty) /\
  normalize sg_match match_fuel (build [] (append NBool (nat_numeral 1) (nat_numeral 1) one_true one_false))
  = NormalForm (build [] (vcons NBool (nat_numeral 1) NTrue (vcons NBool zero NFalse (vnil NBool)))).
Proof. vm_compute. split; reflexivity. Qed.

(** [copy] on W rebuilds a tree; the recursive call is under the λ of
    the new function of children. *)
Definition copy_ty : nterm := Π "A" : Type@ 0, Π "B" : ("A" ~> Type@ 0), W "A" "B" ~> W "A" "B".

Definition copy : nterm :=
  NFix "copy" copy_ty 2
    (λ "A", λ "B", λ "w",
       NCase "W" (Univ 0) (λ "_", W "A" "B") "w"
         [λ "a", λ "f", sup "A" "B" "a" (λ "b", "copy" "A" "B" ("f" "b"))]).

Example copy_typed_and_computes :
  infers predicative sg_families match_fuel [] copy = Accepted (build [] copy_ty) /\
  normalize sg_families match_fuel (build [] (to_nat (copy NBool positions (succ_w (succ_w zero_w)))))
  = NormalForm (build [] (nat_numeral 2)).
Proof. vm_compute. split; reflexivity. Qed.

(** ** Conversion with lazy δ

    [plus] is a δ-constant of [sg_match].  The two sides are compared
    with it folded first, and unfolded only where they differ: a β-redex
    of a motive meets the expected type with [plus] still folded, and
    the reported common form keeps it so; [plus (succ k) m] against
    [succ (plus k m)] needs [plus] unfolded; [plus k m] against
    [plus m k] stays different. *)
Definition plus_ctx : list (string * nterm) := [("m", Nat); ("k", Nat)].

Example convert_lazy_delta :
  convert sg_match match_fuel
    (term_in plus_ctx ((λ "x", Vec NBool (plus "x" "m")) "k")) (term_in plus_ctx (Vec NBool (plus "k" "m")))
  = ConvEqual (term_in plus_ctx (Vec NBool (plus "k" "m"))) /\
  converts sg_match match_fuel plus_ctx (plus (succ "k") "m") (succ (plus "k" "m")) = true /\
  convert sg_match match_fuel (term_in plus_ctx (plus "k" "m")) (term_in plus_ctx (plus "m" "k"))
  = ConvDifferent.
Proof. vm_compute. repeat split. Qed.

(** ** Refusals *)

Definition rect_body (bs : list nterm) : nterm :=
  NFix "F" (nat_rect_ty 0) 3 (λ "P", λ "z", λ "s", λ "n", NCase "Nat" (Univ 0) (λ "m", "P" "m") "n" bs).

Definition succ_branch : nterm := λ "m", "s" "m" ("F" "P" "z" "s" "m").

(** One branch per constructor: a missing branch and a repeated one show
    as a wrong number of branches. *)
Example branch_count_refused :
  option_map (fun e => match e with EBranchCount _ k n => Some (k, n) | _ => None end)
    (refusal (infers predicative sg_nat match_fuel [] (rect_body [NVar "z"]))) = Some (Some (2, 1)) /\
  option_map (fun e => match e with EBranchCount _ k n => Some (k, n) | _ => None end)
    (refusal (infers predicative sg_nat match_fuel [] (rect_body [NVar "z"; succ_branch; succ_branch]))) = Some (Some (2, 3)).
Proof. vm_compute. split; reflexivity. Qed.

(** A wrong motive: the motive is into Type₁ while the match says Type₀. *)
Definition wrong_motive : nterm :=
  NFix "F" (Π "P" : (Nat ~> Type@ 1), "P" zero ~> (Π "n" : Nat, "P" "n" ~> "P" (succ "n")) ~> Π "n" : Nat, "P" "n") 3
    (λ "P", λ "z", λ "s", λ "n",
       NCase "Nat" (Univ 0) (λ "m", "P" "m") "n" [NVar "z"; λ "m", "s" "m" ("F" "P" "z" "s" "m")]).

Example wrong_motive_refused :
  match refusal (infers predicative sg_nat match_fuel [] wrong_motive) with
  | Some (EMismatch _ _ _) => true
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** A scrutinee of another type. *)
Example scrutinee_refused :
  refusal (infers predicative sg_nat match_fuel [] (NCase "Nat" (Univ 0) (λ "m", Nat) NTrue [zero; λ "m", "m"]))
  = Some (ENotInductive BTrue "Nat" Bool).
Proof. vm_compute. reflexivity. Qed.

(** A propositional boolean, eliminable into Prop only: a match on it
    into Type₀ is refused by its category, the same match into Prop is
    accepted. *)
Definition boolp_desc : ind_desc := {|
  ind_name := "BoolP"; ind_params := []; ind_indices := []; ind_sort := Prp; ind_elim := PropOnly;
  ind_ctors := [ {| ctor_name := "trueP"; ctor_fields := []; ctor_indices := [] |};
                 {| ctor_name := "falseP"; ctor_fields := []; ctor_indices := [] |} ] |}.

Definition sg_boolp : signature := {| sig_entries := [EInd boolp_desc]; sig_wf := eq_refl |}.

Definition trueP : nterm := NConst (Ctor "BoolP" "trueP").

Definition match_boolp (s : sort) (T : nterm) (a b : nterm) : nterm :=
  NCase "BoolP" s (λ "_", T) trueP [a; b].

Example elim_sort_checked :
  infers predicative_prop sg_boolp match_fuel [("a", NVar "A"); ("A", NSrt Prp)] (match_boolp Prp "A" "a" "a")
  = Accepted (term_in [("a", NVar "A"); ("A", NSrt Prp)] ((λ "_", "A") trueP)) /\
  refusal (infers predicative_prop sg_boolp match_fuel [] (match_boolp (Univ 0) NBool NTrue NFalse))
  = Some (EElimSort "BoolP" (Univ 0)).
Proof. vm_compute. split; reflexivity. Qed.

(** A structural position past the telescope, a structural argument
    that is not of an inductive type, and a body without enough λ. *)
Example fix_refusals :
  refusal (infers predicative sg_nat match_fuel [] (NFix "f" (Nat ~> Nat) 1 (λ "n", λ "m", "m")))
  = Some (ENoStructArg (build [] (NFix "f" (Nat ~> Nat) 1 (λ "n", λ "m", "m"))) 1 (build [] Nat)) /\
  refusal (infers predicative sg_nat match_fuel [] (NFix "f" (NBool ~> NBool) 0 (λ "b", "b")))
  = Some (EStructNotInductive (build [] (NFix "f" (NBool ~> NBool) 0 (λ "b", "b"))) 0 Bool) /\
  refusal (infers predicative sg_nat match_fuel [] (NFix "f" (Nat ~> Nat) 0 "f"))
  = Some (EFixBody (build [] (NFix "f" (Nat ~> Nat) 0 "f")) 0).
Proof. vm_compute. repeat split. Qed.

(** ** The guard *)

(** [fix f n := f n] is typed, and refused by the guard: applied to a
    constructor, it would unfold forever. *)
Definition loop : nterm := NFix "f" (Nat ~> Nat) 0 (λ "n", "f" "n").

Example loop_refused :
  refusal (infers predicative sg_nat match_fuel [] loop)
  = Some (ENotGuarded (build [] loop) (GNotSubterm (App (Var 1) (Var 0)) (Var 0))) /\
  match normalize sg_nat match_fuel (build [] (loop zero)) with OutOfFuel _ => true | _ => false end = true.
Proof. vm_compute. split; reflexivity. Qed.

(** ** Call-by-value evaluation

    The arguments of a constructor are evaluated too: the index
    [plus zero 1] of the vector is a value only as [1]. *)

(** An eliminator instance computes only with active rules, and a spine
    short of its arity is a value only then: the arity of a value is the
    arity of the contraction.  Without them the instance is an ordinary
    constant, whose spines are neutral: applied, it is stuck. *)
Example eval_src_activity :
  eval_src sg_nat match_fuel (build [] (elim_nat (λ "_", Nat) zero))
  = CbvValue (build [] (elim_nat (λ "_", Nat) zero)) /\
  eval_src sg_nat match_fuel (build [] (elim_nat (λ "_", Nat) zero (λ "m", λ "r", "r") zero))
  = CbvValue (build [] zero) /\
  eval_src sg_nat_inactive match_fuel (build [] (elim_nat (λ "_", Nat) zero))
  = CbvStuck (build [] (elim_nat (λ "_", Nat))) /\
  eval_src sg_nat_inactive match_fuel (build [] (elim_nat (λ "_", Nat) zero (λ "m", λ "r", "r") zero))
  = CbvStuck (build [] (elim_nat (λ "_", Nat))).
Proof. vm_compute. repeat split. Qed.

Example eval_src_runs :
  eval_src sg_match match_fuel (build [] (plus (nat_numeral 2) (nat_numeral 3))) = CbvValue (build [] (nat_numeral 5)) /\
  eval_src sg_match match_fuel (build [] (append NBool (nat_numeral 1) (nat_numeral 1) one_true one_false))
  = CbvValue (build [] (vcons NBool (nat_numeral 1) NTrue (vcons NBool zero NFalse (vnil NBool)))) /\
  eval_src sg_nat match_fuel (term_in (rect_ctx 0) open_match) = CbvStuck (Var 0).
Proof. vm_compute. repeat split. Qed.
