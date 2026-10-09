(** * The eliminators of Void and Unit

    The two remaining checks of the minimal MLTT, in the predicative
    hierarchy with primitives:
    - Void is eliminated in a non-empty context: from [v : Void] anything
      follows, here [elimVoid (λ_. A) v : A]; the term stays neutral, as
      there is no constructor to compute on.  A scrutinee of another type
      is rejected, and in U⁻ the eliminator does not exist;
    - the dependent eliminator of Unit, with a family that uses its
      argument: [C u = elimUnit (λ_. Type₀) Bool u : Type₀].  On the
      constructor, [elimUnit C true tt : C tt], whose type computes to
      [Bool], and the term computes to [true].  On a free [u : Unit] the
      type [C u] stays neutral: there is no η for Unit, so it is not
      [Bool]. *)

From Stdlib Require Import String List Bool.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Spec Reduction Eval Bidir Check CheckSound.
From DepTypes.Configs Require Import Finite Predicative.
From DepTypes.SystemU Require Import Looping.
From DepTypes.MLTT Require Import Choose.

Open Scope string_scope.
Open Scope nterm_scope.

Definition elim_fuel : nat := 100.

(** ** Void *)

Definition void_ctx : list (string * nterm) := [("v", NVoid); ("A", Type@ 0)].

(** The constant family [λ_. A : Void → Type₀]. *)
Definition void_family : nterm := (λ "z", "A") ∷ (NVoid ~> Type@ 0).
Definition void_elim : nterm := NElimVoid void_family "v".

(** The contexts and terms below resolve. *)
Example void_resolves :
  ctx_resolves void_ctx && resolves (map fst void_ctx) void_elim &&
  resolves (map fst void_ctx) "A" && resolves (map fst void_ctx) "v" &&
  resolves ("z" :: map fst void_ctx) "A" && resolves (map fst void_ctx) (NElimVoid void_family NTt)
  = true.
Proof. vm_compute. reflexivity. Qed.

Theorem void_elim_typed :
  predicative ;; in_ctx void_ctx ⊢ term_in void_ctx void_elim ⇓ term_in void_ctx "A".
Proof. apply (accepted_check _ elim_fuel). vm_compute. reflexivity. Qed.

Example void_elim_neutral :
  normalize elim_fuel (term_in void_ctx void_elim)
  = NormalForm (ElimVoid (Lam (build ("z" :: map fst void_ctx) "A")) (term_in void_ctx "v")).
Proof. vm_compute. reflexivity. Qed.

(** [tt] is no proof of Void. *)
Example void_elim_wrong_scrutinee :
  snd (run_infer predicative elim_fuel (in_ctx void_ctx)
         (term_in void_ctx (NElimVoid void_family NTt)))
  = Rejected (EMismatch Tt Void Unit).
Proof. vm_compute. reflexivity. Qed.

(** In U⁻ the primitives are off. *)
Example void_elim_u_minus_no_primitives :
  snd (run_infer system_u_minus elim_fuel [] (ElimVoid (Lam (Srt Star)) Tt))
  = Rejected (ENoPrimitives (ElimVoid (Lam (Srt Star)) Tt)).
Proof. vm_compute. reflexivity. Qed.

(** ** Unit *)

(** [C u = elimUnit (λ_. Type₀) Bool u : Type₀]: a family that computes a
    type from its argument. *)
Definition unit_universe : nterm := (λ "w", Type@ 0) ∷ (NUnit ~> Type@ 1).
Definition unit_family : nterm := (λ "u", NElimUnit unit_universe NBool "u") ∷ (NUnit ~> Type@ 0).
Definition unit_elim (u : nterm) : nterm := NElimUnit unit_family NTrue u.

Example unit_resolves :
  resolves [] (unit_elim NTt) && resolves [] unit_family && ctx_resolves [("u", NUnit)] &&
  resolves ["u"] (unit_elim "u") = true.
Proof. vm_compute. reflexivity. Qed.

Theorem unit_elim_typed : predicative ;; [] ⊢ build [] (unit_elim NTt) ⇓ Bool.
Proof. apply (accepted_check _ elim_fuel). vm_compute. reflexivity. Qed.

(** Its type is [C tt], which computes to [Bool]. *)
Example unit_elim_synthesizes :
  snd (run_infer predicative elim_fuel [] (build [] (unit_elim NTt)))
  = Accepted (App (build [] unit_family) Tt).
Proof. vm_compute. reflexivity. Qed.

Example unit_family_tt_computes :
  normalize elim_fuel (App (build [] unit_family) Tt) = NormalForm Bool.
Proof. vm_compute. reflexivity. Qed.

(** On the constructor the eliminator computes: [elimUnit C true tt ⇝ true]. *)
Example unit_elim_computes : normalize elim_fuel (build [] (unit_elim NTt)) = NormalForm BTrue.
Proof. vm_compute. reflexivity. Qed.

(** On a free [u : Unit] the type [C u] stays neutral: without η for Unit
    it is not [Bool]. *)
Definition unit_ctx : list (string * nterm) := [("u", NUnit)].

Example unit_elim_open_synthesizes :
  snd (run_infer predicative elim_fuel (in_ctx unit_ctx) (term_in unit_ctx (unit_elim "u")))
  = Accepted (App (build [] unit_family) (Var 0)).
Proof. vm_compute. reflexivity. Qed.

Example unit_family_open_neutral :
  normalize elim_fuel (App (build [] unit_family) (Var 0))
  = NormalForm (ElimUnit (Lam (Srt (Univ 0))) Bool (Var 0)).
Proof. vm_compute. reflexivity. Qed.

Example unit_elim_open_not_bool :
  snd (run_check predicative elim_fuel (in_ctx unit_ctx) (term_in unit_ctx (unit_elim "u")) Bool)
  = Rejected (EMismatch (term_in unit_ctx (unit_elim "u")) Bool (App (build [] unit_family) (Var 0))).
Proof. vm_compute. reflexivity. Qed.
