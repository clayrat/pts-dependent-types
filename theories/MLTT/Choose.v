(** * [choose]: a type computed from a boolean

    The main demonstration of the minimal MLTT: in the context
    [A B : Type₀],

      choose : Πb:Bool. A → B → (if b then A else B)
      choose = λb x y. elimBool (λb'. if b' then A else B) x y b

    where [if b then A else B] is [elimBool (λ_. Type₀) A B b]: the family
    [λ_. Type₀ : Bool → Type₁] returns a universe, so this eliminator
    computes a type from a term — large elimination.  The result family
    of [choose] itself lands in Type₀ and gives each branch its own type.

    Checked in the predicative hierarchy with primitives:
    - [choose] has its type;
    - [choose true a c] checks against [A] (its type computes to [A]) and
      evaluates to [a]; [choose false a c] checks against [B] and
      evaluates to [c];
    - with a free [b : Bool] the type [if b then A else B] stays neutral,
      and checking against [A] fails;
    - swapping the branches is rejected at the first branch, and a type
      family declared in Type₀ instead of Type₁ is rejected for its
      level. *)

From Stdlib Require Import String List Bool.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Spec Reduction Eval Bidir Check CheckSound.
From DepTypes.Configs Require Import Predicative.
From DepTypes.SystemU Require Import Looping.

Open Scope string_scope.
Open Scope nterm_scope.

(** ** The terms *)

(** [λ_. Type₀ : Bool → Type₁], and [if b then A else B] with it. *)
Definition universe_family : nterm := (λ "b", Type@ 0) ∷ (NBool ~> Type@ 1).
Definition cond (b : nterm) : nterm := NElimBool universe_family "A" "B" b.

Definition choose_ty : nterm := Π "b" : NBool, "A" ~> "B" ~> cond "b".

(** The result family of [choose], into Type₀. *)
Definition choose_family : nterm := (λ "b", cond "b") ∷ (NBool ~> Type@ 0).

Definition choose : nterm :=
  (λ "b", λ "x", λ "y", NElimBool choose_family "x" "y" "b") ∷ choose_ty.

(** ** Contexts *)

Definition types_ctx : list (string * nterm) := [("B", Type@ 0); ("A", Type@ 0)].
Definition args_ctx : list (string * nterm) := [("c", NVar "B"); ("a", NVar "A")] ++ types_ctx.
Definition open_ctx : list (string * nterm) := ("b", NBool) :: args_ctx.

(** A named context and a term in it, as de Bruijn terms. *)
Definition in_ctx (g : list (string * nterm)) : ctx :=
  match resolve_ctx g with
  | Ok (_, G) => G
  | Err _ => []
  end.

Definition term_in (g : list (string * nterm)) (t : nterm) : term := build (map fst g) t.

Definition choose_at (b : nterm) : nterm := choose b "a" "c".

Definition choose_fuel : nat := 100.

(** The contexts and terms below resolve: [in_ctx] and [term_in] never
    fall back to their default values. *)
Example choose_contexts_resolve :
  forallb ctx_resolves [types_ctx; args_ctx; open_ctx] = true.
Proof. vm_compute. reflexivity. Qed.

Example choose_terms_resolve :
  forallb (fun '(g, t) => resolves (map fst g) t)
    [ (types_ctx, choose); (types_ctx, choose_ty);
      (args_ctx, choose_at NTrue); (args_ctx, choose_at NFalse);
      (args_ctx, cond NTrue); (args_ctx, NVar "A"); (args_ctx, NVar "B");
      (args_ctx, NVar "a"); (args_ctx, NVar "c");
      (open_ctx, choose_at "b"); (open_ctx, cond "b"); (open_ctx, NVar "A");
      (open_ctx, NVar "B"); (open_ctx, NVar "b") ] = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Typing and evaluation *)

Lemma accepted_check : forall S fuel G t A,
  snd (run_check S fuel G t A) = Accepted tt -> S ;; G ⊢ t ⇓ A.
Proof. intros S fuel G t A H. exact (proj2 (proj2 (run_check_sound S fuel G t A tt H))). Qed.

Theorem choose_typed :
  predicative ;; in_ctx types_ctx ⊢ term_in types_ctx choose ⇓ term_in types_ctx choose_ty.
Proof. apply (accepted_check _ choose_fuel). vm_compute. reflexivity. Qed.

(** [choose true a c : A]: the type [if true then A else B] computes to
    [A]. *)
Theorem choose_true_typed :
  predicative ;; in_ctx args_ctx ⊢ term_in args_ctx (choose_at NTrue) ⇓ term_in args_ctx "A".
Proof. apply (accepted_check _ choose_fuel). vm_compute. reflexivity. Qed.

Theorem choose_false_typed :
  predicative ;; in_ctx args_ctx ⊢ term_in args_ctx (choose_at NFalse) ⇓ term_in args_ctx "B".
Proof. apply (accepted_check _ choose_fuel). vm_compute. reflexivity. Qed.

(** The type synthesized for [choose true a c] is [if true then A else B]
    itself; conversion computes it to [A]. *)
Example choose_true_synthesizes :
  snd (run_infer predicative choose_fuel (in_ctx args_ctx) (term_in args_ctx (choose_at NTrue)))
  = Accepted (term_in args_ctx (cond NTrue)).
Proof. vm_compute. reflexivity. Qed.

Example cond_true_computes :
  normalize choose_fuel (term_in args_ctx (cond NTrue)) = NormalForm (term_in args_ctx "A").
Proof. vm_compute. reflexivity. Qed.

(** [choose true a c] evaluates to [a], [choose false a c] to [c]. *)
Example choose_evaluates :
  normalize choose_fuel (term_in args_ctx (choose_at NTrue)) = NormalForm (term_in args_ctx "a") /\
  normalize choose_fuel (term_in args_ctx (choose_at NFalse)) = NormalForm (term_in args_ctx "c").
Proof. split; vm_compute; reflexivity. Qed.

(** ** A free boolean *)

(** With [b : Bool] free, [choose b a c] still synthesizes [if b then A
    else B], whose normal form is a neutral eliminator, and it does not
    check against [A]. *)
Example choose_open_synthesizes :
  snd (run_infer predicative choose_fuel (in_ctx open_ctx) (term_in open_ctx (choose_at "b")))
  = Accepted (term_in open_ctx (cond "b")).
Proof. vm_compute. reflexivity. Qed.

Example cond_open_neutral :
  normalize choose_fuel (term_in open_ctx (cond "b"))
  = NormalForm (ElimBool (Lam (Srt (Univ 0))) (term_in open_ctx "A") (term_in open_ctx "B")
                         (term_in open_ctx "b")).
Proof. vm_compute. reflexivity. Qed.

Example choose_open_not_A :
  snd (run_check predicative choose_fuel (in_ctx open_ctx) (term_in open_ctx (choose_at "b"))
         (term_in open_ctx "A"))
  = Rejected (EMismatch (term_in open_ctx (choose_at "b")) (term_in open_ctx "A")
                        (term_in open_ctx (cond "b"))).
Proof. vm_compute. reflexivity. Qed.

(** ** Errors *)

(** Swapping the branches: [y : B] is offered where the family asks for
    [if true then A else B], which computes to [A]. *)
Definition choose_swapped : nterm :=
  (λ "b", λ "x", λ "y", NElimBool choose_family "y" "x" "b") ∷ choose_ty.

Definition body_names : list string := ["y"; "x"; "b"; "B"; "A"].

Example swapped_terms_resolve :
  resolves (map fst types_ctx) choose_swapped && resolves body_names "y" &&
  resolves body_names (choose_family NTrue) && resolves body_names "B" = true.
Proof. vm_compute. reflexivity. Qed.

Example choose_swapped_rejected :
  snd (run_check predicative choose_fuel (in_ctx types_ctx)
         (term_in types_ctx choose_swapped) (term_in types_ctx choose_ty))
  = Rejected (EMismatch (build body_names "y") (build body_names (choose_family NTrue))
                        (build body_names "B")).
Proof. vm_compute. reflexivity. Qed.

(** A type family declared one universe too low: [λ_. Type₀] lives in
    [Bool → Type₁], not in [Bool → Type₀]. *)
Definition low_family : nterm := (λ "b", Type@ 0) ∷ (NBool ~> Type@ 0).

Example low_family_resolves : resolves [] low_family = true.
Proof. reflexivity. Qed.

Example low_family_rejected :
  snd (run_infer predicative choose_fuel [] (build [] low_family))
  = Rejected (EMismatch (Srt (Univ 0)) (Srt (Univ 0)) (Srt (Univ 1))).
Proof. vm_compute. reflexivity. Qed.
