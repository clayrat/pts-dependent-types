(** * The predicative hierarchy with MLTT primitives

    Sorts Type_0, Type_1, ...; axioms [Type_i : Type_(i+1)] and rules
    [(Type_i, Type_j, Type_(max i j))].  Levels are explicit: no
    cumulativity and no level inference.  Void, Unit and Bool live in
    Type_0.

    [pure_predicative] is the same hierarchy without the primitives; it
    is the target of the renaming [u_to_univ] of the sorts of U⁻, under
    which the looping combinator must be rejected. *)

From Stdlib Require Import Arith.
From DepTypes.PTS Require Import Syntax Spec.

Definition is_univ (s : sort) : bool :=
  match s with
  | Univ _ => true
  | _ => false
  end.

Definition univ_axiom (s : sort) : option sort :=
  match s with
  | Univ i => Some (Univ (S i))
  | _ => None
  end.

Definition univ_rule (s1 s2 : sort) : option sort :=
  match s1, s2 with
  | Univ i, Univ j => Some (Univ (Nat.max i j))
  | _, _ => None
  end.

Definition predicative_table : pts_table := {|
  spec_sort := is_univ;
  spec_axiom := univ_axiom;
  spec_rule := univ_rule;
  spec_prim := Some (Univ 0);
|}.

Definition pure_predicative_table : pts_table := {|
  spec_sort := is_univ;
  spec_axiom := univ_axiom;
  spec_rule := univ_rule;
  spec_prim := None;
|}.

(** ∗, □, △ read as Type_0, Type_1, Type_2. *)
Definition u_to_univ (s : sort) : sort :=
  match s with
  | Star => Univ 0
  | Box => Univ 1
  | Tri => Univ 2
  | Univ i => Univ i
  end.

Lemma predicative_closed : table_closed predicative_table.
Proof. solve_table_closed. Qed.

Lemma pure_predicative_closed : table_closed pure_predicative_table.
Proof. solve_table_closed. Qed.

Definition predicative : spec :=
  {| spec_table := predicative_table; spec_wf := predicative_closed |}.
Definition pure_predicative : spec :=
  {| spec_table := pure_predicative_table; spec_wf := pure_predicative_closed |}.
