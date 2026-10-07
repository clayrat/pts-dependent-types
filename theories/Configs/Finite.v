(** * Finite PTS configurations: λ∗, U and U⁻

    | System | Sorts   | Axioms      | Rules (abbreviated)               |
    |--------|---------|-------------|-----------------------------------|
    | λ∗     | ∗       | ∗:∗         | (∗,∗)                             |
    | U⁻     | ∗, □, △ | ∗:□, □:△    | (∗,∗), (□,∗), (□,□), (△,□)        |
    | U      | ∗, □, △ | ∗:□, □:△    | the rules of U⁻ and (△,∗)         |

    None of them has the MLTT primitives.  The checker terminates on U⁻
    and U only thanks to the strong normalization of their type level;
    on λ∗ it runs out of fuel. *)

From DepTypes.PTS Require Import Syntax Spec.

Definition is_named_sort (s : sort) : bool :=
  match s with
  | Star | Box | Tri => true
  | Univ _ => false
  end.

Definition u_axiom (s : sort) : option sort :=
  match s with
  | Star => Some Box
  | Box => Some Tri
  | _ => None
  end.

(** ** λ∗ *)

Definition lambda_star_table : pts_table := {|
  spec_sort s := match s with Star => true | _ => false end;
  spec_axiom s := match s with Star => Some Star | _ => None end;
  spec_rule s1 s2 :=
    match s1, s2 with
    | Star, Star => Some Star
    | _, _ => None
    end;
  spec_prim := None;
|}.

(** ** U⁻ *)

Definition u_minus_rule (s1 s2 : sort) : option sort :=
  match s1, s2 with
  | Star, Star | Box, Star => Some Star
  | Box, Box | Tri, Box => Some Box
  | _, _ => None
  end.

Definition u_minus_table : pts_table := {|
  spec_sort := is_named_sort;
  spec_axiom := u_axiom;
  spec_rule := u_minus_rule;
  spec_prim := None;
|}.

(** ** U *)

Definition u_table : pts_table := {|
  spec_sort := is_named_sort;
  spec_axiom := u_axiom;
  spec_rule s1 s2 :=
    match s1, s2 with
    | Tri, Star => Some Star
    | _, _ => u_minus_rule s1 s2
    end;
  spec_prim := None;
|}.

(** ** Specifications *)

Lemma lambda_star_closed : table_closed lambda_star_table.
Proof. solve_table_closed. Qed.

Lemma u_minus_closed : table_closed u_minus_table.
Proof. solve_table_closed. Qed.

Lemma u_closed : table_closed u_table.
Proof. solve_table_closed. Qed.

Definition lambda_star : spec := {| spec_table := lambda_star_table; spec_wf := lambda_star_closed |}.
Definition system_u_minus : spec := {| spec_table := u_minus_table; spec_wf := u_minus_closed |}.
Definition system_u : spec := {| spec_table := u_table; spec_wf := u_closed |}.
