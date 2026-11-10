(** * The predicative hierarchy with MLTT primitives

    Sorts Type_0, Type_1, ...; axioms [Type_i : Type_(i+1)] and rules
    [(Type_i, Type_j, Type_(max i j))].  Levels are explicit: no
    cumulativity and no level inference.  Void, Unit and Bool live in
    Type_0.  Σ follows the rule of Π, [Σx:A. B : Type_(max i j)], and
    terms may mention the constants of a signature.

    [pure_predicative] is the same hierarchy without the primitives, Σ
    and constants; it is the target of the renaming [u_to_univ] of the
    sorts of U⁻, under which the looping combinator must be rejected.

    [predicative_prop] adds the impredicative sort Prop of CIC beside the
    hierarchy, with [Prop : Type_1] (Rocq's Set is Type_0 here).  A
    product into Prop is in Prop whatever its domain, Type_i included; a
    product of a proposition into Type_i is in Type_i; between the Type_i
    the rule is [max] as before.  Impredicativity comes from the table of
    products alone: the rule of Π in the checker is unchanged.

    Σ gets its own table, without the impredicative rule: a pair always
    lives in Type, so [Σx:A. P x] with [P x : Prop] keeps its witness as
    computational data.

    | domain   | codomain | Π            | Σ            |
    |----------|----------|--------------|--------------|
    | Type_i   | Type_j   | Type_max(i,j)| Type_max(i,j)|
    | Type_i   | Prop     | Prop         | Type_i       |
    | Prop     | Type_j   | Type_j       | Type_j       |
    | Prop     | Prop     | Prop         | Type_0       |

    The last Σ row is a choice for the native pair; conjunction in Prop
    is declared separately, as an inductive type. *)

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
  spec_sigma := univ_rule;
  spec_decls := true;
|}.

Definition pure_predicative_table : pts_table := {|
  spec_sort := is_univ;
  spec_axiom := univ_axiom;
  spec_rule := univ_rule;
  spec_prim := None;
  spec_sigma _ _ := None;
  spec_decls := false;
|}.

(** ∗, □, △ read as Type_0, Type_1, Type_2. *)
Definition u_to_univ (s : sort) : sort :=
  match s with
  | Star => Univ 0
  | Box => Univ 1
  | Tri => Univ 2
  | Univ i => Univ i
  | Prp => Prp
  end.

(** ** The hierarchy with Prop *)

Definition is_prop_univ (s : sort) : bool :=
  match s with
  | Univ _ | Prp => true
  | _ => false
  end.

Definition prop_axiom (s : sort) : option sort :=
  match s with
  | Prp => Some (Univ 1)
  | _ => univ_axiom s
  end.

Definition prop_rule (s1 s2 : sort) : option sort :=
  match s1, s2 with
  | (Univ _ | Prp), Prp => Some Prp
  | Prp, Univ j => Some (Univ j)
  | _, _ => univ_rule s1 s2
  end.

Definition prop_sigma (s1 s2 : sort) : option sort :=
  match s1, s2 with
  | Univ i, Prp => Some (Univ i)
  | Prp, Univ j => Some (Univ j)
  | Prp, Prp => Some (Univ 0)
  | _, _ => univ_rule s1 s2
  end.

Definition predicative_prop_table : pts_table := {|
  spec_sort := is_prop_univ;
  spec_axiom := prop_axiom;
  spec_rule := prop_rule;
  spec_prim := Some (Univ 0);
  spec_sigma := prop_sigma;
  spec_decls := true;
|}.

Lemma predicative_closed : table_closed predicative_table.
Proof. solve_table_closed. Qed.

Lemma pure_predicative_closed : table_closed pure_predicative_table.
Proof. solve_table_closed. Qed.

Definition predicative : spec :=
  {| spec_table := predicative_table; spec_wf := predicative_closed |}.
Definition pure_predicative : spec :=
  {| spec_table := pure_predicative_table; spec_wf := pure_predicative_closed |}.

Lemma predicative_prop_closed : table_closed predicative_prop_table.
Proof. solve_table_closed. Qed.

Definition predicative_prop : spec :=
  {| spec_table := predicative_prop_table; spec_wf := predicative_prop_closed |}.
