(** * Specifications of pure type systems

    A PTS is given by sorts [S], axioms [A ⊆ S × S] and Π-rules
    [R ⊆ S × S × S].  Only functional PTSs are used, so axioms and rules
    are partial functions: [spec_axiom s = Some s'] is the axiom [s : s'],
    and [spec_rule s1 s2 = Some s3] is the rule [(s1, s2, s3)].  The
    predicative hierarchy is infinite, so a specification is a pair of
    computable functions rather than a finite table.

    [spec_sort] tells the sorts of the system apart from the remaining
    elements of [sort]; it distinguishes "not a sort of this system" from
    "the top sort, which has no type" (△ in U⁻).

    [spec_prim] switches on the block of MLTT primitives: [Some s] puts
    Void, Unit and Bool into the sort [s], [None] turns the block off.  In
    the pure U⁻ the block is off, so that the primitives cannot help the
    checking of the PCF translation or of the looping combinator.

    A specification [spec] packs such a table with a proof of
    [table_closed]: axioms, rules and the primitives mention only sorts of
    the system.  The typing rules do not consult [spec_sort] themselves,
    so without the invariant a table with [spec_sort Star = false] could
    still derive [∗ : ∗]; carrying the proof in the type makes every
    statement about [spec] hold without an extra premise.  [spec] coerces
    to its table, so [spec_rule S s1 s2] reads as before. *)

From DepTypes.PTS Require Import Syntax.

Record pts_table : Type := {
  spec_sort : sort -> bool;
  spec_axiom : sort -> option sort;
  spec_rule : sort -> sort -> option sort;
  spec_prim : option sort;
}.

(** ** Well-formedness of a table *)

Definition table_closed (S : pts_table) : Prop :=
  (forall s s', spec_axiom S s = Some s' -> spec_sort S s = true /\ spec_sort S s' = true) /\
  (forall s1 s2 s3, spec_rule S s1 s2 = Some s3 ->
     spec_sort S s1 = true /\ spec_sort S s2 = true /\ spec_sort S s3 = true) /\
  (forall s, spec_prim S = Some s -> spec_sort S s = true).

Record spec : Type := {
  spec_table :> pts_table;
  spec_wf : table_closed spec_table;
}.

Lemma spec_axiom_sorts : forall (S : spec) s s',
    spec_axiom S s = Some s' -> spec_sort S s = true /\ spec_sort S s' = true.
Proof. intros S. apply (spec_wf S). Qed.

Lemma spec_rule_sorts : forall (S : spec) s1 s2 s3,
    spec_rule S s1 s2 = Some s3 ->
    spec_sort S s1 = true /\ spec_sort S s2 = true /\ spec_sort S s3 = true.
Proof. intros S. apply (spec_wf S). Qed.

Lemma spec_prim_sort : forall (S : spec) s,
    spec_prim S = Some s -> spec_sort S s = true.
Proof. intros S. apply (spec_wf S). Qed.

(** Proves [table_closed] of a concrete table by cases on sorts. *)
Ltac solve_table_closed :=
  repeat split; intros;
  repeat match goal with s : sort |- _ => destruct s end;
  cbn in *; try discriminate;
  repeat match goal with H : Some _ = Some _ |- _ => injection H as <- end;
  repeat split.
