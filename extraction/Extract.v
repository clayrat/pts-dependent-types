(** * Extraction driver

    Exports the syntax, the PTS configurations, the bounded evaluator and
    conversion, the checker with its entry points, and the lecture
    examples into generated/deptypes.ml.  Proofs and relations stay in
    Rocq; the extracted functions are the ones the soundness theorems are
    about.  Natural numbers (fuel, de Bruijn indices, universe levels) are
    OCaml ints, booleans are OCaml bools. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From DepTypes.PTS Require Import Syntax Spec Eval Check.
From DepTypes.Configs Require Import Finite Predicative.
From DepTypes Require Import Examples.

Extraction Language OCaml.
Set Extraction Output Directory "generated".

(** Arithmetic on de Bruijn indices and levels, natively. *)
Extract Inlined Constant Init.Nat.add => "(+)".
Extract Inlined Constant Init.Nat.max => "max".
Extract Inlined Constant Init.Nat.eqb => "(=)".
Extract Inlined Constant Init.Nat.ltb => "(<)".
Extract Inlined Constant PeanoNat.Nat.add => "(+)".
Extract Inlined Constant PeanoNat.Nat.max => "max".
Extract Inlined Constant PeanoNat.Nat.eqb => "(=)".
Extract Inlined Constant PeanoNat.Nat.ltb => "(<)".

Extraction "deptypes.ml"
  term_eqb sort_eqb rename lift subst subst1 arrow free_in map_sorts lookup
  lambda_star system_u system_u_minus predicative pure_predicative u_to_univ
  classify normalize_trace normalize whnf convert
  infer check run_infer run_check
  id_ty id_tm id_applied_ctx id_applied star_box_ctx star_box
  type_family large_elim_ty self_app omega.
