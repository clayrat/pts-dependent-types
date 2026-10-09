(** * Extraction driver

    Exports the syntax, the PTS configurations, the bounded evaluator and
    conversion, the checker with its entry points, and the lecture
    examples into generated/deptypes.ml.  Proofs and relations stay in
    Rocq; the extracted functions are the ones the soundness theorems are
    about.  Natural numbers (fuel, de Bruijn indices, universe levels) are
    OCaml ints, booleans are OCaml bools, and the names of the term
    builder (PTS.Named) are OCaml strings. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString.
From DepTypes.PTS Require Import Syntax Named Spec Eval Check.
From DepTypes.Configs Require Import Finite Predicative.
From DepTypes.SystemU Require Import Looping Encodings.
From DepTypes.MLTT Require Import Choose Eliminators.
From DepTypes.PCFTranslation Require Import Translate Programs.
From PCF Require Examples OperationalSemantics.
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
  resolve resolve_ctx
  lambda_star system_u system_u_minus predicative pure_predicative u_to_univ
  classify normalize_trace normalize whnf convert
  infer check run_infer run_check
  id_ty id_tm id_applied_ctx id_applied star_box_ctx star_box
  type_family large_elim_ty self_app raw_omega
  joinable looping looping_ty looping_applied looping_fuel unfolding_fuel unfolds_to
  CNat CBool ctrue cfalse czero csucc numeral cpair cfst csnd cshift cpred
  is_zero is_zero_lazy ifz ifz_lazy omega_nat omega_fun church church_nf decode_nat
  observe observe_fuel verdict_of best_verdict encodings_typed typed_in_u_minus strictness_cases
  tr_ty tr translate translate_program translated_type translate_checked translate_program_checked
  pcf_cases pcf_fuel translation_fuel fuel_for pcf_as_expected
  universe_family cond choose_ty choose_family choose choose_swapped low_family
  types_ctx args_ctx open_ctx in_ctx term_in choose_at choose_fuel build
  elim_fuel void_ctx void_family void_elim unit_universe unit_family unit_elim unit_ctx
  PCF.Examples.add PCF.Examples.mul PCF.Examples.fact PCF.OperationalSemantics.evalFuel.
