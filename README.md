# Dependent types via pure type systems, in Rocq

The executable companion to the first lecture on dependent types. It is built
around two algorithms:

1. **A type checker parameterized by a PTS specification.** One program with
   a table of sorts, axioms and Π-rules checks both the output of the PCF
   translation in System U⁻ and the minimal predicative MLTT with Π,
   universes and the primitives Void, Unit, Bool.
2. **A translation of PCF into U⁻.** General recursion is encoded by the
   looping combinator of Geuvers–Verkoelen (after Hurkens' paradox);
   typing and the observable numeric result, including the strictness of
   numeric operations, must be preserved.

The main demonstration: the same annotated looping combinator is accepted by
the U⁻ table and rejected by the predicative one. In the latter, the body of
`induct` quantifies over `U : Type₂`, so it has sort `Type₂` where its
annotation expects `Type₀`.

Definitions and algorithms are written in Rocq and extracted to
OCaml, with a thin OCaml shell for printing, traces and demos. The lecture
plan is [plan-dependent-types.md](plan-dependent-types.md); the
implementation plan, stages and readiness criteria are in
[plan-deptypes-impl.md](plan-deptypes-impl.md).

## Status

The base definitions and bounded evaluator exist (stages 0–2 of the
implementation plan); the checker of stage 3 runs, is tested on examples and
is proved sound against the annotated kernel, and is extracted to OCaml with
demonstrations; stage 3 is complete. The looping combinator of stage 4 is
built, typed in U⁻ and rejected in the predicative hierarchy; the Church
numerals of stage 5 give the PCF result on the terminating regression programs,
and no result within the limit on those that diverge in PCF; divergence and the
adequacy of the encoding are not proved. The translator of stage 6 turns
well-typed PCF programs into U⁻ terms; its checked entry point
`translate_checked` runs the U⁻ checker on each output against the translated
type and returns only accepted ones, and the program table, the demos and the
slow test go through it. On the regression programs and on `add`, `mul` and `fact`
(up to `fact 4 = 24`) the translation agrees with the PCF evaluator where both
terminate. Type preservation is proved: a program checked by PCF translates
to a term that checks against its translated type in U⁻. Adequacy is not
proved yet.

| Component | Status |
|---|---|
| unified syntax with de Bruijn indices, renaming, substitution | defined, tested on examples |
| term builder from named syntax (Rocq and extracted OCaml) | implemented, tested |
| PTS specifications; λ∗, U, U⁻, predicative hierarchy | defined, closedness carried in the type |
| β + annotation erasure + ι reduction, conversion (no η) | defined |
| normal-order strategy | defined, determinism proved |
| declarative typing parameterized by a specification | defined |
| bidirectional judgments of the annotated kernel | defined |
| source PCF from strictness-pcf | wired as a submodule, builds |
| bounded normal-order evaluation and conversion | implemented; step correspondence and soundness of successful equality proved |
| bidirectional checker `infer` / `check` with primitives, errors and traces | implemented, tested; soundness against the annotated kernel proved |
| validation of the context and expected type (`bwf_ctx`, `btype`) | implemented, tested, soundness proved |
| OCaml extraction, printer with names, demonstrations, regression tests | done |
| independent readable OCaml reference and differential tests | implemented in `reference/` |
| looping combinator `L₀` and family `Lₙ` from Hurkens' paradox | typed in U⁻ (n ≤ 3), unfolding `Lₙ β f =β f (Lₙ₊₁ β f)` certified (n ≤ 2), predicative rejection recorded |
| Church numerals, Kleene predecessor, zero test strict in the whole numeral | typed in U⁻, correct on numerals; on the strictness regressions, the PCF result for terminating programs and no result within the limit for diverging ones (divergence not proved) |
| PCF translation, following the bidirectional PCF checker | implemented; `translate_checked` runs the U⁻ checker on each output and returns only accepted ones, and the program table, the demos and the slow test go through it; agrees with the PCF evaluator on the regression programs and `fact` up to 4 (no result within the limit where PCF diverges) |
| type preservation of the translation (PCF bidirectional ⇓ to the annotated kernel of U⁻) | proved |

## Building

Tested with Rocq 9.1.1, OCaml 4.14.2 and dune 3.

```sh
git submodule update --init   # fetch the pinned strictness-pcf
make                          # builds the needed PCF modules, then DepTypes
make demo                     # extracts the checker and runs the lecture demos
make test                     # extraction regressions and reference comparisons
make check                    # the Rocq build and the OCaml tests
make test-slow                # fact 4 = 24 by PCF and through the checked translation, about a minute
make -C reference run         # runs the standalone native OCaml examples
make clean
```

`extraction/Extract.v` writes `extraction/generated/deptypes.ml`, which is
rebuilt by `make` and never edited by hand; `pretty.ml` prints terms with
names, errors and trace events, `main.ml` runs the demonstrations and
`regress.ml` the tests.

[`reference/`](reference/README.md) contains a separate, hand-written OCaml
version of the executable kernel, like the native reference in
`strictness-pcf`. Its differential tests compare complete answers and traces
with the extract; proofs about the Rocq code do not transfer to the native
implementation.

`_CoqProject` maps `vendor/strictness-pcf/theories` to `PCF` and `theories/`
to `DepTypes`. Only the PCF modules the translation needs are built, so the
strictness analyser and its Equations dependency are not required.

## Files

| File | What's in it |
|------|--------------|
| `Common/Result.v` | The result monad with `let*` and its inversion lemmas (ported). |
| `Common/Traced.v` | Result with an event log, for checker traces (ported). |
| `PTS/Syntax.v` | Sorts (∗, □, △, Type_i); terms: sort, variable, Π, unannotated λ, application, annotation, and the primitives Void, Unit, Bool with eliminators taking an explicit result family. Renaming, substitution, `subst1`, `arrow`, free variables, `map_sorts`, contexts and `lookup`. Renaming and substitution leave closed terms unchanged. |
| `PTS/Named.v` | A builder of de Bruijn terms from named ones: `nterm` with a name at each binder, `resolve` and `resolve_ctx` with the first unbound name as error, and notations (`λ x, b`, `Π x : A, B`, `A ~> B`, `t ∷ A`, string literals as variables, juxtaposition as application). Unverified; its output is trusted only once the checker accepts it. Extracted, so OCaml builds terms by name too. `resolve_weaken`: a closed named term resolves the same under any names; a resolved term is closed above the number of names. The arrow `A ~> B` binds no name (`NArrow`), so every string, `"_"` included, is an ordinary variable. |
| `PTS/Spec.v` | A functional PTS table `pts_table` (computable `spec_sort`, `spec_axiom`, `spec_rule`, plus `spec_prim` switching on the MLTT primitives) and `spec`, a table packed with the proof that it mentions only its own sorts. |
| `PTS/Reduction.v` | One-step reduction (β, annotation erasure, ι, congruences), `red`, conversion `≡`, normal forms. A conversion relation, not a strategy. Multi-step congruences, `erase_ann` with `red_erase` (a term reduces to its annotation-free version) and `erase_conv`. |
| `PTS/NormalOrder.v` | The evaluator's strategy: deterministic leftmost-outermost `⇝ₙ`, normal and neutral forms `nf`/`ne`; `nstep` is a sub-relation of `red1`, normal forms do not step, and the step is deterministic. A raw term without a step may be `stuck` rather than normal, so the evaluator answers normal form, stuck, or out of fuel. |
| `PTS/Eval.v` | Bounded full normalization with traces and weak-head reduction; conversion accepts syntactically equal terms at once and otherwise compares normal forms; `ConvEqual v` reports the common form `v` both sides reach by normal order. `classify` finds the next normal-order step, or tells neutral, normal and stuck terms apart, in one structural pass, and corresponds exactly to `nstep`; it and `head_step` share the root contractions in `contract`; normalization results, weak-head results (each weak-head step is a normal-order step) and accepted equalities have soundness proofs; normalization is complete: a normal form reachable by normal order is found with enough fuel, and more fuel does not change it. Timeouts and stuck terms have separate results; `convert` reports stuckness only for syntactically different terms, so the checker passes it validated types only. The converse for `ConvDifferent` and progress of well-typed terms remain open. `joinable` finds a common reduct up to annotations in two bounded traces, for terms without normal forms; `joinable_sound` makes a positive answer a conversion. |
| `PTS/Typing.v` | Declarative `wf_ctx` and `S ;; Γ ⊢ t ∈ A` parameterized by a specification; every typable sort is a sort of the system. Types unannotated β-redexes, so it is not the reference for completeness. |
| `PTS/Bidir.v` | The annotated kernel: `S ;; Γ ⊢ t ⇑ A` and `S ;; Γ ⊢ t ⇓ A`, the algorithmic rules the checker must be sound and complete for. Admissible inputs `bwf_ctx` and `btype` (a sort of the system, or a term synthesizing a sort), and the explicit premise `normalizing_types` of completeness. Synthesis is a relation, so completeness of `infer` is stated up to conversion and for sufficient fuel. With the primitives off, no primitive syntax is accepted. `bidir_weaken` extends a context from below for terms whose variables stay above it; a closed term typed in the empty context is typed in any (`synth_closed`, `chk_closed`). |
| `PTS/Check.v` | The checker: one structural function `tc` for both modes, with `infer` and `check` as wrappers; fuel only for `whnf` and `convert` on types; three answers: `Accepted`, `Rejected` with a diagnostic (the subterm with its expected and inferred types, or a Π-type with its missing sort rule), and `Undecided` with the term whose typing ran out of fuel; a trace with phase markers (context entries, expected type, term) and events for axioms, rules, unfoldings to a sort or a Π (with the type before unfolding), argument checks, substitutions, conversions (with the common form) and result families of eliminators (with their sort). The entry points `run_infer` and `run_check` first validate the context (`check_ctx`) and the expected type (`check_type`). |
| `PTS/CheckSound.v` | Soundness of the checker against PTS.Bidir, for every specification and any fuel: `tc_sound` (synthesis and checking), `check_ctx_sound`, `check_type_sound`, and for the entry points `run_infer_sound` and `run_check_sound` (an `Accepted` answer gives `bwf_ctx`, `btype` and the judgment). |
| `Configs/Finite.v` | λ∗, U and U⁻. |
| `Configs/Predicative.v` | Type_i : Type_(i+1) with the `max` rule, with and without primitives; the renaming of ∗, □, △ to Type_0, Type_1, Type_2. |
| `PCFTranslation/Source.v` | The source PCF from the submodule, under qualified names. |
| `PCFTranslation/Translate.v` | The translation: `⟦ℕ⟧ = Nat`, `⟦A ⇒ B⟧ = ⟦A⟧ → ⟦B⟧`; variables, λ, application and annotations keep their shape and names, literals become numerals, `succ`/`pred` the Church operations, `ifz` the zero test strict in the whole numeral at the checked type, and `fix_A u` the looping combinator `L₀ ⟦A⟧ ⟦u⟧`. One structural function `tr` follows the bidirectional checker of strictness-pcf and fails with its error, so only well-typed programs are translated; names are resolved by the builder, as PCF's `lookup` finds the first entry. `translate_checked` (and `translate_program_checked`) also runs the U⁻ checker on the output against the translated type and returns it only when accepted; `translate_checked_sound` derives the typing of an accepted output from the soundness of that checker, independently of type preservation. |
| `PCFTranslation/Programs.v` | PCF programs in PCF notation (the regression table, `ifz` at a function type, `fix` at `ℕ → ℕ`, and `add`, `mul`, `fact` of strictness-pcf): each is evaluated by PCF and translated, checked at `Nat` in U⁻ and run by normal order, with the three-valued verdict. On the source side, `pcf_cases_source` proves what PCF does: the expected number by its evaluator, or genuine divergence (`diverges t`, from the divergence of Ω and strictness-pcf's closure lemmas through `succ`, `pred` and the condition of `ifz`). `fact 4` is checked by `make test-slow`, which runs both the PCF evaluator and the checked translation and compares the numbers. |
| `PCFTranslation/TranslateSound.v` | Type preservation: `translation_preserves_typing` — if PCF checks `Γ ⊢ t ⇓ A`, the translation exists and checks against `⟦A⟧` in `⟦Γ⟧` in U⁻; `translate_sound` — whatever the translator outputs is typed, in a well-formed context against an admissible type; `tr_complete` and `tr_resolves` — the translator succeeds on PCF-typed programs. Built on typing certificates of the closed encodings, carried into any context by `synth_closed`, closed translated types of sort ∗, numerals typed for every `k`, and the bridge between PCF's `lookup` and the builder's names. |
| `SystemU/Looping.v` | Hurkens' paradox in λU⁻ after Geuvers–Verkoelen (TLCA version, §4), written with the builder: `V`, `U`, `sb`, `le`, `induct`, `WF`, `I`, `omega`, `lemma`, `lemma2`, `paradox`, the looping combinator `L₀ : Πβ:∗. (β → β) → β` and the family `Lₙ` of their Lemma 3. `looping_typed` (n ≤ 3) from checker runs and `run_infer_sound`; `looping_unfolds` (n ≤ 2) from bounded evaluation, `whnf_reduces` and `joinable_sound`; `looping_predicative_rejected` records where the predicative checker fails: the body of `induct` quantifies over `U : Type₂`. |
| `SystemU/Encodings.v` | Church numerals and booleans in pure U⁻, Kleene's predecessor through pairs, and `ifz` at any result type with a zero test strict in the whole numeral: its step uses the result of the inner layer, so a partial numeral such as `succ Ω` makes it diverge, while the branches and function arguments stay lazy. The lazy test is kept as the counterexample. `observe` decodes a normal form to a number (`observe_numeral_sound`); `omega_nat_typed` checks the translation of Ω_ℕ; the PCF strictness regressions are typed in U⁻ and judged by a three-valued verdict: terminating programs agree with PCF, diverging ones have no result within the limit, which is not a proof of divergence. |
| `Examples.v` | The lecture examples shared by the tests and the OCaml demos: the polymorphic identity and its application, the forbidden rule (∗,□), large elimination, the raw Ω. The raw Ω is `raw_omega`, apart from the `omega` of Hurkens' paradox. |
| `Tests.v` | Substitution without capture, open terms, PTS tables, normal order, bounded evaluation and traces, conversion without η, declarative versus annotated typing, admissibility of expected types, and the checker on U⁻ and the predicative hierarchy (lecture traces of `id A x` and of large elimination, the forbidden rule (∗,□), the universe level of ΠA:Type₀. A → A, large elimination, and each kind of error), and validation of inputs (an unbound annotation in the expected type, the top sort △ accepted, ill-formed contexts). |

## Planned layout

```text
theories/
  Common/          results, errors, traces
  PTS/             syntax, substitution, typing, reduction, checker
  Configs/         U⁻ and the predicative hierarchy
  SystemU/         looping combinator and encodings
  PCFTranslation/  name bridge, translation, type preservation, adequacy
  MLTT/            primitives and dependent eliminators
  Contracts.v      proved interfaces and their assumptions
  Examples.v
  Tests.v
extraction/        Extract.v, generated/ (never edited), pretty.ml, main.ml
reference/         standalone readable OCaml version and differential tests
tests/             regressions and differential tests
```

Ports from sibling projects are recorded in [PORTING.md](PORTING.md).
