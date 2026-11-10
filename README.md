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

For the lecture on inductive types the kernel is extended on the branch
`inductive-types`, from the tag `lecture-6` that the notes of lecture 6 cite.
Terms gain dependent pairs and the constants of a signature: inductive types,
constructors, eliminator instances at fixed levels and δ-constants, given by
classified descriptions (`PTS/Signature.v`). Reduction, normal order, the
evaluator, both typings and the checker take the signature; its δ-rule and
the ι-rule of eliminator instances by the scheme of descriptions are steps
like β. The soundness of the checker and the stability of reduction under
substitution are proved for every signature. Σ and constants are on only in
the predicative table with primitives, and the developments of lecture 6 run
in the empty signature: `make demo` prints the same output as at the tag, and
the regressions, the differential test and `make test-slow` pass. The native
reference in `reference/` implements Σ and constants as well, and the
differential test compares it with the extract on them.

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
| Church numerals, Kleene predecessor, zero test strict in the whole numeral | typed in U⁻; computation on every numeral proved; on the strictness regressions, the PCF result for terminating programs and no result within the limit for diverging ones (divergence not proved) |
| PCF translation, following the bidirectional PCF checker | implemented; `translate_checked` runs the U⁻ checker on each output and returns only accepted ones, and the program table, the demos and the slow test go through it; agrees with the PCF evaluator on the regression programs and `fact` up to 4 (no result within the limit where PCF diverges) |
| type preservation of the translation (PCF bidirectional ⇓ to the annotated kernel of U⁻) | proved |
| minimal MLTT (stage 7): `choose`, the eliminators of Void and Unit | typed and evaluated in the predicative hierarchy: both branches of `choose`, neutral types on free variables, errors of branch and level, Void in a non-empty context, Unit computing on `tt` and staying neutral without η |
| Σ: formation by a rule of the table, pairs checked against Σ, projections, no η | defined in every layer; checker soundness proved; tested on dependent pairs, products and levels |
| signatures: classified descriptions, eliminator instances with the flag of active ι-rules, δ-constants, closedness carried in the type | defined; δ and ι by scheme in reduction, normal order and the evaluator, stable under substitution (proved); checker soundness proved for every signature; tested on a hand-written ℕ |
| match and fix (lecture 8, branch `cic`): typing with the category of elimination, ι of match, unfolding of fix on constructors, normal order, call-by-value `eval_src` | defined in every layer; checker soundness and the stability of reduction under substitution proved; tested on `nat_rect`, `plus`, `append`, `copy` and refusals |
| guard of fix (lecture 8): marks `Large`, `Arg`, `Sub m`, `Self`; the declarative judgment `Guarded`; the strict subterm relation of descriptions | executable guard in the checker, proved to imply `Guarded`; the invariants of the marks against the strict subterm relation proved (entry, binders, the step of a match on a constructor, decreasing calls); tested on `half`, `size` over `Tr`, calls under λ and the refusals of the plan; well-foundedness of the relation open |
| native reference for Σ and constants | implemented; compared with the extract on Σ in every configuration, the dependent pairs of `MLTT/Pairs.v`, the signature of `MLTT/Constants.v` (traces, δ, ι, object-first order, inactive instances) and the families of `MLTT/Families.v` (ι on open terms against the right sides written by hand) |

## Building

Tested with Rocq 9.1.1, OCaml 4.14.2 and dune 3.

```sh
git submodule update --init   # fetch the pinned strictness-pcf
make                          # builds the needed PCF modules, then DepTypes
make demo                     # extracts the checker and runs the lecture demos
make test                     # extraction regressions, the demos against lecture-6, reference comparisons
make assumptions              # every proved contract is axiom-free
make check                    # the Rocq build, the axiom check and the OCaml tests
make test-slow                # fact 4 = 24 by PCF and through the checked translation, about a minute
make -C reference run         # runs the standalone native OCaml examples
make clean
```

`extraction/Extract.v` writes `extraction/generated/deptypes.ml`, which is
rebuilt by `make` and never edited by hand; `pretty.ml` prints terms with
names, errors and trace events, `main.ml` runs the demonstrations and
`regress.ml` the tests; `make test` also compares the output of the demos with
`lecture6.expected`, recorded at the tag `lecture-6`.

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
| `Common/Traced.v` | Result with an event log, for checker traces (ported); `titer` and `tfold` over lists, `titer2` over the pairs of two lists of the same length, and the tactic `tbind_in` that splits a successful run. |
| `Common/Outcome.v` | `cbv_result`, the answers of a call-by-value evaluator over the terms of any language (a value, a stuck term, out of fuel), shared by `PTS/EvalSrc.v` and the evaluators of compiled programs. |
| `PTS/Syntax.v` | Sorts (∗, □, △, Type_i, and Prop for lecture 8); terms: sort, variable, Π, unannotated λ, application, annotation, the primitives Void, Unit, Bool with eliminators taking an explicit result family, Σ with unannotated pairs and projections, and constants `Const g` with `g` one of `Ind D`, `Ctor D c`, `Elim D s` (the instance for motives into the sort `s`), `Def f`. Renaming, substitution, `subst1`, `arrow`, `times`, free variables, `map_sorts`, spines (`apps`, `spine_head`, `spine_args`) and telescopes (`pis`, `lams`, `vars`), contexts and `lookup`. Renaming and substitution leave closed terms unchanged. On the branch `cic` (lecture 8): `Case D s P x bs`, the primitive match on an element of D into the sort `s`, with the motive `P` a λ over the indices and the scrutinee and one branch per constructor, a λ over its fields; `Fix A k b`, the structural fixpoint with its type, the position of its structural argument and a body where the function is `Var 0`; `term_ind'`, induction with a hypothesis for the branches; `has_lams`. |
| `PTS/Telescope.v` | Substitution under the binders of a telescope: `upn` and `subst_tele` as the specification, and the environments the kernel computes with, `inst` (one `lift` instead of `m`), `params_env` (the parameters reversed once), `inst_tele`, `inst_params`; `SubstLaws.v` proves the two forms equal (`inst_upn`, `inst_tele_subst`). |
| `PTS/Named.v` | A builder of de Bruijn terms from named ones: `nterm` with a name at each binder, `resolve` and `resolve_ctx` with the first unbound name as error, and notations (`λ x, b`, `Π x : A, B`, `Σ x : A, B`, `A ~> B`, `A ⨯ B`, `⟨a, b⟩`, `t ∷ A`, string literals as variables, juxtaposition as application; constants as `NConst g`). Unverified; its output is trusted only once the checker accepts it. Extracted, so OCaml builds terms by name too. `resolve_weaken`: a closed named term resolves the same under any names; a resolved term is closed above the number of names. The arrow `A ~> B` binds no name (`NArrow`), so every string, `"_"` included, is an ordinary variable. `NCase` and `NFix f A k b`, binding `f` in its body. |
| `PTS/Build.v` | The conveniences of the examples, outside the kernel: `build`, `in_ctx` and `term_in` turn named terms and contexts into de Bruijn ones and fall back on ∗ or the empty context on an unbound name; every example checks that its terms resolve, so a fallback never stands in for an error. The examples turn accepted checker runs into derivations with `accepted_synth` and `accepted_check` of `PTS/CheckSound.v`, for any signature. |
| `PTS/Runs.v` | Runs of the checker on named terms for the examples: `infers`, `checks`, `converts` and `refusal`. Imported where used and not re-exported, so that projects with helpers of the same names are not affected. |
| `PTS/Spec.v` | A functional PTS table `pts_table` (computable `spec_sort`, `spec_axiom`, `spec_rule`, plus `spec_prim` switching on the MLTT primitives, `spec_sigma` the rules forming Σ, and `spec_decls` switching on constants) and `spec`, a table packed with the proof that it mentions only its own sorts. |
| `PTS/Signature.v` | Signatures: classified descriptions after Dybjer's schema (fields `FArg A` and `FRec B̄ v̄`, constructors with result indices, declarations with parameters, indices, a sort and the category of elimination `elim_class`, `PropOnly` or `AllSorts`, computed by the registration), entries for declarations, eliminator instances with their type and the flag of active ι-rules, and δ-constants, newest first; `signature` carries the proof that all its terms are closed in their telescopes, `∅` is the empty one and `sig_add` extends one, by exactly the new entry (`sig_add_entries`). Lookup, the types of an inductive type and its constructors rebuilt from the description, δ (`sig_delta`), and ι by the scheme of descriptions (`elim_view`, `full_elim`, `iota`): an instance with active rules on its full spine and a constructor spine contracts to the method applied to each field and, after a recursive one, its hypothesis. `allows_elimination`: a sort of the table that the category admits, the one check of the sort of a motive. ι of match by the description (`case_iota`), the types of the motive and of the branches for given parameters (`case_motive_type`, `case_branch_type`: the method type without hypotheses), the unfolding of a fix applied up to a structural constructor argument (`fix_unfold`), and the spines contracted at their last argument (`full_spine`, `spine_iota`). |
| `PTS/EmptySig.v` | The notations of the kernel's sections with the empty signature `∅` in place of the section's: the vocabulary of the developments of lecture 6. |
| `PTS/Reduction.v` | One-step reduction (β, annotation erasure, ι of the primitives and of projections, δ and ι of a signature, congruences), `red`, conversion `≡`, normal forms, all relative to a signature. A conversion relation, not a strategy. Multi-step congruences, `erase_ann` with `red_erase` (a term reduces to its annotation-free version) and `erase_conv`. With match and fix: their congruences, ι of match and the unfolding of fix; `struct_arg`, the structural argument of a type unfolding to a Π-telescope. |
| `PTS/SubstLaws.v` | The correctness of substitution, syntactically: extensionality, `subst Var t = t`, the fusion laws of renaming and substitution, `subst1 (lift 1 t) u = t`, the commutation `subst sb (subst1 b u) = subst1 (subst (up_sub sb) b) (subst sb u)`; ι of a signature commutes with substitution (`iota_subst`, from the closedness of descriptions); one-step and multi-step reduction and conversion are stable under substitution and renaming in every signature, and reducing the substituted terms reduces the result. ι of match and the unfolding of fix commute with substitution (`case_iota_subst`, `fix_unfold_subst`). |
| `PTS/NormalOrder.v` | The evaluator's strategy: deterministic leftmost-outermost `⇝ₙ`, normal and neutral forms `nf`/`ne`; a full spine of an eliminator instance with active rules is scanned object first, a projection pair first, and constants that are not δ-redexes head neutral spines; `nstep` is a sub-relation of `red1`, normal forms do not step, and the step is deterministic. A raw term without a step may be `stuck` rather than normal, so the evaluator answers normal form, stuck, or out of fuel. A fix applied up to its structural argument is scanned from that argument as well, a match from its scrutinee and then its motive and branches; a fix with normal type and body is a neutral head; `nfs` for normal branches. |
| `PTS/Eval.v` | Bounded full normalization with traces and weak-head reduction; conversion accepts syntactically equal terms at once and otherwise compares normal forms (`convert_full`); when a side mentions a δ-constant, `convert` first normalizes both sides with δ-constants folded (`sig_opaque`) and compares the two forms in one pass, unfolding δ only in the nearest spine around a difference with a δ-constant at the head (`conv_lazy`; a spine is unfolded only if nothing inside it was, and the pass gives up when an unfolding does not help, so it normalizes no subterm twice and is otherwise linear), and leaves every other answer to `convert_full`; `ConvEqual v` reports a common reduct `v` of both sides (`convert_equal_reaches`). `classify` finds the next normal-order step, or tells neutral, normal and stuck terms apart, in one structural pass, with one walk of each spine, linear in its length, in the extracted code and under `vm_compute` alike (it is proved equal to `classify_nested`, which takes a spine apart at every application, as `head_step` to `head_step_nested`), and corresponds exactly to `nstep`; it and `head_step` share the root contractions in `contract`; normalization results, weak-head results (each weak-head step is a normal-order step) and accepted equalities have soundness proofs; normalization is complete: a normal form reachable by normal order is found with enough fuel, and more fuel does not change it. Timeouts and stuck terms have separate results; `convert` reports stuckness only for syntactically different terms, so the checker passes it validated types only. The converse for `ConvDifferent` and progress of well-typed terms remain open. `joinable` finds a common reduct up to annotations in two bounded traces, for terms without normal forms; `joinable_sound` makes a positive answer a conversion. `classify`, `whnf` and `normalize` with match and fix, with the same proofs. |
| `PTS/EvalSrc.v` | Call-by-value evaluation of source programs (lecture 8), the source side of the contract of erasure: weak, function then argument, constructors and families applied to values are values, and so are eliminator instances with active rules and fixes short of the arity at which they compute (`head_arity`, the arity of their contraction); an instance without active rules is an ordinary constant and, applied, is stuck; the same root rules as `whnf`; three answers, `CbvValue`, `CbvStuck`, `CbvOutOfFuel`. `eval_nested` states the strategy one application at a time; `eval_src` takes each spine apart once and compares the count of its arguments with the arity of its head, linear in the length of the spine, in the extracted code and under `vm_compute` alike, where `eval_nested` is quadratic, and is proved equal to it (`eval_src_nested`). A value found is a reduct (`eval_src_reduces`). |
| `PTS/Guard.v` | The guard of fix (lecture 8): marks of the variables of a body (`Self` the function, `Arg` the structural argument, `Sub m` a strict subterm once applied to `m` arguments, `Large`), kept with their variables under binders; a match on a structural origin marks the fields of its branches from the description; every call heads a maximal spine with more than `k` arguments and a recognized subterm at `k` (`GPartialCall`, `GNotSubterm`). A body short of its `k + 1` leading λ is refused (`GShortBody`). The executable `guard_fix` and the judgment `Guarded` (`fix_guarded`), on the syntax and the signature alone: the typing rules use the judgment, the checker the algorithm. What the guard of Rocq accepts beyond: reduction of the checked terms, commutative cuts, nested and mutual fixpoints, nested inductive types. |
| `PTS/GuardSound.v` | The proofs about the guard: `guard_fix_sound`, the check implies the judgment; the strict subterm relation of descriptions (`immediate`, `strict_sub`), independent of the marks, and the invariants: marks respected at the entry, under binders and in the branch a match on a constructor takes, and every accepted call on a strict subterm. |
| `PTS/Typing.v` | Declarative `wf_ctx` and `S ;; Γ ⊢ t ∈ A` parameterized by a specification and a signature, with Σ, pairs, projections and constants at their closed types; every typable sort is a sort of the system. `signature_typed S sg`: the types of constants are types, δ-bodies have them, and ι-contractions keep the type of the redex, the premise of the declarative obligations, since a signature itself guarantees only closedness. Types unannotated β-redexes, so it is not the reference for completeness. `T_Case` and `T_Fix`, with `has_branches` for the branches; `T_Fix` asks `fix_guarded`. |
| `PTS/Bidir.v` | The annotated kernel: `S ;; Γ ⊢ t ⇑ A` and `S ;; Γ ⊢ t ⇓ A` (`synth S sg` and `chk S sg`), the algorithmic rules the checker must be sound and complete for; a pair, like a λ, only checks, projections synthesize, a constant synthesizes the type the signature gives it. Admissible inputs `bwf_ctx` and `btype` (a sort of the system, or a term synthesizing a sort), and the explicit premise `normalizing_types` of completeness. Synthesis is a relation, so completeness of `infer` is stated up to conversion and for sufficient fuel. With the primitives off, no primitive syntax is accepted. `bidir_weaken` extends a context from below for terms whose variables stay above it; a closed term typed in the empty context is typed in any (`synth_closed`, `chk_closed`). `S_Case`: the scrutinee synthesizes a type unfolding to `D ps us`, the motive and the branches check against the types built from the description, the motive sort is allowed by the category; `S_Fix` synthesizes the annotation of a guarded fix. |
| `PTS/Check.v` | The checker: one structural function `tc` for both modes, with `infer` and `check` as wrappers; fuel only for `whnf` and `convert` on types; three answers: `Accepted`, `Rejected` with a diagnostic (the subterm with its expected and inferred types, or a Π- or Σ-type with its missing sort rule, a constant missing from the signature or used while constants are off), and `Undecided` with the term whose typing ran out of fuel; a trace with phase markers (context entries, expected type, term) and events for axioms, Π- and Σ-rules, unfoldings to a sort, a Π or a Σ (with the type before unfolding), argument checks, substitutions, conversions (with the common form) and result families of eliminators (with their sort). The entry points `run_infer` and `run_check` first validate the context (`check_ctx`) and the expected type (`check_type`). Match: the family, the category of elimination (`EElimSort`), the number of branches (`EBranchCount`), the type of the scrutinee (`ENotInductive`), the motive and the branches, with the events `EvCase` and `EvBranch`; fix: the annotation, the structural position in its telescope (`ENoStructArg`) and its inductive type (`EStructNotInductive`, `EvFix`), the leading λ of the body (`EFixBody`), the body against the annotation, then the guard (`ENotGuarded`, `EvGuard`). |
| `PTS/CheckSound.v` | Soundness of the checker against PTS.Bidir, for every specification, every signature and any fuel: `tc_sound` (synthesis and checking), `check_ctx_sound`, `check_type_sound`, and for the entry points `run_infer_sound` and `run_check_sound` (an `Accepted` answer gives `bwf_ctx`, `btype` and the judgment). Soundness covers match and fix. |
| `Configs/Finite.v` | λ∗, U and U⁻; λC (lecture 8): ∗ : □ and all four rules over ∗ and □, the product in the sort of its codomain, as in Hirrolot's CoC gist. |
| `Configs/Predicative.v` | Type_i : Type_(i+1) with the `max` rule, with and without primitives; Σ by the same rule and constants only with the primitives; the renaming of ∗, □, △ to Type_0, Type_1, Type_2. For lecture 8, `predicative_prop`: the sort Prop (`Prp`, since `Prop` is a keyword of Rocq) with `Prop : Type₁`, products into Prop in Prop whatever the domain, `(Prop, Type_j, Type_j)`, and Σ by its own table, always in Type. |
| `PCFTranslation/Source.v` | The source PCF from the submodule, under qualified names. |
| `PCFTranslation/Translate.v` | The translation: `⟦ℕ⟧ = Nat`, `⟦A ⇒ B⟧ = ⟦A⟧ → ⟦B⟧`; variables, λ, application and annotations keep their shape and names, literals become numerals, `succ`/`pred` the Church operations, `ifz` the zero test strict in the whole numeral at the checked type, and `fix_A u` the looping combinator `L₀ ⟦A⟧ ⟦u⟧`. One structural function `tr` follows the bidirectional checker of strictness-pcf and fails with its error, so only well-typed programs are translated; names are resolved by the builder, as PCF's `lookup` finds the first entry. `translate_checked` (and `translate_program_checked`) also runs the U⁻ checker on the output against the translated type and returns it only when accepted; `translate_checked_sound` derives the typing of an accepted output from the soundness of that checker, independently of type preservation. |
| `PCFTranslation/Programs.v` | PCF programs in PCF notation (the regression table, `ifz` at a function type, `fix` at `ℕ → ℕ`, and `add`, `mul`, `fact` of strictness-pcf): each is evaluated by PCF and translated, checked at `Nat` in U⁻ and run by normal order, with the three-valued verdict. On the source side, `pcf_cases_source` proves what PCF does: the expected number by its evaluator, or genuine divergence (`diverges t`, from the divergence of Ω and strictness-pcf's closure lemmas through `succ`, `pred` and the condition of `ifz`). `fact 4` is checked by `make test-slow`, which runs both the PCF evaluator and the checked translation and compares the numbers. |
| `PCFTranslation/TranslateSound.v` | Type preservation: `translation_preserves_typing` — if PCF checks `Γ ⊢ t ⇓ A`, the translation exists and checks against `⟦A⟧` in `⟦Γ⟧` in U⁻; `translate_sound` — whatever the translator outputs is typed, in a well-formed context against an admissible type; `tr_complete` and `tr_resolves` — the translator succeeds on PCF-typed programs. Built on typing certificates of the closed encodings, carried into any context by `synth_closed`, closed translated types of sort ∗, numerals typed for every `k`, and the bridge between PCF's `lookup` and the builder's names. |
| `MLTT/Choose.v` | `choose : Πb:Bool. A → B → (if b then A else B)` in `A B : Type₀`, with `if b then A else B = elimBool (λ_. Type₀) A B b` (large elimination through `λ_. Type₀ : Bool → Type₁`): typed, `choose true a c` checks against `A` and evaluates to `a` (and `false` to `B` and `c`), with a free `b` the type stays neutral and checking against `A` fails, swapped branches and a family declared in `Type₀` are rejected. |
| `MLTT/Eliminators.v` | The other eliminators: Void in a non-empty context (`A : Type₀, v : Void ⊢ elimVoid (λ_. A) v ⇓ A`, neutral normal form; a scrutinee `tt` and the eliminator in U⁻ are rejected), and the dependent eliminator of Unit with a family computing a type, `C u = elimUnit (λ_. Type₀) Bool u`: `elimUnit C true tt : C tt` with `C tt ⇝ Bool`, computing to `true`; on a free `u : Unit` the type stays neutral and is not `Bool` (no η). |
| `MLTT/Pairs.v` | Σ: the dependent pair `⟨true, tt⟩ : Σb:Bool. IsTrue b` and the rejected `⟨false, tt⟩`; the dependent `snd` with the neutral type `IsTrue (fst p)`; projections computing, no η; `Bool × Bool`; `Σb:Bool. Type₀ : Type₁`; pairs only check, and U⁻ has no Σ. |
| `MLTT/Constants.v` | A signature written by hand: ℕ, the instance `elimNat[0]` with active rules and the δ-constant `double`. Types from the signature, the body of `double` in the signature of ℕ and `elimNat[0]` alone, where a body mentioning `double` is rejected; δ as a step of its own and ι in the order of `nat_rect`, so `double 1` reaches `succ (succ zero)`; the ι-rule on open terms by conversion; the object of a full spine evaluated first; a neutral spine on a free `n`; an instance without the flag staying neutral; unknown constants and constants in U⁻ rejected; a signature without types, where the checker accepts `c (λx. x)` for `c : (tt → tt) → Bool` and `f true` for `f := tt`, which gets stuck. |
| `MLTT/Families.v` | ι where shifts and substitutions matter, over the ℕ of `MLTT/Constants.v`: `Vec A n` (a parameter and an index, the index of `xs` an earlier field), `W A B` (a recursive field with a position, its domain mentioning a parameter and an earlier field) and `Tr A h x` (indices `h a y` mentioning a position, an earlier field and a parameter; two positions in `fork`; a field after a recursive one in `twin`). The rebuilt constructor types are the ones written by hand; every ι-rule on open terms contracts syntactically to the right side written by hand, converts to it, and both sides check against the motive at the constructor, while a swapped index or swapped positions make the right side ill-typed; vector negation under a motive depending on the index, ℕ as a W-type, and labels of trees compute. |
| `SystemU/Looping.v` | Hurkens' paradox in λU⁻ after Geuvers–Verkoelen (TLCA version, §4), written with the builder: `V`, `U`, `sb`, `le`, `induct`, `WF`, `I`, `omega`, `lemma`, `lemma2`, `paradox`, the looping combinator `L₀ : Πβ:∗. (β → β) → β` and the family `Lₙ` of their Lemma 3. `looping_typed` (n ≤ 3) from checker runs and `run_infer_sound`; `looping_unfolds` (n ≤ 2) from bounded evaluation, `whnf_reduces` and `joinable_sound`; `looping_predicative_rejected` records where the predicative checker fails: the body of `induct` quantifies over `U : Type₂`. |
| `SystemU/Encodings.v` | Church numerals and booleans in pure U⁻, Kleene's predecessor through pairs, and `ifz` at any result type with a zero test strict in the whole numeral: its step uses the result of the inner layer, so a partial numeral such as `succ Ω` makes it diverge, while the branches and function arguments stay lazy. The lazy test is kept as the counterexample. `observe` decodes a normal form to a number (`observe_numeral_sound`); `omega_nat_typed` checks the translation of Ω_ℕ; the PCF strictness regressions are typed in U⁻ and judged by a three-valued verdict: terminating programs agree with PCF, diverging ones have no result within the limit, which is not a proof of divergence. |
| `SystemU/EncodingsCompute.v` | The encodings compute on every numeral, by reduction: `succ cₖ ⇝* cₖ₊₁`, `pred cₖ₊₁ ⇝* cₖ`, `pred c₀ ⇝* c₀`, `is_zero c₀ ≡ true`, `is_zero cₖ₊₁ ≡ false`. A numeral applied to `T F X` unfolds to `Fᵏ X`; `pred` iterates `shift` from `(0, 0)` to the normal pair `(cₖ₋₁, cₖ)`; each step of the strict test applies the inner boolean to `false false`. |
| `PTS/Contracts.v` | The guarantees of the kernel as `Prop` definitions, kernel-checked independently of their proofs, for every specification and signature, and the obligations of progress and of soundness for the declarative rules for type-correct signatures: 14 proved contracts (`..._holds`: the laws of substitution and the stability of reduction under it, normal order and the evaluator, the equal and stuck answers of conversion, checker soundness, the category of elimination respected by every accepted match, the soundness of the guard and the invariants of its marks, a value of `eval_src` is a reduct) and the open obligations stated precisely (weakening and the substitution lemma for the declarative typing, confluence, injectivity of Π, progress for normal order and for `eval_src`, the well-foundedness of the strict subterm relation, soundness of the kernel for the declarative rules, the different answer and the completeness of conversion, checker completeness for both entry points). It depends on the kernel alone, so projects built on the kernel import it without the PCF translation and strictness-pcf. |
| `Contracts.v` | The guarantees of lecture 6, in the empty signature, re-exporting those of the kernel: 11 proved contracts (the looping combinator, numerals and their computation on every numeral, type preservation and the checked translation, the PCF source side, `choose` and the eliminators) and the open obligations (typing and unfolding of every `Lₙ`, normalization of U⁻ and of the predicative hierarchy, adequacy of the translation). `make assumptions` generates `checks/Assumptions.v` from the proved contracts of both files, prints their assumptions and fails unless all are closed. |
| `Examples.v` | The lecture examples shared by the tests and the OCaml demos: the polymorphic identity and its application, the forbidden rule (∗,□), large elimination, the raw Ω. The raw Ω is `raw_omega`, apart from the `omega` of Hurkens' paradox. |
| `CIC/Impredicative.v` | Prop on the unchanged checker (lecture 8): `ΠA:Type_i. P A : Prop` for `P : Type_i → Prop` at every level (by runs, and for all `i` by the annotated rules), the same product into Type₀ one level up, `ΠP:Prop. P : Prop`, the identity on propositions applied to its own type against the rejected one on Type₀; `Prop : Type₁`, and `Type₀ : Type₀`, `Prop : Prop`, `Prop : Type₀` rejected; the four rows of Σ, the pair of a witness and a proof, its projections, and the Σ rejected as a proposition. |
| `CIC/Match.v` | match and fix (lecture 8) on the hand-written signatures: `nat_rect` by fix and match against the type of `elimNat[j]` at three levels, the ι-equations of both implementations on open terms, `plus`, `append` on vectors with its index computed by `plus`, `copy` on W with the call under a λ, neutral match and fix on free variables, refusals (a missing or a repeated branch, a wrong motive, a scrutinee of another type, a motive into a sort the category refuses, a structural position past the telescope, a structural argument of a non-inductive type, a body without enough λ), `fix f n := f n` refused by the guard, and `eval_src` on the same programs. |
| `CIC/GuardExamples.v` | The guard on examples: `half` directly, the programs of `CIC/Match.v`, `size` over `Tr` with a field of two positions, calls under several λ and an inner match accepted; a call on the structural argument, `g (pred k)`, a partial call, the bare function passed on, an invalid call inside a valid one and a shadowing binder refused after typing; a call on a non-recursive field and a field applied to one of two positions refused by the guard alone. |
| `Tests.v` | Substitution without capture, open terms, PTS tables, normal order, bounded evaluation and traces, conversion without η, declarative versus annotated typing, admissibility of expected types, and the checker on U⁻ and the predicative hierarchy (lecture traces of `id A x` and of large elimination, the forbidden rule (∗,□), the universe level of ΠA:Type₀. A → A, large elimination, and each kind of error), and validation of inputs (an unbound annotation in the expected type, the top sort △ accepted, ill-formed contexts). |

## Planned layout

```text
theories/
  Common/          results, errors, traces
  PTS/             syntax, substitution, typing, reduction, checker
  Configs/         U⁻, λC, the predicative hierarchy, with and without Prop
  SystemU/         looping combinator and encodings
  PCFTranslation/  name bridge, translation, type preservation, adequacy
  MLTT/            primitives and dependent eliminators
  CIC/             Prop, match and fix, the guard (lecture 8)
  PTS/Contracts.v  proved interfaces of the kernel
  Contracts.v      proved interfaces of lecture 6 and their assumptions
  Examples.v
  Tests.v
extraction/        Extract.v, generated/ (never edited), pretty.ml, main.ml
reference/         standalone readable OCaml version and differential tests
tests/             regressions and differential tests
```

Ports from sibling projects are recorded in [PORTING.md](PORTING.md).
