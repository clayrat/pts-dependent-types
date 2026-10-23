# Native OCaml reference

`pts_native.ml` is a hand-written, standalone version of the executable PTS
kernel. It has its own syntax and specifications, capture-avoiding substitution,
normal-order evaluator, weak-head reduction, conversion, and bidirectional
checker with errors and traces. Its inference and checking functions
correspond to the single structurally recursive `tc` in Rocq.

It covers the extension of the lecture on inductive types as well: Σ with
pairs and projections, and the constants of a signature, a list of entries
(classified descriptions, eliminator instances with the flag of active
ι-rules, δ-constants) with its own closedness check in `sig_add`, the types
of inductive types and constructors rebuilt from descriptions, δ, and ι by
the scheme of descriptions. Evaluation and checking take the signature as an
optional `~sg`, the empty one by default, so the callers of lecture 6 are
unchanged.

`looping.ml` independently builds the Hurkens-derived looping combinator
from named OCaml terms, resolves binders to de Bruijn indices, and defines
the family `Lₙ`. It fails on an unbound name. The differential test compares
these native terms with the Rocq extract before running the native checker
and evaluator on them.

`encodings.ml` builds, with the same builder, the Church numerals and booleans,
Kleene's predecessor, the zero test strict in the whole numeral and the PCF
strictness programs. The differential test compares the terms, their complete
typing traces in U⁻, and their bounded normal-order results and decoded
numerals with the extract.

`translate.ml` is a native PCF-to-U- translator with its own PCF syntax and two
mutually recursive functions following the bidirectional PCF checker. The
differential test compares its translations and first errors with the extracted
`translate` on every program of `Programs.v`, on ill-typed programs, open
contexts and shadowing, and the normal-order results of short translations.

`choose.ml` builds `choose` of the minimal MLTT with the same builder, now able
to write the primitives and their eliminators. The differential test compares
its terms, contexts, complete checker traces and normal forms with the extract.
`eliminators.ml` does the same for the eliminators of Void and Unit.

`pairs.ml` builds the dependent pairs of `MLTT/Pairs.v` with the builder, which
also writes Σ, products, pairs and projections. `constants.ml` builds the
hand-written signature of `MLTT/Constants.v` (ℕ, `elimNat[0]`, `double`) entry
by entry through the native `sig_add`. The differential test compares the
terms and the signatures, the types of constants, complete checker traces in
the signature with active rules, without them, in U⁻ and in the empty
signature, and normal-order traces, normal forms, weak-head forms and
conversions, which exercise δ, ι on closed and open terms and the
object-first order of full spines.

`families.ml` builds the families of `MLTT/Families.v` (`Vec`, `W`, `Tr`) and
their signature the same way. For every ι-rule on open terms the differential
test checks that the native contraction is the right side written by hand and
equals the extracted one, compares the conversion of the two sides and their
complete checker traces against the motive at the constructor, also for
right sides with a swapped index or swapped positions, and compares the
closed computations. These rules exercise what ℕ leaves idle: the lifts under
the positions of a recursive field, the instantiation of its indices with
the positions, the earlier fields and the parameters, the order of several
positions, and fields after a recursive one.

Run the examples directly, as with `strictness-pcf/reference/pcf_native.ml`:

```sh
ocaml reference/pts_native.ml
```

`diff.ml` compares the native implementation with the generated Rocq extract.
It checks specification tables (with their Σ-rules and the switch of
constants), evaluation results and traces, conversion, checker answers and
complete typing event logs on shared examples, including the looping
combinator and samples with Σ in every configuration. From the
repository root:

```sh
make -C reference test
# or: make test   (also runs the extraction's printer regressions)
```

The extracted code remains the reference for proved properties. Rocq's
soundness theorems do not apply to this manually written implementation;
differential tests detect discrepancies on the exercised inputs. Both OCaml
versions use machine integers for Rocq natural numbers, so callers should
provide nonnegative values that do not overflow `int`.
