(** * The answers of a call-by-value evaluator

    A value, a stuck term, or a run out of its budget, over the terms of
    any language: the evaluator of source programs (PTS.EvalSrc) and the
    evaluators of the languages programs are compiled to share it.  A
    timeout is inconclusive: it says neither that the program diverges
    nor that it gets stuck. *)

Inductive cbv_result (T : Type) : Type :=
| CbvValue : T -> cbv_result T
| CbvStuck : T -> cbv_result T
| CbvOutOfFuel : cbv_result T.

Arguments CbvValue {T} _.
Arguments CbvStuck {T} _.
Arguments CbvOutOfFuel {T}.
