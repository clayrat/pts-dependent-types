(** * The source language: PCF of strictness-pcf

    The source PCF is not reimplemented: its syntax, typing, checker and
    call-by-name evaluator come from the pinned submodule
    vendor/strictness-pcf (logical prefix [PCF]).  Arguments of functions
    are passed by name; [succ], [pred] and the condition of [ifz] are
    strict; branches are not evaluated before the choice.

    PCF keeps named variables and its own [result] type, so its modules are
    required here without being imported; the adapters of the translation
    refer to them through the names below. *)

From PCF Require Ty Syntax Context Typing Checker OperationalSemantics Safety.

Notation pcf_ty := PCF.Ty.ty.
Notation pcf_term := PCF.Syntax.term.
Notation pcf_ctx := PCF.Context.ctx.
Notation pcf_has_type := PCF.Typing.has_type.
Notation pcf_check := PCF.Checker.check.
Notation pcf_eval := PCF.OperationalSemantics.evalFuel.
Notation pcf_diverges := PCF.OperationalSemantics.diverges.
