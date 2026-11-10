(** * Building the examples

    The examples write their terms with names (PTS.Named) and state them
    as de Bruijn terms.  These conveniences fall back on a default value
    when a name is unbound, so that an example stays a plain term rather
    than a [result]: [build] gives ∗, [in_ctx] the empty context.  Every
    example checks that its terms and contexts resolve ([resolves],
    [ctx_resolves] of PTS.Named), so a fallback never stands in for an
    error.  They are not part of the kernel: the checker and its proofs
    do not use them. *)

From Stdlib Require Import String List.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named.

(** The resolved term in the context [names], innermost first, or ∗ if a
    name is unbound. *)
Definition build (names : list string) (t : nterm) : term :=
  match resolve names t with
  | Ok u => u
  | Err _ => Srt Star
  end.

(** A named context, innermost entry first, and a term in it, as de
    Bruijn terms. *)
Definition in_ctx (g : list (string * nterm)) : ctx :=
  match resolve_ctx g with
  | Ok (_, G) => G
  | Err _ => []
  end.

Definition term_in (g : list (string * nterm)) (t : nterm) : term := build (map fst g) t.
