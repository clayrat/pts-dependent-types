(** * Named terms: a builder for de Bruijn terms

    Terms of the lecture are written with names and resolved to the
    de Bruijn syntax of PTS.Syntax.  [nterm] mirrors [term] constructor
    by constructor, with a name at each binder; [resolve] replaces every
    variable by the index of its nearest binder, or of an entry of the
    given names of the context, and fails with the first unbound name.

    The binder name [anon] ("_") is never referred to: it makes the
    non-dependent arrow [A ~> B].

    The builder is a convenience: it is not verified, and a term it
    produces is trusted only after the checker accepts it.

    Definitions are inlined at the Rocq level.  A definition used as a
    function is written closed and annotated, [(λ x, b) ∷ A]; a free name
    inside a definition is captured by the binders of the term it is
    pasted into, so definitions abstract over the names they need. *)

From Stdlib Require Import String List.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax.

Inductive nterm : Type :=
| NSrt : sort -> nterm
| NVar : string -> nterm
| NPi : string -> nterm -> nterm -> nterm
| NLam : string -> nterm -> nterm
| NApp : nterm -> nterm -> nterm
| NAnn : nterm -> nterm -> nterm
| NVoid : nterm
| NElimVoid : nterm -> nterm -> nterm
| NUnit : nterm
| NTt : nterm
| NElimUnit : nterm -> nterm -> nterm -> nterm
| NBool : nterm
| NTrue : nterm
| NFalse : nterm
| NElimBool : nterm -> nterm -> nterm -> nterm -> nterm.

Definition anon : string := "_".

(** The index of the nearest binder named [x]. *)
Fixpoint index_of (x : string) (names : list string) : option nat :=
  match names with
  | [] => None
  | y :: rest => if String.eqb x y then Some 0 else option_map S (index_of x rest)
  end.

(** [resolve names t]: [names] are the names of the context, innermost
    first.  The error is the unbound name. *)
Fixpoint resolve (names : list string) (t : nterm) : result string term :=
  match t with
  | NSrt s => Ok (Srt s)
  | NVar x =>
      if String.eqb x anon then Err x
      else match index_of x names with
           | Some n => Ok (Var n)
           | None => Err x
           end
  | NPi x A B =>
      let* A' := resolve names A in
      let* B' := resolve (x :: names) B in
      Ok (Pi A' B')
  | NLam x b => let* b' := resolve (x :: names) b in Ok (Lam b')
  | NApp f a =>
      let* f' := resolve names f in
      let* a' := resolve names a in
      Ok (App f' a')
  | NAnn u A =>
      let* u' := resolve names u in
      let* A' := resolve names A in
      Ok (Ann u' A')
  | NVoid => Ok Void
  | NElimVoid C e =>
      let* C' := resolve names C in
      let* e' := resolve names e in
      Ok (ElimVoid C' e')
  | NUnit => Ok Unit
  | NTt => Ok Tt
  | NElimUnit C c u =>
      let* C' := resolve names C in
      let* c' := resolve names c in
      let* u' := resolve names u in
      Ok (ElimUnit C' c' u')
  | NBool => Ok Bool
  | NTrue => Ok BTrue
  | NFalse => Ok BFalse
  | NElimBool C t f b =>
      let* C' := resolve names C in
      let* t' := resolve names t in
      let* f' := resolve names f in
      let* b' := resolve names b in
      Ok (ElimBool C' t' f' b')
  end.

(** A named context, innermost entry first: each type is resolved in the
    names of the entries behind it.  Returns the names and the context. *)
Fixpoint resolve_ctx (g : list (string * nterm)) : result string (list string * ctx) :=
  match g with
  | [] => Ok ([], [])
  | (x, A) :: g' =>
      let* p := resolve_ctx g' in
      let (names, G) := p in
      let* A' := resolve names A in
      Ok (x :: names, A' :: G)
  end.

(** ** Notations

    Open [nterm_scope] together with [string_scope]: a string literal is a
    variable, and applying a named term to another is application. *)

Declare Scope nterm_scope.
Delimit Scope nterm_scope with nt.
Bind Scope nterm_scope with nterm.

Coercion NVar : string >-> nterm.
Definition napp (f : nterm) : nterm -> nterm := NApp f.
Coercion napp : nterm >-> Funclass.

Notation "'λ' x , b" := (NLam x b)
  (at level 200, x at level 0, b at level 200, right associativity) : nterm_scope.
Notation "'Π' x : A , B" := (NPi x A B)
  (at level 200, x at level 0, A at level 200, B at level 200, right associativity)
  : nterm_scope.
Notation "A ~> B" := (NPi anon A B) (at level 99, right associativity) : nterm_scope.
Notation "t ∷ A" := (NAnn t A) (at level 100, no associativity) : nterm_scope.
Notation "⋆" := (NSrt Star) : nterm_scope.
Notation "□" := (NSrt Box) : nterm_scope.
Notation "△" := (NSrt Tri) : nterm_scope.
Notation "'Type@' i" := (NSrt (Univ i)) (at level 0, i at level 0) : nterm_scope.
