(** * Named terms: a builder for de Bruijn terms

    Terms of the lecture are written with names and resolved to the
    de Bruijn syntax of PTS.Syntax.  [nterm] mirrors [term] constructor
    by constructor, with a name at each binder; [resolve] replaces every
    variable by the index of its nearest binder, or of an entry of the
    given names of the context, and fails with the first unbound name.
    Every string is an ordinary name.

    The non-dependent arrow [A ~> B] binds nothing: [B] is resolved in
    the names around the arrow and lifted past the binder of the Π, as
    [arrow] of PTS.Syntax does.

    The builder is a convenience: it is not verified, and a term it
    produces is trusted only after the checker accepts it.

    Definitions are inlined at the Rocq level.  A definition used as a
    function is written closed and annotated, [(λ x, b) ∷ A]; a free name
    inside a definition is captured by the binders of the term it is
    pasted into, so definitions abstract over the names they need. *)

From Stdlib Require Import String List Arith Lia.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax.

Inductive nterm : Type :=
| NSrt : sort -> nterm
| NVar : string -> nterm
| NPi : string -> nterm -> nterm -> nterm
| NArrow : nterm -> nterm -> nterm
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
      match index_of x names with
      | Some n => Ok (Var n)
      | None => Err x
      end
  | NPi x A B =>
      let* A' := resolve names A in
      let* B' := resolve (x :: names) B in
      Ok (Pi A' B')
  | NArrow A B =>
      let* A' := resolve names A in
      let* B' := resolve names B in
      Ok (arrow A' B')
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

(** Whether a term, or a named context, resolves ([is_ok] of
    Common.Result): used to check that a fallback value of a convenience
    wrapper never stands in for an error. *)
Definition resolves (names : list string) (t : nterm) : bool := is_ok (resolve names t).
Definition ctx_resolves (g : list (string * nterm)) : bool := is_ok (resolve_ctx g).

(** ** Resolution and closed terms *)

Lemma index_of_app : forall x bs ns n,
  index_of x bs = Some n -> index_of x (bs ++ ns) = Some n.
Proof.
  induction bs as [|y bs IH]; intros ns n H; cbn in *; [discriminate | ].
  destruct (String.eqb x y); [exact H | ].
  destruct (index_of x bs) eqn:E; [ | discriminate]. injection H as <-.
  rewrite (IH ns n0 eq_refl). reflexivity.
Qed.

Lemma index_of_lt : forall x names n, index_of x names = Some n -> n < length names.
Proof.
  induction names as [|y names IH]; intros n H; cbn in *; [discriminate | ].
  destruct (String.eqb x y); [injection H as <-; lia | ].
  destruct (index_of x names) eqn:E; [ | discriminate]. injection H as <-.
  specialize (IH n0 eq_refl). lia.
Qed.

(** Splits the successful [let*] steps of a resolution. *)
Ltac resolve_inv H :=
  repeat match type of H with
  | bind _ _ = Ok _ =>
      let x := fresh "r" in let Hx := fresh "Hr" in apply bind_ok in H as (x & Hx & H)
  end.

(** A term resolved under some names resolves the same way under more
    names appended outside. *)
Lemma resolve_weaken : forall t bs ns t',
  resolve bs t = Ok t' -> resolve (bs ++ ns) t = Ok t'.
Proof.
  induction t; intros bs ns t' H.
  2: { cbn in H |- *. destruct (index_of s bs) eqn:E; [ | discriminate H].
       rewrite (index_of_app _ _ ns _ E). exact H. }
  all: cbn [resolve] in H |- *; resolve_inv H.
  all: repeat match goal with
       | IH : forall bs ns t', resolve bs ?u = Ok t' -> resolve (bs ++ ns) ?u = Ok t',
         Hr : resolve ?n ?u = Ok _ |- _ =>
           apply (IH n ns) in Hr; cbn [app] in Hr; rewrite Hr; clear Hr; cbn [bind]
       end.
  all: exact H.
Qed.
Lemma resolve_closed : forall t t' ns, resolve [] t = Ok t' -> resolve ns t = Ok t'.
Proof. intros t t' ns H. exact (resolve_weaken t [] ns t' H). Qed.

(** A resolved term mentions only the given names. *)
Lemma resolve_closed_above : forall t names t',
  resolve names t = Ok t' -> closed_above (length names) t' = true.
Proof.
  induction t; intros names t' H.
  2: { cbn in H. destruct (index_of s names) eqn:E; [ | discriminate H].
       injection H as <-. cbn. apply Nat.ltb_lt, (index_of_lt s), E. }
  all: cbn [resolve] in H; resolve_inv H; injection H as <-; unfold arrow; cbn.
  all: repeat match goal with
       | IH : forall names t', resolve names ?u = Ok t' -> closed_above (length names) t' = true,
         Hr : resolve _ ?u = Ok _ |- _ => apply IH in Hr; cbn [length] in Hr
       end.
  all: repeat (apply andb_true_intro; split);
    first [reflexivity | assumption | apply closed_above_lift1; assumption].
Qed.

Lemma resolve_closed_term : forall t t', resolve [] t = Ok t' -> closed t' = true.
Proof. intros t t' H. exact (resolve_closed_above t [] t' H). Qed.

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
Notation "A ~> B" := (NArrow A B) (at level 99, right associativity) : nterm_scope.
Notation "t ∷ A" := (NAnn t A) (at level 100, no associativity) : nterm_scope.
Notation "⋆" := (NSrt Star) : nterm_scope.
Notation "□" := (NSrt Box) : nterm_scope.
Notation "△" := (NSrt Tri) : nterm_scope.
Notation "'Type@' i" := (NSrt (Univ i)) (at level 0, i at level 0) : nterm_scope.
