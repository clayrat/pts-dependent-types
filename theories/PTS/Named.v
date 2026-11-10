(** * Named terms: a builder for de Bruijn terms

    Terms of the lecture are written with names and resolved to the
    de Bruijn syntax of PTS.Syntax.  [nterm] mirrors [term] constructor
    by constructor, with a name at each binder; [resolve] replaces every
    variable by the index of its nearest binder, or of an entry of the
    given names of the context, and fails with the first unbound name.
    Every string is an ordinary name.

    The non-dependent arrow [A ~> B] binds nothing: [B] is resolved in
    the names around the arrow and lifted past the binder of the Π, as
    [arrow] of PTS.Syntax does; the product [A ⨯ B] is resolved the same
    way into a Σ.  A constant [NConst g] is not a name: it refers to the
    signature, not to the context.

    [NCase D s P x bs] is a match, with the motive and the branches
    written as named λ like any other term; [NFix f A k b] binds the
    name [f] of the function in its body [b].

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
| NElimBool : nterm -> nterm -> nterm -> nterm -> nterm
| NSigma : string -> nterm -> nterm -> nterm
| NTimes : nterm -> nterm -> nterm
| NPair : nterm -> nterm -> nterm
| NFst : nterm -> nterm
| NSnd : nterm -> nterm
| NConst : gref -> nterm
| NCase : string -> sort -> nterm -> nterm -> list nterm -> nterm
| NFix : string -> nterm -> nat -> nterm -> nterm.

(** Induction with the branches of a match, as [term_ind'] of
    PTS.Syntax. *)
Section NTermInd.
  Variable P : nterm -> Prop.
  Hypothesis HSrt : forall s, P (NSrt s).
  Hypothesis HVar : forall x, P (NVar x).
  Hypothesis HPi : forall x t1, P t1 -> forall t2, P t2 -> P (NPi x t1 t2).
  Hypothesis HArrow : forall t1, P t1 -> forall t2, P t2 -> P (NArrow t1 t2).
  Hypothesis HLam : forall x t, P t -> P (NLam x t).
  Hypothesis HApp : forall t1, P t1 -> forall t2, P t2 -> P (NApp t1 t2).
  Hypothesis HAnn : forall t1, P t1 -> forall t2, P t2 -> P (NAnn t1 t2).
  Hypothesis HVoid : P NVoid.
  Hypothesis HElimVoid : forall t1, P t1 -> forall t2, P t2 -> P (NElimVoid t1 t2).
  Hypothesis HUnit : P NUnit.
  Hypothesis HTt : P NTt.
  Hypothesis HElimUnit : forall t1, P t1 -> forall t2, P t2 -> forall t3, P t3 -> P (NElimUnit t1 t2 t3).
  Hypothesis HBool : P NBool.
  Hypothesis HTrue : P NTrue.
  Hypothesis HFalse : P NFalse.
  Hypothesis HElimBool : forall t1, P t1 -> forall t2, P t2 -> forall t3, P t3 -> forall t4, P t4 ->
    P (NElimBool t1 t2 t3 t4).
  Hypothesis HSigma : forall x t1, P t1 -> forall t2, P t2 -> P (NSigma x t1 t2).
  Hypothesis HTimes : forall t1, P t1 -> forall t2, P t2 -> P (NTimes t1 t2).
  Hypothesis HPair : forall t1, P t1 -> forall t2, P t2 -> P (NPair t1 t2).
  Hypothesis HFst : forall t, P t -> P (NFst t).
  Hypothesis HSnd : forall t, P t -> P (NSnd t).
  Hypothesis HConst : forall g, P (NConst g).
  Hypothesis HCase : forall D s t1, P t1 -> forall t2, P t2 -> forall l (IHl : Forall P l),
    P (NCase D s t1 t2 l).
  Hypothesis HFix : forall f t1, P t1 -> forall n t2, P t2 -> P (NFix f t1 n t2).

  Fixpoint nterm_ind' (t : nterm) : P t :=
    match t with
    | NSrt s => HSrt s
    | NVar x => HVar x
    | NPi x A B => HPi x A (nterm_ind' A) B (nterm_ind' B)
    | NArrow A B => HArrow A (nterm_ind' A) B (nterm_ind' B)
    | NLam x b => HLam x b (nterm_ind' b)
    | NApp f a => HApp f (nterm_ind' f) a (nterm_ind' a)
    | NAnn u A => HAnn u (nterm_ind' u) A (nterm_ind' A)
    | NVoid => HVoid
    | NElimVoid C e => HElimVoid C (nterm_ind' C) e (nterm_ind' e)
    | NUnit => HUnit
    | NTt => HTt
    | NElimUnit C c u => HElimUnit C (nterm_ind' C) c (nterm_ind' c) u (nterm_ind' u)
    | NBool => HBool
    | NTrue => HTrue
    | NFalse => HFalse
    | NElimBool C bt bf b =>
        HElimBool C (nterm_ind' C) bt (nterm_ind' bt) bf (nterm_ind' bf) b (nterm_ind' b)
    | NSigma x A B => HSigma x A (nterm_ind' A) B (nterm_ind' B)
    | NTimes A B => HTimes A (nterm_ind' A) B (nterm_ind' B)
    | NPair a b => HPair a (nterm_ind' a) b (nterm_ind' b)
    | NFst p => HFst p (nterm_ind' p)
    | NSnd p => HSnd p (nterm_ind' p)
    | NConst g => HConst g
    | NCase D s M x bs =>
        HCase D s M (nterm_ind' M) x (nterm_ind' x) bs
          ((fix all (bs : list nterm) : Forall P bs :=
              match bs with
              | [] => Forall_nil P
              | b :: bs' => Forall_cons b (nterm_ind' b) (all bs')
              end) bs)
    | NFix f A k b => HFix f A (nterm_ind' A) k b (nterm_ind' b)
    end.
End NTermInd.

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
  | NSigma x A B =>
      let* A' := resolve names A in
      let* B' := resolve (x :: names) B in
      Ok (Sigma A' B')
  | NTimes A B =>
      let* A' := resolve names A in
      let* B' := resolve names B in
      Ok (times A' B')
  | NPair a b =>
      let* a' := resolve names a in
      let* b' := resolve names b in
      Ok (Pair a' b')
  | NFst p => let* p' := resolve names p in Ok (Fst p')
  | NSnd p => let* p' := resolve names p in Ok (Snd p')
  | NConst g => Ok (Const g)
  | NCase D s P x bs =>
      let* P' := resolve names P in
      let* x' := resolve names x in
      let* bs' := mapM (resolve names) bs in
      Ok (Case D s P' x' bs')
  | NFix f A k b =>
      let* A' := resolve names A in
      let* b' := resolve (f :: names) b in
      Ok (Fix A' k b')
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
  induction t using nterm_ind'; intros bs ns t' H.
  (* the branches of a match *)
  all: try lazymatch goal with
       | IHl : Forall _ ?l |- resolve _ (NCase _ _ _ _ ?l) = _ =>
           cbn [resolve] in H |- *; resolve_inv H;
           apply mapM_ok in Hr1;
           rewrite (IHt1 _ _ _ Hr), (IHt2 _ _ _ Hr0); cbn [bind];
           replace (mapM (resolve (bs ++ ns)) l) with (Ok r1 : result string (list term));
           [exact H | ];
           clear - IHl Hr1; induction Hr1 as [|a b l l' Ha _ IH]; [reflexivity | ];
           inversion IHl; subst; cbn; rewrite (H1 _ _ _ Ha); cbn; rewrite <- IH by assumption; reflexivity
       end.
  (* a variable: its nearest binder lies among [bs] *)
  all: try lazymatch goal with
       | H : resolve _ (NVar ?x) = _ |- _ =>
           cbn in H |- *; destruct (index_of x bs) eqn:E; [ | discriminate H];
           rewrite (index_of_app _ _ ns _ E); exact H
       end.
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
  induction t using nterm_ind'; intros names t' H.
  (* the branches of a match *)
  all: try lazymatch goal with
       | IHl : Forall _ ?l |- _ =>
           cbn [resolve] in H; resolve_inv H; injection H as <-;
           apply mapM_ok in Hr1; cbn [closed_above];
           rewrite (IHt1 _ _ Hr), (IHt2 _ _ Hr0); cbn;
           clear - IHl Hr1; induction Hr1 as [|a b l l' Ha _ IH]; [reflexivity | ];
           inversion IHl; subst; cbn; rewrite (H1 _ _ Ha); cbn; apply IH; assumption
       end.
  (* a variable: its index is below the number of names *)
  all: try lazymatch goal with
       | H : resolve _ (NVar ?x) = _ |- _ =>
           cbn in H; destruct (index_of x names) eqn:E; [ | discriminate H];
           injection H as <-; cbn; apply Nat.ltb_lt, (index_of_lt x), E
       end.
  all: cbn [resolve] in H; resolve_inv H; injection H as <-; unfold arrow, times; cbn.
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

(** [h a₁ … aₙ], as [apps] of PTS.Syntax for named terms. *)
Definition napps (h : nterm) (args : list nterm) : nterm := fold_left NApp args h.
Coercion napp : nterm >-> Funclass.

Notation "'λ' x , b" := (NLam x b)
  (at level 200, x at level 0, b at level 200, right associativity) : nterm_scope.
Notation "'Π' x : A , B" := (NPi x A B)
  (at level 200, x at level 0, A at level 200, B at level 200, right associativity)
  : nterm_scope.
Notation "'Σ' x : A , B" := (NSigma x A B)
  (at level 200, x at level 0, A at level 200, B at level 200, right associativity)
  : nterm_scope.
Notation "A ~> B" := (NArrow A B) (at level 99, right associativity) : nterm_scope.
Notation "A ⨯ B" := (NTimes A B) (at level 98, right associativity) : nterm_scope.
Notation "⟨ a , b ⟩" := (NPair a b) (at level 0, a at level 200, b at level 200) : nterm_scope.
Notation "t ∷ A" := (NAnn t A) (at level 100, no associativity) : nterm_scope.
Notation "⋆" := (NSrt Star) : nterm_scope.
Notation "□" := (NSrt Box) : nterm_scope.
Notation "△" := (NSrt Tri) : nterm_scope.
Notation "'Type@' i" := (NSrt (Univ i)) (at level 0, i at level 0) : nterm_scope.
