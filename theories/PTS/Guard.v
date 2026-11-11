(** * The guard of fix

    [Fix A k b] is accepted only if every recursive call in its body is on
    a strict subterm of its structural argument, the [k]-th.  The guard
    walks the body with a mark for each variable of the context:
    - [Self]: the function itself, [Var 0] at the entry of the body;
    - [Arg]: the structural argument, given to the [k]-th leading λ; the
      other leading λ get [Large];
    - [Sub m]: a strict subterm of the structural argument once applied
      to [m] arguments: [Sub 0] an ordinary recursive field, [Sub m] a
      functional recursive field with [m] positions;
    - [Large]: nothing is known; every new binder gets it.
    Entering a binder pushes a mark, so the marks of the outer context
    follow their variables with their shifted indices: a call under a λ,
    as in [sup a (λb. copy (f b))], is recognized.

    A [match] whose scrutinee is the structural argument, or a recognized
    strict subterm, gives the fields its branches bind marks from the
    description: a recursive field [Πȳ:B̄. D Δ v̄] gets [Sub |B̄|], a
    non-recursive one [Large], whatever its type after the parameters are
    substituted.  The branch binds them with its leading λ; past them, or
    in a match on anything else, binders get [Large].

    Every occurrence of the function is checked.  The maximal spine of
    its applications is taken whole: with at most [k] arguments it is a
    partial call ([GPartialCall]), the bare function passed to another
    one included; otherwise the argument at [k] must be a variable marked
    [Sub m] applied to exactly [m] arguments ([GNotSubterm]).  The
    structural argument itself does not do.  The arguments of an accepted
    call are checked in turn, so an invalid call inside the argument of a
    valid one is found.

    The origin of a subterm is not recovered through the application of
    an arbitrary function, β- or δ-reduction, or a new name: a call on
    [pred k], or on [(λy. y) k], is refused.  The guard of Rocq accepts
    more, and none of it is needed here: it reduces the terms it checks
    (head normal forms, unfolding of constants and β), follows subterms
    through a match whose branches return functions (commutative cuts)
    and through nested fixpoints, checks mutual fixpoints, and treats
    nested inductive types.  An inner [Fix] in a body gets [Large] for its
    own function: its body is guarded when it is typed.

    The soundness of [guard] with respect to the judgment [Guarded], and
    the meaning of the marks, are in PTS.GuardSound: the typing rules
    need only the judgment, and the checker only the algorithm. *)

From Stdlib Require Import List Bool Arith.
From Stdlib Require String.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Signature.

Local Notation string := String.string.

(** ** Marks *)

Inductive mark : Type :=
| Large : mark
| Arg : mark
| Sub : nat -> mark
| Self : mark.

Definition mark_at (ms : list mark) (i : nat) : mark := nth i ms Large.

Definition is_self (m : mark) : bool := match m with Self => true | _ => false end.

(** The marks at the entry of a body: the structural argument, the [k]
    arguments before it, the function. *)
Definition entry_marks (k : nat) : list mark := Arg :: repeat Large k ++ [Self].

(** A recursive field is a strict subterm once applied to its positions. *)
Definition field_mark (fd : field) : mark :=
  match fd with
  | FArg _ => Large
  | FRec Bs _ => Sub (length Bs)
  end.

Inductive guard_error : Type :=
| GPartialCall : term -> guard_error            (** a call with at most [k] arguments *)
| GNotSubterm : term -> term -> guard_error     (** a call and its structural argument *)
| GShortBody : term -> guard_error.             (** a body short of its [k + 1] λ: where one is missing *)

Section Guard.
  Variable sg : signature.
  Variable k : nat.

  (** A variable marked [Sub m] applied to exactly [m] arguments. *)
  Definition sub_arg (ms : list mark) (a : term) : bool :=
    match spine_head a with
    | Var i => match mark_at ms i with Sub m => Nat.eqb (length (spine_args a)) m | _ => false end
    | _ => false
    end.

  Definition is_arg (ms : list mark) (x : term) : bool :=
    match x with
    | Var i => match mark_at ms i with Arg => true | _ => false end
    | _ => false
    end.

  (** A scrutinee whose recursive fields are strict subterms. *)
  Definition origin (ms : list mark) (x : term) : bool := is_arg ms x || sub_arg ms x.

  Definition self_headed (ms : list mark) (t : term) : bool :=
    match spine_head t with
    | Var i => is_self (mark_at ms i)
    | _ => false
    end.

  (** The fields of the constructors of D, for the branches of a match on
      a structural origin; nothing otherwise. *)
  Definition branch_fields (ms : list mark) (D : string) (x : term) : list (list field) :=
    if origin ms x then
      match sig_ind sg D with
      | Some d => map ctor_fields (ind_ctors d)
      | None => []
      end
    else [].

  (** The leading λ of a branch, with the marks of the fields they bind. *)
  Fixpoint peel (ms : list mark) (fds : list field) (b : term) : list mark * term :=
    match fds, b with
    | fd :: fds', Lam b' => peel (field_mark fd :: ms) fds' b'
    | _, _ => (ms, b)
    end.

  (** The call heading the maximal spine [t], if the function heads it. *)
  Definition call_ok (ms : list mark) (t : term) : result guard_error unit :=
    if self_headed ms t then
      let args := spine_args t in
      if Nat.ltb k (length args) then
        if sub_arg ms (nth k args (Var 0)) then Ok tt else Err (GNotSubterm t (nth k args (Var 0)))
      else Err (GPartialCall t)
    else Ok tt.

  (** [peel_with g ms fds b] is [g] after [peel] ([peel_with_peel] of
      PTS.GuardSound).  It is written by recursion on the branch, not as
      [g] applied to the pair [peel] returns, so that the guard condition
      of [guard] sees [g] applied to a subterm of the match. *)
  Fixpoint peel_with (g : list mark -> term -> result guard_error unit) (ms : list mark)
    (fds : list field) (b : term) {struct b} : result guard_error unit :=
    match fds, b with
    | fd :: fds', Lam b' => peel_with g (field_mark fd :: ms) fds' b'
    | _, _ => g ms b
    end.

  (** Each branch with the fields of its constructor, in order.  [fss] is
      empty when the scrutinee is not a structural origin
      ([branch_fields]): [hd] and [tl] of the empty list then give every
      branch no field, so all its binders get [Large]. *)
  Fixpoint each_branch (g : list mark -> term -> result guard_error unit) (ms : list mark)
    (fss : list (list field)) (bs : list term) {struct bs} : result guard_error unit :=
    match bs with
    | [] => Ok tt
    | b :: bs' => let* _ := peel_with g ms (hd [] fss) b in each_branch g ms (tl fss) bs'
    end.

  (** [spine]: [t] is the function part of an application whose maximal
      spine was checked already. *)
  Fixpoint guard (ms : list mark) (t : term) (spine : bool) {struct t} : result guard_error unit :=
    match t with
    | Var i => if spine then Ok tt else if is_self (mark_at ms i) then Err (GPartialCall t) else Ok tt
    | App f a =>
        let* _ := if spine then Ok tt else call_ok ms t in
        let* _ := guard ms f true in
        guard ms a false
    | Lam b => guard (Large :: ms) b false
    | Pi A B | Sigma A B | Fix A _ B => let* _ := guard ms A false in guard (Large :: ms) B false
    | Ann u A | ElimVoid u A | Pair u A => let* _ := guard ms u false in guard ms A false
    | ElimUnit C c u => let* _ := guard ms C false in let* _ := guard ms c false in guard ms u false
    | ElimBool C t' f b =>
        let* _ := guard ms C false in let* _ := guard ms t' false in
        let* _ := guard ms f false in guard ms b false
    | Fst p | Snd p => guard ms p false
    | Case D _ P x bs =>
        let* _ := guard ms P false in
        let* _ := guard ms x false in
        each_branch (fun ms' b => guard ms' b false) ms (branch_fields ms D x) bs
    | Srt _ | Void | Unit | Tt | Bool | BTrue | BFalse | Const _ => Ok tt
    end.

  (** The body after its [k + 1] leading λ, with the marks of the entry;
      a body without them is refused. *)
  Fixpoint guard_entry (n : nat) (ms : list mark) (b : term) : result guard_error unit :=
    match n, b with
    | O, Lam b' => guard (Arg :: ms) b' false
    | S n', Lam b' => guard_entry n' (Large :: ms) b'
    | _, _ => Err (GShortBody b)
    end.

  Definition guard_fix (b : term) : result guard_error unit := guard_entry k [Self] b.

  (** ** The rules as a judgment *)

  Definition atomic (t : term) : bool :=
    match t with
    | Srt _ | Void | Unit | Tt | Bool | BTrue | BFalse | Const _ => true
    | _ => false
    end.

  Inductive Guarded : list mark -> term -> Prop :=
  | G_Call : forall ms i args,
      mark_at ms i = Self -> k < length args -> sub_arg ms (nth k args (Var 0)) = true ->
      (forall a, In a args -> Guarded ms a) ->
      Guarded ms (apps (Var i) args)
  | G_Var : forall ms i, is_self (mark_at ms i) = false -> Guarded ms (Var i)
  | G_App : forall ms f a,
      self_headed ms (App f a) = false -> Guarded ms f -> Guarded ms a -> Guarded ms (App f a)
  | G_Lam : forall ms b, Guarded (Large :: ms) b -> Guarded ms (Lam b)
  | G_Pi : forall ms A B, Guarded ms A -> Guarded (Large :: ms) B -> Guarded ms (Pi A B)
  | G_Sigma : forall ms A B, Guarded ms A -> Guarded (Large :: ms) B -> Guarded ms (Sigma A B)
  | G_Fix : forall ms A k' b, Guarded ms A -> Guarded (Large :: ms) b -> Guarded ms (Fix A k' b)
  | G_Ann : forall ms u A, Guarded ms u -> Guarded ms A -> Guarded ms (Ann u A)
  | G_ElimVoid : forall ms C e, Guarded ms C -> Guarded ms e -> Guarded ms (ElimVoid C e)
  | G_Pair : forall ms a b, Guarded ms a -> Guarded ms b -> Guarded ms (Pair a b)
  | G_ElimUnit : forall ms C c u, Guarded ms C -> Guarded ms c -> Guarded ms u ->
      Guarded ms (ElimUnit C c u)
  | G_ElimBool : forall ms C t f b, Guarded ms C -> Guarded ms t -> Guarded ms f -> Guarded ms b ->
      Guarded ms (ElimBool C t f b)
  | G_Fst : forall ms p, Guarded ms p -> Guarded ms (Fst p)
  | G_Snd : forall ms p, Guarded ms p -> Guarded ms (Snd p)
  | G_Case : forall ms D s P x bs, Guarded ms P -> Guarded ms x ->
      (forall j b, nth_error bs j = Some b ->
         let p := peel ms (nth j (branch_fields ms D x) []) b in Guarded (fst p) (snd p)) ->
      Guarded ms (Case D s P x bs)
  | G_Atom : forall ms t, atomic t = true -> Guarded ms t.

  (** A body is guarded after its [k + 1] leading λ. *)
  Definition fix_guarded (b : term) : Prop :=
    exists body, b = lams (S k) body /\ Guarded (entry_marks k) body.

End Guard.

(** Peeling the leading λ off a body keeps [allnodes]. *)
Lemma an_peel : forall pc pk fds ms b, allnodes pc pk b = true ->
  allnodes pc pk (snd (peel ms fds b)) = true.
Proof.
  intros pc pk fds. induction fds as [|fd fds IH]; intros ms b H; [exact H | ].
  destruct b; try exact H. exact (IH _ b H).
Qed.
