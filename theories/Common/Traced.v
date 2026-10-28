(** * The trace monad: result with an event log

    The PTS checker records its lecture trace (Π unfolding, argument checks,
    substitutions, queries to the PTS specification) in this monad: a
    computation that may fail with an error of type [E] and appends events
    of type [Ev] to a log.  The log is kept in reverse
    order while running; [run_traced] starts from the empty log and returns
    it in chronological order.

    The lemmas decompose a successful run: [tbind_ok] splits a successful
    [let!] into two successful steps, the tactic [tbind_in] applies it to
    a hypothesis, and [tbind_step] rebuilds one.  Over a list, [titer]
    runs a step on every element in turn and [tfold] threads a value
    through the steps; every step of a successful [titer] succeeds
    ([titer_Forall]).

    Ported from modules-system-fw (see PORTING.md). *)

From Stdlib Require Import List.
Import ListNotations.

From DepTypes.Common Require Import Result.

Definition traced (Ev E A : Type) : Type := list Ev -> list Ev * result E A.

Section Traced.
  Context {Ev E : Type}.

  Definition tret {A} (a : A) : traced Ev E A := fun log => (log, Ok a).

  Definition tfail {A} (e : E) : traced Ev E A := fun log => (log, Err e).

  Definition temit (event : Ev) : traced Ev E unit :=
    fun log => (event :: log, Ok tt).

  (** A check: go on if [b] holds, fail with [e] otherwise. *)
  Definition trequire (b : bool) (e : E) : traced Ev E unit :=
    if b then tret tt else tfail e.

  Definition tbind {A B} (m : traced Ev E A) (f : A -> traced Ev E B)
      : traced Ev E B :=
    fun log =>
      match m log with
      | (log', Ok a) => f a log'
      | (log', Err e) => (log', Err e)
      end.

  Definition run_traced {A} (m : traced Ev E A) : list Ev * result E A :=
    let (log, r) := m [] in (rev log, r).

  (** ** Successful runs *)

  Lemma tbind_ok : forall {A B} (m : traced Ev E A) (f : A -> traced Ev E B) log log' b,
      tbind m f log = (log', Ok b) ->
      exists log1 a, m log = (log1, Ok a) /\ f a log1 = (log', Ok b).
  Proof.
    intros A B m f log log' b H. unfold tbind in H.
    destruct (m log) as [log1 [a | e]]; [ | discriminate ].
    now exists log1, a.
  Qed.

  Lemma tbind_step : forall {A B} (m : traced Ev E A) (f : A -> traced Ev E B) log log1 a,
      m log = (log1, Ok a) -> tbind m f log = f a log1.
  Proof. intros A B m f log log1 a H. unfold tbind. now rewrite H. Qed.

  Lemma tret_ok : forall {A} (a : A) log log' b, tret a log = (log', Ok b) -> b = a.
  Proof. intros A a log log' b H. unfold tret in H. congruence. Qed.

  Lemma tfail_ok : forall {A} e log log' (b : A), tfail e log = (log', Ok b) -> False.
  Proof. intros A e log log' b H. unfold tfail in H. discriminate. Qed.

  Lemma run_traced_ok : forall {A} (m : traced Ev E A) a,
      snd (run_traced m) = Ok a -> exists log, m [] = (log, Ok a).
  Proof.
    intros A m a H. unfold run_traced in H.
    destruct (m []) as [log r]. cbn in H. subst r. now exists log.
  Qed.

  Lemma run_traced_step : forall {A} (m : traced Ev E A) log a,
      m [] = (log, Ok a) -> snd (run_traced m) = Ok a.
  Proof. intros A m log a H. unfold run_traced. now rewrite H. Qed.
End Traced.

Notation "'let!' x ':=' m 'in' body" := (tbind m (fun x => body))
  (at level 200, x name, m at level 100, body at level 200).

Ltac tfail_contra H := exfalso; eapply tfail_ok; exact H.

(** Splits a successful [let!] in [H] into the step that gives [x], as
    [Hx], and the rest, still [H]; the intermediate log stays anonymous.
    The counterpart of [bind_in] of Common.Result. *)
Ltac tbind_in H x Hx := apply tbind_ok in H as (? & x & Hx & H); cbv beta in H.

(** ** Over lists *)

Section Lists.
  Context {Ev E : Type}.

  Fixpoint titer {A} (f : A -> traced Ev E unit) (l : list A) : traced Ev E unit :=
    match l with
    | [] => tret tt
    | a :: l' => let! _ := f a in titer f l'
    end.

  Fixpoint tfold {A B} (f : B -> A -> traced Ev E B) (b : B) (l : list A) : traced Ev E B :=
    match l with
    | [] => tret b
    | a :: l' => let! b' := f b a in tfold f b' l'
    end.

  Lemma titer_Forall : forall {A} (f : A -> traced Ev E unit) l log log' u,
    titer f l log = (log', Ok u) -> Forall (fun a => exists log1 log2 v, f a log1 = (log2, Ok v)) l.
  Proof.
    intros A f l. induction l as [|a l IH]; intros log log' u H; [constructor | ].
    cbn in H. apply tbind_ok in H as (log1 & v & Ha & H).
    constructor; [now exists log, log1, v | eapply IH; exact H].
  Qed.
End Lists.
