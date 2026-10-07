(** * The result monad

    A computation that succeeds with [Ok a] or fails with [Err e].  Every
    algorithm of the development is written in it or, when it also logs
    events, in the trace monad of Common.Traced built on top of it.

    The lemmas invert a success: [bind_ok] splits a successful [let*]
    into two successful steps, and the tactic [bind_in] applies it to a
    hypothesis.

    Ported from modules-system-fw (see PORTING.md). *)

From Stdlib Require Import List.
Import ListNotations.

Inductive result (E A : Type) : Type :=
| Ok : A -> result E A
| Err : E -> result E A.

Arguments Ok {E A} _.
Arguments Err {E A} _.

Definition bind {E A B} (r : result E A) (f : A -> result E B) : result E B :=
  match r with
  | Ok a => f a
  | Err e => Err e
  end.

(** Whether a computation succeeded, forgetting its value. *)
Definition is_ok {E A} (r : result E A) : bool :=
  match r with
  | Ok _ => true
  | Err _ => false
  end.

Lemma is_ok_iff : forall {E A} (r : result E A), is_ok r = true <-> exists a, r = Ok a.
Proof.
  intros E A [a | e]; cbn; split; intros H.
  - now exists a.
  - reflexivity.
  - discriminate.
  - now destruct H.
Qed.

Definition map_err {E E' A} (f : E -> E') (r : result E A) : result E' A :=
  match r with
  | Ok a => Ok a
  | Err e => Err (f e)
  end.

Notation "'let*' x ':=' r 'in' body" := (bind r (fun x => body))
  (at level 200, x name, r at level 100, body at level 200).

Fixpoint mapM {E A B} (f : A -> result E B) (l : list A) : result E (list B) :=
  match l with
  | [] => Ok []
  | a :: rest =>
      let* b := f a in
      let* bs := mapM f rest in
      Ok (b :: bs)
  end.

(** A check: [Ok tt] if [b] holds, the error [e] otherwise. *)
Definition require {E} (b : bool) (e : E) : result E unit :=
  if b then Ok tt else Err e.

(** Inverting a success. *)

Lemma bind_ok : forall {E A B} (r : result E A) (f : A -> result E B) b,
    bind r f = Ok b -> exists a, r = Ok a /\ f a = Ok b.
Proof. intros E A B r f b H. destruct r as [a | e]; [ now exists a | discriminate ]. Qed.

Lemma map_err_ok : forall {E E' A} (f : E -> E') (r : result E A) a,
    map_err f r = Ok a -> r = Ok a.
Proof. intros E E' A f r a H. destruct r; cbn in H; congruence. Qed.

Lemma require_ok : forall {E} b (e : E) u, require b e = Ok u -> b = true.
Proof. intros E [] e u H; [ reflexivity | discriminate ]. Qed.

Ltac bind_in H x Hx := apply bind_ok in H as (x & Hx & H); cbv beta zeta in H.
