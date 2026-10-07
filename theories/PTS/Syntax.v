(** * Unified syntax of terms and types

    One syntactic category for terms, types, kinds and sorts, with de
    Bruijn indices: [Var 0] is the innermost binder.  [Pi A B] and [Lam b]
    bind index 0 in [B] and [b].

    λ is unannotated (as in the PCF of strictness-pcf): it is checked
    against an expected Π-type, and a λ in a synthesizing position, e.g.
    the head of a β-redex, needs an annotation [Ann t A].

    Sorts cover both families of configurations: the named sorts ∗, □, △
    of λ∗, U and U⁻, and the predicative hierarchy [Univ i] = Type_i.
    Which of them exist, and how they are related, is decided by a PTS
    specification (PTS.Spec), not by the syntax.

    The primitives Void, Unit and Bool of the minimal MLTT are part of the
    syntax from the start; a specification enables them or not.  Their
    eliminators take an explicit result family [C]:
    - [ElimVoid C e]     : [C e]
    - [ElimUnit C c u]   : [C u], with [c : C tt]
    - [ElimBool C t f b] : [C b], with [t : C true] and [f : C false].

    Renaming and substitution are parallel ([nat -> nat], [nat -> term]);
    [subst1 b u] is [b[u/0]], decrementing the other free variables of
    [b]. *)

From Stdlib Require Import Arith List Bool.
Import ListNotations.

(** ** Sorts *)

Inductive sort : Type :=
| Star : sort            (** ∗ *)
| Box : sort             (** □ *)
| Tri : sort             (** △ *)
| Univ : nat -> sort.    (** Type_i *)

Definition sort_eq_dec (s s' : sort) : {s = s'} + {s <> s'}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition sort_eqb (s s' : sort) : bool :=
  if sort_eq_dec s s' then true else false.

Lemma sort_eqb_eq : forall s s', sort_eqb s s' = true <-> s = s'.
Proof.
  intros s s'. unfold sort_eqb.
  destruct (sort_eq_dec s s'); split; congruence.
Qed.

(** ** Terms *)

Inductive term : Type :=
| Srt : sort -> term
| Var : nat -> term
| Pi : term -> term -> term
| Lam : term -> term
| App : term -> term -> term
| Ann : term -> term -> term
(** MLTT primitives *)
| Void : term
| ElimVoid : term -> term -> term
| Unit : term
| Tt : term
| ElimUnit : term -> term -> term -> term
| Bool : term
| BTrue : term
| BFalse : term
| ElimBool : term -> term -> term -> term -> term.

Definition term_eq_dec (t u : term) : {t = u} + {t <> u}.
Proof. decide equality; first [apply sort_eq_dec | apply Nat.eq_dec]. Defined.

Definition term_eqb (t u : term) : bool :=
  if term_eq_dec t u then true else false.

Lemma term_eqb_eq : forall t u, term_eqb t u = true <-> t = u.
Proof.
  intros t u. unfold term_eqb.
  destruct (term_eq_dec t u); split; congruence.
Qed.

Implicit Types
  (n m : nat)
  (s : sort)
  (t u A B : term)
  (r : nat -> nat).

(** ** Renaming *)

Definition up_ren r : nat -> nat :=
  fun n => match n with 0 => 0 | S n' => S (r n') end.

Fixpoint rename r t : term :=
  match t with
  | Srt s => Srt s
  | Var n => Var (r n)
  | Pi A B => Pi (rename r A) (rename (up_ren r) B)
  | Lam b => Lam (rename (up_ren r) b)
  | App f a => App (rename r f) (rename r a)
  | Ann t A => Ann (rename r t) (rename r A)
  | Void => Void
  | ElimVoid C e => ElimVoid (rename r C) (rename r e)
  | Unit => Unit
  | Tt => Tt
  | ElimUnit C c u => ElimUnit (rename r C) (rename r c) (rename r u)
  | Bool => Bool
  | BTrue => BTrue
  | BFalse => BFalse
  | ElimBool C t f b =>
      ElimBool (rename r C) (rename r t) (rename r f) (rename r b)
  end.

(** [lift k t] moves [t] under [k] new binders. *)
Definition lift (k : nat) t : term := rename (Nat.add k) t.

(** The non-dependent arrow [A → B] is [Πx:A. B] with [B] lifted past the
    unused binder. *)
Definition arrow A B : term := Pi A (lift 1 B).

(** ** Substitution *)

Definition up_sub (sb : nat -> term) : nat -> term :=
  fun n => match n with 0 => Var 0 | S n' => lift 1 (sb n') end.

Fixpoint subst (sb : nat -> term) t : term :=
  match t with
  | Srt s => Srt s
  | Var n => sb n
  | Pi A B => Pi (subst sb A) (subst (up_sub sb) B)
  | Lam b => Lam (subst (up_sub sb) b)
  | App f a => App (subst sb f) (subst sb a)
  | Ann t A => Ann (subst sb t) (subst sb A)
  | Void => Void
  | ElimVoid C e => ElimVoid (subst sb C) (subst sb e)
  | Unit => Unit
  | Tt => Tt
  | ElimUnit C c u => ElimUnit (subst sb C) (subst sb c) (subst sb u)
  | Bool => Bool
  | BTrue => BTrue
  | BFalse => BFalse
  | ElimBool C t f b =>
      ElimBool (subst sb C) (subst sb t) (subst sb f) (subst sb b)
  end.

Definition scons (u : term) (sb : nat -> term) : nat -> term :=
  fun n => match n with 0 => u | S n' => sb n' end.

Definition subst1 (b u : term) : term := subst (scons u Var) b.

(** ** Free variables *)

(** [free_in i t] decides whether index [i] occurs free in [t]. *)
Fixpoint free_in (i : nat) t : bool :=
  match t with
  | Srt _ | Void | Unit | Tt | Bool | BTrue | BFalse => false
  | Var n => Nat.eqb n i
  | Pi A B => free_in i A || free_in (S i) B
  | Lam b => free_in (S i) b
  | App f a | Ann f a | ElimVoid f a => free_in i f || free_in i a
  | ElimUnit C c u => free_in i C || free_in i c || free_in i u
  | ElimBool C t f b =>
      free_in i C || free_in i t || free_in i f || free_in i b
  end.

(** [closed_above k t]: every free index of [t] is below [k]. *)
Fixpoint closed_above (k : nat) t : bool :=
  match t with
  | Srt _ | Void | Unit | Tt | Bool | BTrue | BFalse => true
  | Var n => Nat.ltb n k
  | Pi A B => closed_above k A && closed_above (S k) B
  | Lam b => closed_above (S k) b
  | App f a | Ann f a | ElimVoid f a => closed_above k f && closed_above k a
  | ElimUnit C c u => closed_above k C && closed_above k c && closed_above k u
  | ElimBool C t f b =>
      closed_above k C && closed_above k t && closed_above k f && closed_above k b
  end.

Definition closed t : bool := closed_above 0 t.

(** ** Renaming of sorts

    Used to move one annotated term between configurations, e.g. to check
    the looping combinator of U⁻ again with ∗, □, △ read as Type_0,
    Type_1, Type_2. *)

Fixpoint map_sorts (g : sort -> sort) t : term :=
  match t with
  | Srt s => Srt (g s)
  | Var n => Var n
  | Pi A B => Pi (map_sorts g A) (map_sorts g B)
  | Lam b => Lam (map_sorts g b)
  | App f a => App (map_sorts g f) (map_sorts g a)
  | Ann t A => Ann (map_sorts g t) (map_sorts g A)
  | Void => Void
  | ElimVoid C e => ElimVoid (map_sorts g C) (map_sorts g e)
  | Unit => Unit
  | Tt => Tt
  | ElimUnit C c u => ElimUnit (map_sorts g C) (map_sorts g c) (map_sorts g u)
  | Bool => Bool
  | BTrue => BTrue
  | BFalse => BFalse
  | ElimBool C t f b =>
      ElimBool (map_sorts g C) (map_sorts g t) (map_sorts g f) (map_sorts g b)
  end.

(** ** Contexts

    The head of the list is the type of [Var 0].  The type stored for
    [Var n] is well formed in the context that remains after dropping
    [n + 1] entries, so [lookup] lifts it past them. *)

Definition ctx : Type := list term.

Definition lookup (G : ctx) n : option term :=
  option_map (lift (S n)) (nth_error G n).
