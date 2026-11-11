(** * Unified syntax of terms and types

    One syntactic category for terms, types, kinds and sorts, with de
    Bruijn indices: [Var 0] is the innermost binder.  [Pi A B] and [Lam b]
    bind index 0 in [B] and [b].

    λ is unannotated (as in the PCF of strictness-pcf): it is checked
    against an expected Π-type, and a λ in a synthesizing position, e.g.
    the head of a β-redex, needs an annotation [Ann t A].

    Sorts cover both families of configurations: the named sorts ∗, □, △
    of λ∗, U, U⁻ and λC, and the predicative hierarchy [Univ i] = Type_i
    with the impredicative sort [Prp] of propositions beside it ([Prop] is
    a keyword of Rocq).  Which of them exist, and how they are related, is
    decided by a PTS specification (PTS.Spec), not by the syntax.

    The primitives Void, Unit and Bool of the minimal MLTT are part of the
    syntax from the start; a specification enables them or not.  Their
    eliminators take an explicit result family [C]:
    - [ElimVoid C e]     : [C e]
    - [ElimUnit C c u]   : [C u], with [c : C tt]
    - [ElimBool C t f b] : [C b], with [t : C true] and [f : C false].

    Dependent pairs are native: [Sigma A B] binds index 0 in [B], like
    [Pi]; [Pair a b] is unannotated and checked against an expected Σ, and
    [Fst p], [Snd p] are the projections.

    A constant [Const g] names an entry of a signature (PTS.Signature):
    an inductive type, a constructor, an eliminator instance for motives
    into a fixed sort, or a δ-constant.  Constants take their arguments as ordinary
    [App] spines.

    [match] and [fix] are primitive, as in Rocq:
    - [Case D s P x bs] is [match x as y in D Δ θ̄ return P θ̄ y with … end]:
      the motive [P] is a λ over the indices θ̄ and the scrutinee, into
      the sort [s]; [bs] holds one branch per constructor of D, in the
      order of their declaration, each a λ over the fields.  The
      parameters Δ are not stored: they are read off the type of [x].
      No former binds at the root of a [Case]: the motive and the
      branches bind their own variables;
    - [Fix A k b] is [fix f : A {struct k} := b]: [A] the type of the
      function, [k] the position of its structural argument, counted
      from 0, and [b] the body, where [f] is [Var 0].  The body starts
      with at least [k + 1] λ, up to the structural argument.

    Renaming and substitution are parallel ([nat -> nat], [nat -> term]);
    [subst1 b u] is [b[u/0]], decrementing the other free variables of
    [b]. *)

From Stdlib Require Import Arith List Bool Lia.
From Stdlib Require String.
Import ListNotations.

(** ** Sorts *)

Inductive sort : Type :=
| Star : sort            (** ∗ *)
| Box : sort             (** □ *)
| Tri : sort             (** △ *)
| Univ : nat -> sort     (** Type_i *)
| Prp : sort.            (** Prop *)

Definition sort_eq_dec (s s' : sort) : {s = s'} + {s <> s'}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition sort_eqb (s s' : sort) : bool :=
  if sort_eq_dec s s' then true else false.

Lemma sort_eqb_eq : forall s s', sort_eqb s s' = true <-> s = s'.
Proof.
  intros s s'. unfold sort_eqb.
  destruct (sort_eq_dec s s'); split; congruence.
Qed.

(** ** Global constants

    [Ind D] is an inductive type, [Ctor D c] its constructor named [c],
    [Elim D s] the instance of its eliminator for motives into the sort
    [s], [Type_j] or [Prop], and [Def f] a δ-constant.  The sort is part
    of the name: an instance has one closed type, there is no universe
    polymorphism. *)

Inductive gref : Type :=
| Ind : String.string -> gref
| Ctor : String.string -> String.string -> gref
| Elim : String.string -> sort -> gref
| Def : String.string -> gref.

Definition gref_eq_dec (g g' : gref) : {g = g'} + {g <> g'}.
Proof. decide equality; first [apply String.string_dec | apply sort_eq_dec]. Defined.

Definition gref_eqb (g g' : gref) : bool :=
  if gref_eq_dec g g' then true else false.

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
| ElimBool : term -> term -> term -> term -> term
(** dependent pairs *)
| Sigma : term -> term -> term
| Pair : term -> term -> term
| Fst : term -> term
| Snd : term -> term
(** constants of a signature *)
| Const : gref -> term
(** match and structural recursion *)
| Case : String.string -> sort -> term -> term -> list term -> term
| Fix : term -> nat -> term -> term.

Definition term_eq_dec : forall (t u : term), {t = u} + {t <> u}.
Proof.
  fix IH 1. intros t u.
  decide equality;
    first [ apply sort_eq_dec | apply Nat.eq_dec | apply gref_eq_dec | apply String.string_dec
          | apply (list_eq_dec IH) ].
Defined.

Definition term_eqb (t u : term) : bool :=
  if term_eq_dec t u then true else false.

Lemma term_eqb_eq : forall t u, term_eqb t u = true <-> t = u.
Proof.
  intros t u. unfold term_eqb.
  destruct (term_eq_dec t u); split; congruence.
Qed.

(** ** Induction with the branches of a match

    The induction principle Rocq generates for [term] gives no hypothesis
    for the branches, which lie in a list.  [term_ind'] is the same
    principle with [Forall P bs] for them; proofs that look into branches
    use [induction t using term_ind']. *)

Section TermInd.
  Variable P : term -> Prop.
  Hypothesis HSrt : forall s, P (Srt s).
  Hypothesis HVar : forall n, P (Var n).
  Hypothesis HPi : forall t1, P t1 -> forall t2, P t2 -> P (Pi t1 t2).
  Hypothesis HLam : forall t, P t -> P (Lam t).
  Hypothesis HApp : forall t1, P t1 -> forall t2, P t2 -> P (App t1 t2).
  Hypothesis HAnn : forall t1, P t1 -> forall t2, P t2 -> P (Ann t1 t2).
  Hypothesis HVoid : P Void.
  Hypothesis HElimVoid : forall t1, P t1 -> forall t2, P t2 -> P (ElimVoid t1 t2).
  Hypothesis HUnit : P Unit.
  Hypothesis HTt : P Tt.
  Hypothesis HElimUnit : forall t1, P t1 -> forall t2, P t2 -> forall t3, P t3 -> P (ElimUnit t1 t2 t3).
  Hypothesis HBool : P Bool.
  Hypothesis HTrue : P BTrue.
  Hypothesis HFalse : P BFalse.
  Hypothesis HElimBool : forall t1, P t1 -> forall t2, P t2 -> forall t3, P t3 -> forall t4, P t4 ->
    P (ElimBool t1 t2 t3 t4).
  Hypothesis HSigma : forall t1, P t1 -> forall t2, P t2 -> P (Sigma t1 t2).
  Hypothesis HPair : forall t1, P t1 -> forall t2, P t2 -> P (Pair t1 t2).
  Hypothesis HFst : forall t, P t -> P (Fst t).
  Hypothesis HSnd : forall t, P t -> P (Snd t).
  Hypothesis HConst : forall g, P (Const g).
  Hypothesis HCase : forall D s t1, P t1 -> forall t2, P t2 -> forall l (IHl : Forall P l), P (Case D s t1 t2 l).
  Hypothesis HFix : forall t1, P t1 -> forall n t2, P t2 -> P (Fix t1 n t2).

  Fixpoint term_ind' (t : term) : P t :=
    match t with
    | Srt s => HSrt s
    | Var n => HVar n
    | Pi A B => HPi A (term_ind' A) B (term_ind' B)
    | Lam b => HLam b (term_ind' b)
    | App f a => HApp f (term_ind' f) a (term_ind' a)
    | Ann u A => HAnn u (term_ind' u) A (term_ind' A)
    | Void => HVoid
    | ElimVoid C e => HElimVoid C (term_ind' C) e (term_ind' e)
    | Unit => HUnit
    | Tt => HTt
    | ElimUnit C c u => HElimUnit C (term_ind' C) c (term_ind' c) u (term_ind' u)
    | Bool => HBool
    | BTrue => HTrue
    | BFalse => HFalse
    | ElimBool C bt bf b => HElimBool C (term_ind' C) bt (term_ind' bt) bf (term_ind' bf) b (term_ind' b)
    | Sigma A B => HSigma A (term_ind' A) B (term_ind' B)
    | Pair a b => HPair a (term_ind' a) b (term_ind' b)
    | Fst p => HFst p (term_ind' p)
    | Snd p => HSnd p (term_ind' p)
    | Const g => HConst g
    | Case D s M x bs =>
        HCase D s M (term_ind' M) x (term_ind' x) bs
          ((fix all (bs : list term) : Forall P bs :=
              match bs with
              | [] => Forall_nil P
              | b :: bs' => Forall_cons b (term_ind' b) (all bs')
              end) bs)
    | Fix A k b => HFix A (term_ind' A) k b (term_ind' b)
    end.
End TermInd.

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
  | Sigma A B => Sigma (rename r A) (rename (up_ren r) B)
  | Pair a b => Pair (rename r a) (rename r b)
  | Fst p => Fst (rename r p)
  | Snd p => Snd (rename r p)
  | Const g => Const g
  | Case D s P x bs => Case D s (rename r P) (rename r x) (map (rename r) bs)
  | Fix A k b => Fix (rename r A) k (rename (up_ren r) b)
  end.

(** [lift k t] moves [t] under [k] new binders. *)
Definition lift (k : nat) t : term := rename (Nat.add k) t.

(** The non-dependent arrow [A → B] is [Πx:A. B] with [B] lifted past the
    unused binder. *)
Definition arrow A B : term := Pi A (lift 1 B).

(** The product [A × B] is [Σx:A. B] in the same way. *)
Definition times A B : term := Sigma A (lift 1 B).

(** ** Spines and telescopes

    [apps h [a₁; …; aₙ]] is [h a₁ … aₙ]; [spine_head] and [spine_args]
    take a spine apart again, [spine_args] in one pass with an
    accumulator; [spine_args_App] is its equation on an application.
    [pis] and [lams] bind a telescope, outermost entry
    first; [vars base n] are the variables of a telescope of [n] entries
    lying [base] binders up, outermost first:
    [Var (base + n - 1), …, Var base]. *)

Definition apps (h : term) (us : list term) : term := fold_left App us h.

Fixpoint spine_head t : term :=
  match t with
  | App f _ => spine_head f
  | _ => t
  end.

Fixpoint spine_args_acc t (acc : list term) : list term :=
  match t with
  | App f a => spine_args_acc f (a :: acc)
  | _ => acc
  end.

Definition spine_args t : list term := spine_args_acc t [].

Lemma spine_args_acc_app : forall t acc, spine_args_acc t acc = spine_args t ++ acc.
Proof.
  induction t; intros acc; try reflexivity.
  unfold spine_args. cbn [spine_args_acc]. rewrite !IHt1, <- app_assoc. reflexivity.
Qed.

(* TODO(elim-inductive-types): remove this comment once elim-inductive-types
   builds against this kernel.  Its theories/Elim/Decl.v keeps a copy of
   [apps_spine] whose proof unfolds [spine_args] by [cbn].  Since
   [spine_args] uses an accumulator, that unfolding no longer gives
   [spine_args f ++ [a]], and the proof breaks.  Fix there: use
   [apps_spine] of this module instead of the copy, or rewrite with
   [spine_args_App]. *)
Lemma spine_args_App : forall f a, spine_args (App f a) = spine_args f ++ [a].
Proof. intros f a. unfold spine_args at 1. cbn [spine_args_acc]. apply spine_args_acc_app. Qed.

(** [t] and the applications it is built from, outermost first: [f a b],
    [f a], [f] for [t = f a b]; one more than the arguments. *)
Fixpoint spine_prefixes (t : term) : list term :=
  match t with
  | App f _ => t :: spine_prefixes f
  | _ => [t]
  end.

Lemma spine_prefixes_hd : forall t, exists ps, spine_prefixes t = t :: ps.
Proof. intros t. destruct t; eexists; reflexivity. Qed.

Lemma spine_prefixes_length : forall t, length (spine_prefixes t) = S (length (spine_args t)).
Proof.
  induction t; try reflexivity.
  cbn [spine_prefixes length]. rewrite IHt1, spine_args_App, length_app. cbn [length].
  rewrite Nat.add_1_r. reflexivity.
Qed.

Fixpoint pis (As : list term) (B : term) : term :=
  match As with
  | [] => B
  | A :: As' => Pi A (pis As' B)
  end.

Fixpoint lams (n : nat) (b : term) : term :=
  match n with
  | 0 => b
  | S n' => Lam (lams n' b)
  end.

Fixpoint vars (base n : nat) : list term :=
  match n with
  | 0 => []
  | S n' => Var (base + n') :: vars base n'
  end.

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
  | Sigma A B => Sigma (subst sb A) (subst (up_sub sb) B)
  | Pair a b => Pair (subst sb a) (subst sb b)
  | Fst p => Fst (subst sb p)
  | Snd p => Snd (subst sb p)
  | Const g => Const g
  | Case D s P x bs => Case D s (subst sb P) (subst sb x) (map (subst sb) bs)
  | Fix A k b => Fix (subst sb A) k (subst (up_sub sb) b)
  end.

Definition scons (u : term) (sb : nat -> term) : nat -> term :=
  fun n => match n with 0 => u | S n' => sb n' end.

Definition subst1 (b u : term) : term := subst (scons u Var) b.

(** ** Free variables *)

(** [free_in i t] decides whether index [i] occurs free in [t]. *)
Fixpoint free_in (i : nat) t : bool :=
  match t with
  | Srt _ | Void | Unit | Tt | Bool | BTrue | BFalse | Const _ => false
  | Var n => Nat.eqb n i
  | Pi A B | Sigma A B | Fix A _ B => free_in i A || free_in (S i) B
  | Lam b => free_in (S i) b
  | Fst p | Snd p => free_in i p
  | App f a | Ann f a | ElimVoid f a | Pair f a => free_in i f || free_in i a
  | ElimUnit C c u => free_in i C || free_in i c || free_in i u
  | ElimBool C t f b =>
      free_in i C || free_in i t || free_in i f || free_in i b
  | Case _ _ P x bs => free_in i P || free_in i x || existsb (free_in i) bs
  end.

(** [closed_above k t]: every free index of [t] is below [k]. *)
Fixpoint closed_above (k : nat) t : bool :=
  match t with
  | Srt _ | Void | Unit | Tt | Bool | BTrue | BFalse | Const _ => true
  | Var n => Nat.ltb n k
  | Pi A B | Sigma A B | Fix A _ B => closed_above k A && closed_above (S k) B
  | Lam b => closed_above (S k) b
  | Fst p | Snd p => closed_above k p
  | App f a | Ann f a | ElimVoid f a | Pair f a => closed_above k f && closed_above k a
  | ElimUnit C c u => closed_above k C && closed_above k c && closed_above k u
  | ElimBool C t f b =>
      closed_above k C && closed_above k t && closed_above k f && closed_above k b
  | Case _ _ P x bs => closed_above k P && closed_above k x && forallb (closed_above k) bs
  end.

Definition closed t : bool := closed_above 0 t.

(** [has_def t]: [t] mentions a δ-constant. *)
Fixpoint has_def t : bool :=
  match t with
  | Const (Def _) => true
  | Srt _ | Var _ | Void | Unit | Tt | Bool | BTrue | BFalse | Const _ => false
  | Pi A B | Sigma A B | Fix A _ B | App A B | Ann A B | ElimVoid A B | Pair A B => has_def A || has_def B
  | Lam b | Fst b | Snd b => has_def b
  | ElimUnit C c u => has_def C || has_def c || has_def u
  | ElimBool C t f b => has_def C || has_def t || has_def f || has_def b
  | Case _ _ P x bs => has_def P || has_def x || existsb has_def bs
  end.

(** [def_head t]: the head of the spine of [t] is a δ-constant. *)
Definition def_head t : bool := match spine_head t with Const (Def _) => true | _ => false end.

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
  | Sigma A B => Sigma (map_sorts g A) (map_sorts g B)
  | Pair a b => Pair (map_sorts g a) (map_sorts g b)
  | Fst p => Fst (map_sorts g p)
  | Snd p => Snd (map_sorts g p)
  | Const c => Const c
  | Case D s P x bs => Case D (g s) (map_sorts g P) (map_sorts g x) (map (map_sorts g) bs)
  | Fix A k b => Fix (map_sorts g A) k (map_sorts g b)
  end.

(** ** Contexts

    The head of the list is the type of [Var 0].  The type stored for
    [Var n] is well formed in the context that remains after dropping
    [n + 1] entries, so [lookup] lifts it past them. *)

Definition ctx : Type := list term.

Definition lookup (G : ctx) n : option term :=
  option_map (lift (S n)) (nth_error G n).

(** ** Closed terms are unaffected by renaming and substitution *)

(** The branches of a match.  A goal over the list [l] of the branches
    — an equality of maps over [l], or a [forallb] over [l] or over a map
    of it — is reduced to a branch [b] of [l] and given to the hypothesis
    [Forall P l] of [term_ind']; a premise of it that a [forallb] over
    [l] gives is discharged, the others are left. *)
Ltac on_branches :=
  lazymatch goal with
  | IHl : Forall _ ?l |- _ =>
      rewrite Forall_forall in IHl;
      let b := fresh "b" in let Hb := fresh "Hb" in
      lazymatch goal with
      | |- map _ l = l => rewrite <- (map_id l) at 2; apply map_ext_in; intros b Hb
      | |- map _ _ = map _ _ => rewrite ?map_map; apply map_ext_in; intros b Hb
      | |- forallb _ (map _ l) = true =>
          apply forallb_forall; let x := fresh "x" in let Hx := fresh "Hx" in
          intros x Hx; apply in_map_iff in Hx as (b & <- & Hb)
      | |- forallb _ l = true => apply forallb_forall; intros b Hb
      end;
      eapply IHl; [exact Hb | ..];
      try match goal with Hl : forallb _ l = true |- _ => exact (proj1 (forallb_forall _ _) Hl b Hb) end
  end.

Lemma rename_closed_above : forall t k r,
  closed_above k t = true -> (forall i, i < k -> r i = i) -> rename r t = t.
Proof.
  induction t using term_ind'; intros k r Hc Hr; cbn in *;
    repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [? ?] end;
    try reflexivity.
  all: try (f_equal; apply Hr; apply Nat.ltb_lt; assumption).
  all: f_equal;
    first [ eapply IHt1; eassumption | eapply IHt2; eassumption | eapply IHt3; eassumption
          | eapply IHt4; eassumption | eapply IHt; eassumption
          | idtac ].
  all: try (on_branches; assumption).
  all: match goal with
       | IH : forall k r, closed_above k ?b = true -> _ -> rename r ?b = ?b,
         H : closed_above (S ?k) ?b = true |- rename (up_ren ?r) ?b = ?b =>
           apply (IH (S k)); [exact H | intros [|i] Hi; cbn; [reflexivity | f_equal; apply Hr; lia]]
       end.
Qed.

Lemma subst_closed_above : forall t k sb,
  closed_above k t = true -> (forall i, i < k -> sb i = Var i) -> subst sb t = t.
Proof.
  induction t using term_ind'; intros k sb Hc Hs; cbn in *;
    repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [? ?] end;
    try reflexivity.
  all: try (apply Hs; apply Nat.ltb_lt; assumption).
  all: f_equal;
    first [ eapply IHt1; eassumption | eapply IHt2; eassumption | eapply IHt3; eassumption
          | eapply IHt4; eassumption | eapply IHt; eassumption
          | idtac ].
  all: try (on_branches; assumption).
  all: match goal with
       | IH : forall k sb, closed_above k ?b = true -> _ -> subst sb ?b = ?b,
         H : closed_above (S ?k) ?b = true |- subst (up_sub ?s) ?b = ?b =>
           apply (IH (S k)); [exact H | intros [|i] Hi; cbn; [reflexivity | ]]
       end.
  all: unfold lift; rewrite Hs by lia; reflexivity.
Qed.

Lemma lift_closed : forall k t, closed t = true -> lift k t = t.
Proof. intros k t H. apply (rename_closed_above t 0); [exact H | intros i Hi; lia]. Qed.

Lemma subst_closed : forall sb t, closed t = true -> subst sb t = t.
Proof. intros sb t H. apply (subst_closed_above t 0); [exact H | intros i Hi; lia]. Qed.

Lemma subst1_closed : forall t u, closed t = true -> subst1 t u = t.
Proof. intros t u H. apply subst_closed, H. Qed.

Lemma closed_above_mono : forall t k k', closed_above k t = true -> k <= k' -> closed_above k' t = true.
Proof.
  induction t using term_ind'; intros k k' H Hk; cbn in *;
    repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [? ?] end;
    repeat (apply andb_true_intro; split); try reflexivity.
  all: try (apply Nat.ltb_lt; apply Nat.ltb_lt in H; lia).
  all: try (on_branches; lia).
  all: first [ eapply IHt1 | eapply IHt2 | eapply IHt3 | eapply IHt4 | eapply IHt ];
       first [ eassumption | lia ].
Qed.

Lemma closed_pi : forall A B, closed A = true -> closed B = true -> closed (Pi A B) = true.
Proof.
  intros A B HA HB. unfold closed in *. cbn. rewrite HA.
  apply (closed_above_mono B 0 1 HB). lia.
Qed.

Lemma closed_above_rename : forall t k k' r,
  closed_above k t = true -> (forall i, i < k -> r i < k') -> closed_above k' (rename r t) = true.
Proof.
  induction t using term_ind'; intros k k' r H Hr; cbn in *;
    repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [? ?] end;
    repeat (apply andb_true_intro; split); try reflexivity.
  all: try (apply Nat.ltb_lt, Hr, Nat.ltb_lt; assumption).
  all: try (on_branches; assumption).
  all: first [ eapply IHt1 | eapply IHt2 | eapply IHt3 | eapply IHt4 | eapply IHt ];
       try eassumption.
  all: intros [|i] Hi; cbn; [lia | ]. all: specialize (Hr i ltac:(lia)); lia.
Qed.

Lemma closed_above_lift1 : forall t k, closed_above k t = true -> closed_above (S k) (lift 1 t) = true.
Proof. intros t k H. apply (closed_above_rename t k); [exact H | intros; cbn; lia]. Qed.

(** ** Spines and the λ of a fix *)

Lemma apps_spine : forall t, apps (spine_head t) (spine_args t) = t.
Proof.
  induction t; try reflexivity.
  rewrite spine_args_App. cbn [spine_head]. unfold apps in *. rewrite fold_left_app. cbn. now rewrite IHt1.
Qed.

Lemma spine_args_apps : forall us h, spine_args (apps h us) = spine_args h ++ us.
Proof.
  induction us as [|u us IH]; intros h; [cbn [apps fold_left]; now rewrite app_nil_r | ].
  change (apps h (u :: us)) with (apps (App h u) us). rewrite IH, spine_args_App. now rewrite <- app_assoc.
Qed.

Lemma spine_head_apps : forall us h, spine_head (apps h us) = spine_head h.
Proof. induction us as [|u us IH]; intros h; [reflexivity | cbn; unfold apps in IH; now rewrite IH]. Qed.

(** [rev'] reverses a list in one pass; [rev] appends at every element.
    Code that runs uses the first, proofs reason with the second. *)
Lemma rev'_rev : forall {X : Type} (l : list X), rev' l = rev l.
Proof. intros X l. symmetry. apply rev_alt. Qed.

Lemma apps_snoc : forall h us u, apps h (us ++ [u]) = App (apps h us) u.
Proof. intros h us u. unfold apps. rewrite fold_left_app. reflexivity. Qed.

Lemma spine_head_idem : forall t, spine_head (spine_head t) = spine_head t.
Proof. induction t; try reflexivity. exact IHt1. Qed.

Lemma spine_head_not_app : forall t f a, spine_head t <> App f a.
Proof. induction t; intros f a; try discriminate. exact (IHt1 f a). Qed.

(** A head is not an application: it has no arguments. *)
Lemma spine_head_args : forall h, spine_head h = h -> spine_args h = [].
Proof.
  intros h H. destruct h; try reflexivity.
  exfalso. exact (spine_head_not_app h1 h1 h2 H).
Qed.

(** The head and the arguments of a spine in one pass, the last argument
    first: what an evaluator that walks a spine from its root and adds
    the arguments it evaluates in front needs, without reversing a
    list. *)
Fixpoint spine_rev t : term * list term :=
  match t with
  | App f a => let (h, vs) := spine_rev f in (h, a :: vs)
  | _ => (t, [])
  end.

Lemma spine_rev_spec : forall t, spine_rev t = (spine_head t, rev (spine_args t)).
Proof.
  induction t; try reflexivity.
  rewrite spine_args_App. cbn [spine_rev spine_head]. rewrite IHt1, rev_app_distr. reflexivity.
Qed.

(** [b] starts with at least [n] λ. *)
Fixpoint has_lams (n : nat) (b : term) : bool :=
  match n, b with
  | 0, _ => true
  | S n', Lam b' => has_lams n' b'
  | S _, _ => false
  end.

(** ** Spines, Π-telescopes, variables and contexts *)

Lemma apps_const_inj : forall g l l', apps (Const g) l = apps (Const g) l' -> l = l'.
Proof. intros g l l' E. apply (f_equal spine_args) in E. rewrite !spine_args_apps in E. exact E. Qed.

Lemma apps_const_not_srt : forall g l s, apps (Const g) l <> Srt s.
Proof.
  intros g l s. induction l as [|a l _] using rev_ind; [discriminate | rewrite apps_snoc; discriminate].
Qed.

Lemma pis_app : forall Ts1 Ts2 R, pis (Ts1 ++ Ts2) R = pis Ts1 (pis Ts2 R).
Proof. induction Ts1 as [|T Ts1 IH]; intros Ts2 R; cbn [app pis]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma pis_apps_not_srt : forall Ts h l a s, pis Ts (apps h (l ++ [a])) <> Srt s.
Proof. intros [|T Ts] h l a s; cbn [pis]; [rewrite apps_snoc | ]; discriminate. Qed.

Lemma closed_above_apps : forall us h k,
  closed_above k (apps h us) = closed_above k h && forallb (closed_above k) us.
Proof.
  induction us as [|u us IH]; intros h k; cbn [apps fold_left forallb].
  - rewrite andb_true_r. reflexivity.
  - unfold apps in IH. rewrite IH. cbn [closed_above]. rewrite andb_assoc. reflexivity.
Qed.

Lemma vars_closed : forall k base n, base + n <= k -> forallb (closed_above k) (vars base n) = true.
Proof.
  intros k base n. induction n as [|n IH]; intros H; [reflexivity | ].
  cbn [vars forallb closed_above]. rewrite IH by lia.
  apply andb_true_intro; split; [apply Nat.ltb_lt; lia | reflexivity].
Qed.

Lemma vars_in : forall base n t, In t (vars base n) -> exists i, t = Var i /\ base <= i < base + n.
Proof.
  intros base n. induction n as [|n IH]; intros t H; [destruct H | ].
  cbn [vars In] in H. destruct H as [<- | H]; [exists (base + n); split; [reflexivity | lia] | ].
  destruct (IH t H) as (i & -> & Hi). exists i. split; [reflexivity | lia].
Qed.

Lemma length_vars : forall base n, length (vars base n) = n.
Proof. intros base n. induction n as [|n IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma free_in_head : forall t i, spine_head t = Var i -> free_in i t = true.
Proof.
  induction t; intros i H; cbn [spine_head] in H; try discriminate H.
  - injection H as ->. cbn [free_in]. apply Nat.eqb_refl.
  - cbn [free_in]. rewrite (IHt1 i H). reflexivity.
Qed.

Lemma subst1_srt_inv : forall B u s, subst1 B u = Srt s -> B = Srt s \/ (B = Var 0 /\ u = Srt s).
Proof.
  intros B u s E. destruct B as [s' | n | | | | | | | | | | | | | | | | | | | |]; cbn in E; try discriminate E.
  - left. exact E.
  - destruct n as [|n]; cbn in E; [right; split; [reflexivity | exact E] | discriminate E].
Qed.

Lemma lookup_app_some : forall Gm G n A, lookup Gm n = Some A -> lookup (Gm ++ G) n = Some A.
Proof.
  intros Gm G n A H. unfold lookup in *.
  destruct (nth_error Gm n) eqn:E; [ | discriminate H].
  rewrite nth_error_app1 by (apply nth_error_Some; congruence). rewrite E. exact H.
Qed.

(** ** Terms of allowed constants and matches

    [allnodes pc pk t]: every constant of [t] satisfies [pc] and every
    match of [t] is on a family that satisfies [pk].  Renaming and
    substitution of terms of that kind keep it. *)

Fixpoint allnodes (pc : gref -> bool) (pk : String.string -> bool) (t : term) : bool :=
  match t with
  | Srt _ | Var _ | Void | Unit | Tt | Bool | BTrue | BFalse => true
  | Const g => pc g
  | Pi A B | Sigma A B | App A B | Ann A B | ElimVoid A B | Pair A B => allnodes pc pk A && allnodes pc pk B
  | Lam b | Fst b | Snd b => allnodes pc pk b
  | ElimUnit C c u => allnodes pc pk C && allnodes pc pk c && allnodes pc pk u
  | ElimBool C t f b => allnodes pc pk C && allnodes pc pk t && allnodes pc pk f && allnodes pc pk b
  | Case D _ P x bs => pk D && allnodes pc pk P && allnodes pc pk x && forallb (allnodes pc pk) bs
  | Fix A _ b => allnodes pc pk A && allnodes pc pk b
  end.

(** Every constant allowed: only the families of the matches are checked. *)
Notation cases_in cok := (allnodes (fun _ => true) cok).

Section AllNodes.
  Variable pc : gref -> bool.
  Variable pk : String.string -> bool.
  Local Notation an := (allnodes pc pk).

  Lemma an_rename : forall t f, an (rename f t) = an t.
  Proof.
    intros t. induction t using term_ind'; intros fr; cbn [allnodes rename]; auto;
      repeat match goal with H : forall f, an (rename f ?t) = _ |- _ => rewrite H end; auto.
    f_equal. induction IHl as [|b bs Hb _ IH]; [reflexivity | cbn [map forallb]; rewrite Hb, IH; reflexivity].
  Qed.

  Lemma an_lift : forall n t, an (lift n t) = an t.
  Proof. intros n t. apply an_rename. Qed.

  Lemma an_subst : forall t sb, an t = true -> (forall n, an (sb n) = true) -> an (subst sb t) = true.
  Proof.
    assert (Hup : forall sb, (forall n, an (sb n) = true) -> forall n, an (up_sub sb n) = true).
    { intros sb H [|n]; [reflexivity | cbn [up_sub]; rewrite an_lift; apply H]. }
    intros t. induction t using term_ind'; intros sb Ht Hsb; cbn [allnodes subst] in *;
      repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [? ?] end;
      repeat (apply andb_true_intro; split); auto.
    rewrite forallb_forall in *. intros b Hb. apply in_map_iff in Hb as (b0 & <- & Hb0).
    rewrite Forall_forall in IHl. auto.
  Qed.

  Lemma an_subst1 : forall b u, an b = true -> an u = true -> an (subst1 b u) = true.
  Proof. intros b u Hb Hu. apply an_subst; [exact Hb | intros [|n]; [exact Hu | reflexivity]]. Qed.

  Lemma an_apps : forall l h, an (apps h l) = an h && forallb an l.
  Proof.
    induction l as [|a l IH]; intros h; cbn [forallb]; [rewrite andb_true_r; reflexivity | ].
    change (apps h (a :: l)) with (apps (App h a) l). rewrite IH. cbn [allnodes]. symmetry. apply andb_assoc.
  Qed.

  Lemma an_lams : forall n b, an (lams n b) = an b.
  Proof. induction n as [|n IH]; intros b; [reflexivity | exact (IH b)]. Qed.

  Lemma an_vars : forall base n, forallb an (vars base n) = true.
  Proof. intros base n. induction n as [|n IH]; [reflexivity | exact IH]. Qed.

  Lemma an_pis : forall Ts R, an (pis Ts R) = forallb an Ts && an R.
  Proof.
    induction Ts as [|T Ts IH]; intros R; [reflexivity | ]. cbn [pis allnodes forallb]. rewrite IH.
    apply andb_assoc.
  Qed.

  Lemma an_spine : forall t, an t = true -> an (spine_head t) = true /\ forallb an (spine_args t) = true.
  Proof.
    intros t Ht. rewrite <- (apps_spine t) in Ht. rewrite an_apps in Ht. apply andb_prop in Ht. exact Ht.
  Qed.

End AllNodes.

Lemma an_true : forall t, allnodes (fun _ => true) (fun _ => true) t = true.
Proof.
  intros t. induction t using term_ind'; cbn [allnodes]; auto; try (rewrite ?IHt1, ?IHt2, ?IHt3, ?IHt4, ?IHt; reflexivity).
  rewrite IHt1, IHt2. cbn [andb]. induction IHl as [|b bs Hb _ IH]; [reflexivity | cbn [forallb]; rewrite Hb; exact IH].
Qed.

Lemma an_weaken : forall pc pk pc' pk' t, (forall g, pc g = true -> pc' g = true) ->
  (forall D, pk D = true -> pk' D = true) -> allnodes pc pk t = true -> allnodes pc' pk' t = true.
Proof.
  intros pc pk pc' pk' t Hc Hk. induction t using term_ind'; intros H; cbn [allnodes] in *;
    repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [? ?] end;
    repeat (apply andb_true_intro; split); auto.
  rewrite forallb_forall in *. rewrite Forall_forall in IHl. auto.
Qed.

Lemma an_lookup : forall pc pk G n A, forallb (allnodes pc pk) G = true -> lookup G n = Some A ->
  allnodes pc pk A = true.
Proof.
  intros pc pk G n A HG H. unfold lookup in H. destruct (nth_error G n) as [A0|] eqn:E; [ | discriminate H].
  injection H as <-. rewrite an_lift. rewrite forallb_forall in HG. exact (HG A0 (nth_error_In _ _ E)).
Qed.
