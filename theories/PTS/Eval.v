(** * Bounded evaluation and conversion

    [classify] implements the deterministic normal-order relation of
    PTS.NormalOrder in one structural pass: it returns the next step, or
    says that the term is neutral, normal but not neutral, or stuck.  Each
    subterm is classified once, and its shape decides whether the next
    position is inspected.  [normalize_trace] records each term before a
    step and includes the final term.  A zero budget still recognizes an
    already normal or stuck term; it times out only when another step is
    needed.

    [head_step] contracts only redexes needed to expose a constructor at the
    head.  In particular, beta substitution never evaluates its argument.
    Each of its steps is a normal-order step, so [whnf] follows [nstep].
    Both evaluators are total because recursion is bounded by fuel.  A
    timeout is inconclusive, not evidence of divergence or inequality.
    Conversely, [normalize_complete]: a normal form reachable by normal
    order is found once the fuel covers the number of steps. *)

From Stdlib Require Import List Relations Lia.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Reduction NormalOrder.

(** ** One step of normal order *)

Inductive shape : Type :=
| Steps : term -> shape     (** the next normal-order step *)
| IsNe : shape              (** neutral *)
| IsNf : shape              (** normal, not neutral *)
| IsStuck : shape.          (** no step, not normal *)

(** A component that may be any normal form: a step is taken there, a
    normal component lets the scan go on with [k], a stuck one stops it.
    [k] is a thunk, so later components are classified only when needed. *)
Definition next (s : shape) (rebuild : term -> term) (k : unit -> shape) : shape :=
  match s with
  | Steps u => Steps (rebuild u)
  | IsNe | IsNf => k tt
  | IsStuck => IsStuck
  end.

(** The head of an application or the scrutinee of an eliminator: there
    a normal form that is not neutral is stuck. *)
Definition next_head (s : shape) (rebuild : term -> term) (k : unit -> shape) : shape :=
  match s with
  | Steps u => Steps (rebuild u)
  | IsNe => k tt
  | IsNf | IsStuck => IsStuck
  end.

Fixpoint classify (t : term) : shape :=
  match t with
  | Var _ => IsNe
  | Srt _ | Void | Unit | Tt | Bool | BTrue | BFalse => IsNf
  | Pi A B =>
      next (classify A) (fun A' => Pi A' B) (fun _ =>
      next (classify B) (Pi A) (fun _ => IsNf))
  | Lam b => next (classify b) Lam (fun _ => IsNf)
  | App (Lam b) a => Steps (subst1 b a)
  | App f a =>
      next_head (classify f) (fun f' => App f' a) (fun _ =>
      next (classify a) (App f) (fun _ => IsNe))
  | Ann t _ => Steps t
  | ElimVoid C e =>
      next_head (classify e) (ElimVoid C) (fun _ =>
      next (classify C) (fun C' => ElimVoid C' e) (fun _ => IsNe))
  | ElimUnit _ c Tt => Steps c
  | ElimUnit C c u =>
      next_head (classify u) (ElimUnit C c) (fun _ =>
      next (classify C) (fun C' => ElimUnit C' c u) (fun _ =>
      next (classify c) (fun c' => ElimUnit C c' u) (fun _ => IsNe)))
  | ElimBool _ t _ BTrue => Steps t
  | ElimBool _ _ f BFalse => Steps f
  | ElimBool C t f b =>
      next_head (classify b) (ElimBool C t f) (fun _ =>
      next (classify C) (fun C' => ElimBool C' t f b) (fun _ =>
      next (classify t) (fun t' => ElimBool C t' f b) (fun _ =>
      next (classify f) (fun f' => ElimBool C t f' b) (fun _ => IsNe))))
  end.

(** Weak-head reduction does not descend under binders or into arguments. *)
Fixpoint head_step (t : term) : option term :=
  match t with
  | App (Lam b) a => Some (subst1 b a)
  | App f a => option_map (fun f' => App f' a) (head_step f)
  | Ann t _ => Some t
  | ElimVoid C e => option_map (fun e' => ElimVoid C e') (head_step e)
  | ElimUnit _ c Tt => Some c
  | ElimUnit C c u => option_map (fun u' => ElimUnit C c u') (head_step u)
  | ElimBool _ t _ BTrue => Some t
  | ElimBool _ _ f BFalse => Some f
  | ElimBool C t f b => option_map (fun b' => ElimBool C t f b') (head_step b)
  | _ => None
  end.

Inductive eval_result : Type :=
| NormalForm : term -> eval_result
| StuckTerm : term -> eval_result
| OutOfFuel : term -> eval_result.

Fixpoint normalize_trace (fuel : nat) (t : term) : list term * eval_result :=
  match classify t with
  | Steps u =>
      match fuel with
      | O => ([t], OutOfFuel t)
      | S fuel' =>
          let '(trace, answer) := normalize_trace fuel' u in
          (t :: trace, answer)
      end
  | IsNe | IsNf => ([t], NormalForm t)
  | IsStuck => ([t], StuckTerm t)
  end.

Definition normalize (fuel : nat) (t : term) : eval_result :=
  snd (normalize_trace fuel t).

Inductive head_result : Type :=
| HeadForm : term -> head_result
| HeadOutOfFuel : term -> head_result.

Fixpoint whnf (fuel : nat) (t : term) : head_result :=
  match head_step t with
  | None => HeadForm t
  | Some u =>
      match fuel with
      | O => HeadOutOfFuel t
      | S fuel' => whnf fuel' u
      end
  end.

Inductive conv_result : Type :=
| ConvEqual : conv_result
| ConvDifferent : conv_result
| ConvOutOfFuel : conv_result
| ConvStuck : conv_result.

(** Syntactically equal terms are convertible without evaluation; this
    also settles identical terms without a normal form, such as the raw
    Ω of Tests.v.

    The answers:
    - [ConvEqual]: the terms are convertible ([compare_equal_sound]);
    - [ConvStuck]: the terms differ syntactically and the normalization
      of one of them got stuck ([compare_stuck_sound]);
    - [ConvDifferent], [ConvOutOfFuel]: different normal forms, or not
      enough fuel.
    Stuckness is diagnosed only for syntactically different terms: two
    copies of the same stuck raw term are [ConvEqual], although
    [normalize] reports [StuckTerm] for each.  The checker relies on this
    only for types it has already validated, where stuck terms are ruled
    out by progress for normal order. *)
Definition compare (fuel : nat) (t u : term) : conv_result :=
  if term_eqb t u then ConvEqual else
  match normalize fuel t, normalize fuel u with
  | NormalForm t', NormalForm u' =>
      if term_eqb t' u' then ConvEqual else ConvDifferent
  | StuckTerm _, _ | _, StuckTerm _ => ConvStuck
  | _, _ => ConvOutOfFuel
  end.

(** ** Correctness of [classify] *)

Definition shape_spec (t : term) (s : shape) : Prop :=
  match s with
  | Steps u => t ⇝ₙ u
  | IsNe => ne t
  | IsNf => nf t /\ ~ ne t
  | IsStuck => stuck t
  end.

(** Closes a goal whose hypotheses give a component two incompatible
    shapes. *)
Ltac contra :=
  match goal with
  | H : ~ ne ?x, H' : ne ?x |- _ => exact (H H')
  | H : ~ nf ?x, H' : nf ?x |- _ => exact (H H')
  | H : ~ nf ?x, H' : ne ?x |- _ => exact (H (NF_Ne _ H'))
  | H : forall u, ~ ?x ⇝ₙ u, H' : ?x ⇝ₙ _ |- _ => exact (H _ H')
  | H : nf ?x, H' : ?x ⇝ₙ _ |- _ => exact (nf_no_nstep _ _ H H')
  | H : ne ?x, H' : ?x ⇝ₙ _ |- _ => exact (ne_no_nstep _ _ H H')
  end.

(** The shape is truthful: a step of normal order, a neutral term, a
    normal one, or a stuck one.  Together with determinism of [nstep] this
    makes [classify] complete as well ([classify_complete]). *)
Lemma classify_spec : forall t, shape_spec t (classify t).
Proof.
  induction t; cbn [classify].
  all: repeat (cbn [next next_head shape_spec] in *;
               match goal with |- context [classify ?x] => destruct (classify x) end).
  all: repeat match goal with |- context [match ?x with _ => _ end] => destruct x end.
  all: cbn [next next_head shape_spec] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H | H : stuck _ |- _ => destruct H end.
  all: first
    [ lazymatch goal with |- stuck ?t =>
        split;
        [ intro Hn; inversion Hn; subst;
          try match goal with Hne : ne t |- _ => inversion Hne; subst end;
          contra
        | intros ? Hs; inversion Hs; subst; contra ]
      end
    | solve [ split; [solve [econstructor; eauto using NF_Ne] | intro Hne; inversion Hne] ]
    | solve [ econstructor; solve [reflexivity | eauto using NF_Ne] ] ].
Qed.

Lemma classify_complete : forall t u, t ⇝ₙ u -> classify t = Steps u.
Proof.
  intros t u H. pose proof (classify_spec t) as Hs.
  destruct (classify t); cbn in Hs.
  - f_equal. eapply nstep_det; eassumption.
  - destruct (ne_no_nstep _ _ Hs H).
  - destruct (nf_no_nstep _ _ (proj1 Hs) H).
  - destruct (proj2 Hs _ H).
Qed.

Lemma classify_nf : forall t, nf t -> classify t = IsNe \/ classify t = IsNf.
Proof.
  intros t H. pose proof (classify_spec t) as Hs.
  destruct (classify t); cbn in Hs; auto.
  - destruct (nf_no_nstep _ _ H Hs).
  - destruct (proj1 Hs H).
Qed.

Definition result_term (r : eval_result) : term :=
  match r with NormalForm t | StuckTerm t | OutOfFuel t => t end.

(** What each answer guarantees about its term. *)
Definition result_spec (r : eval_result) : Prop :=
  match r with
  | NormalForm v => nf v
  | StuckTerm v => stuck v
  | OutOfFuel v => exists u, v ⇝ₙ u
  end.

(** Soundness of normalization: the answer is reached by normal order and
    is a normal form, a stuck term, or a term with a pending step. *)
Lemma normalize_trace_spec : forall fuel t trace r,
  normalize_trace fuel t = (trace, r) ->
  t ⇝ₙ* result_term r /\ result_spec r.
Proof.
  induction fuel as [|fuel IH]; intros t trace r H; cbn [normalize_trace] in H;
    pose proof (classify_spec t) as Hs; destruct (classify t) as [u| | |];
    cbn in Hs.
  all: try (injection H as <- <-; split;
            [apply rt_refl | cbn; solve [apply Hs | apply NF_Ne, Hs | eexists; exact Hs]]).
  destruct (normalize_trace fuel u) as [trace' r'] eqn:ER.
  injection H as <- <-. destruct (IH _ _ _ ER) as [Hr Hr'].
  split; [eapply rt_trans; [apply rt_step, Hs | exact Hr] | exact Hr'].
Qed.


Lemma normalize_spec : forall fuel t,
  t ⇝ₙ* result_term (normalize fuel t) /\ result_spec (normalize fuel t).
Proof.
  intros fuel t. unfold normalize.
  destruct (normalize_trace fuel t) as [trace r] eqn:ER.
  exact (normalize_trace_spec _ _ _ _ ER).
Qed.

(** ** Completeness of normalization

    A normal form reachable by normal order is found by [normalize] once
    the fuel covers the number of steps, and more fuel does not change
    the answer.  This is what the premise [normalizing_types] of
    PTS.Bidir is turned into by the completeness proof of the checker. *)

Lemma normalize_step : forall fuel t u,
  classify t = Steps u -> normalize (S fuel) t = normalize fuel u.
Proof.
  intros fuel t u E. unfold normalize. cbn [normalize_trace]. rewrite E.
  now destruct (normalize_trace fuel u).
Qed.

Lemma normalize_nf : forall fuel v, nf v -> normalize fuel v = NormalForm v.
Proof.
  intros fuel v H. unfold normalize.
  destruct fuel; cbn [normalize_trace];
    destruct (classify_nf v H) as [-> | ->]; reflexivity.
Qed.

Theorem normalize_complete : forall t v, t ⇝ₙ* v -> nf v ->
  exists n, forall m, n <= m -> normalize m t = NormalForm v.
Proof.
  intros t v H Hv. apply clos_rt_rt1n in H.
  induction H as [v | t t' v Hs _ IH].
  - exists 0. intros m _. now apply normalize_nf.
  - destruct (IH Hv) as [n Hn]. exists (S n). intros [|m] Hm; [lia | ].
    rewrite (normalize_step _ _ _ (classify_complete _ _ Hs)).
    apply Hn. lia.
Qed.

(** Weak-head reduction is a prefix of normal order. *)
Lemma head_step_nstep : forall t u, head_step t = Some u -> t ⇝ₙ u.
Proof.
  induction t; intros u H; try discriminate.
  all: lazymatch type of H with
       | head_step (App ?f _) = _ => destruct f
       | head_step (ElimUnit _ _ ?s) = _ => destruct s
       | head_step (ElimBool _ _ _ ?s) = _ => destruct s
       | _ => idtac
       end.
  all: cbn [head_step] in H; try (injection H as <-; solve [repeat constructor]).
  all: match type of H with
       | option_map _ ?x = _ => destruct x as [t'|] eqn:E; cbn in H
       end; try discriminate.
  all: injection H as <-;
       first [ apply N_AppFun; [reflexivity | ]
             | apply N_ElimVoidScr | apply N_ElimUnitScr | apply N_ElimBoolScr ].
  all: match goal with
       | IH : forall u, _ = Some u -> ?x ⇝ₙ u |- ?x ⇝ₙ _ =>
           apply IH; first [exact E | reflexivity]
       end.
Qed.

Lemma whnf_reduces : forall fuel t v, whnf fuel t = HeadForm v -> t ⇝ₙ* v.
Proof.
  induction fuel as [|fuel IH]; intros t v H; cbn [whnf] in H;
    destruct (head_step t) as [u|] eqn:E; try discriminate.
  - injection H as <-. apply rt_refl.
  - eapply rt_trans; [apply rt_step, head_step_nstep, E | apply IH, H].
  - injection H as <-. apply rt_refl.
Qed.

Lemma compare_stuck_sound : forall fuel t u,
  compare fuel t u = ConvStuck ->
  t <> u /\ exists v, normalize fuel t = StuckTerm v \/ normalize fuel u = StuckTerm v.
Proof.
  intros fuel t u H. unfold compare in H.
  destruct (term_eqb t u) eqn:E0; [discriminate | ].
  split; [intros ->; rewrite (proj2 (term_eqb_eq u u) eq_refl) in E0; discriminate | ].
  destruct (normalize fuel t) as [tn|ts|tf]; destruct (normalize fuel u) as [un|us|uf];
    try discriminate; eauto.
  destruct (term_eqb tn un); discriminate.
Qed.

(** Equality is sound for the declared conversion relation.  A negative
    answer needs confluence and uniqueness of normal forms to be complete. *)
Lemma compare_equal_sound : forall fuel t u,
  compare fuel t u = ConvEqual -> t ≡ u.
Proof.
  intros fuel t u H. unfold compare in H.
  destruct (term_eqb t u) eqn:E0;
    [apply term_eqb_eq in E0; subst; apply conv_refl | ].
  destruct (normalize fuel t) as [tn|ts|tf] eqn:ET;
    destruct (normalize fuel u) as [un|us|uf] eqn:EU; try discriminate.
  destruct (term_eqb tn un) eqn:E; try discriminate.
  apply term_eqb_eq in E; subst.
  apply conv_trans with un.
  - apply red_conv, nsteps_red.
    pose proof (proj1 (normalize_spec fuel t)) as Ht. rewrite ET in Ht. exact Ht.
  - apply conv_sym, red_conv, nsteps_red.
    pose proof (proj1 (normalize_spec fuel u)) as Hu. rewrite EU in Hu. exact Hu.
Qed.
