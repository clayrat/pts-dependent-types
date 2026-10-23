(** * Bounded evaluation and conversion

    [classify] implements the deterministic normal-order relation of
    PTS.NormalOrder in one structural pass: it returns the next step, or
    says that the term is neutral, normal but not neutral, or stuck.  Each
    subterm is classified once, and its shape decides whether the next
    position is inspected.  [normalize_trace] records each term before a
    step and includes the final term; [normalize] runs the same loop
    without the record ([normalize_trace_result]).  A zero budget still recognizes an
    already normal or stuck term; it times out only when another step is
    needed.

    [head_step] contracts only redexes needed to expose a constructor at the
    head.  In particular, beta substitution never evaluates its argument.
    Each of its steps is a normal-order step, so [whnf] follows [nstep].
    Both evaluators are total because recursion is bounded by fuel.  A
    timeout is inconclusive, not evidence of divergence or inequality.
    Conversely, [normalize_complete]: a normal form reachable by normal
    order is found once the fuel covers the number of steps.

    Everything is relative to a signature, the variable of the section:
    its δ- and ι-contractions are root redexes like β, and a full spine
    of an eliminator instance is scanned object first. *)

From Stdlib Require Import List Relations Lia.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Signature Reduction NormalOrder.

Section Eval.
Variable sg : signature.
Local Notation "t ⇝ u" := (red1 sg t u).
Local Notation "t ⇝* u" := (red sg t u).
Local Notation "t ≡ u" := (conv sg t u).
Local Notation "t ⇝ₙ u" := (nstep sg t u).
Local Notation "t ⇝ₙ* u" := (clos_refl_trans term (nstep sg) t u).
Local Notation nf := (nf sg).
Local Notation ne := (ne sg).
Local Notation stuck := (stuck sg).

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

(** The redexes at the root, shared by both evaluators: β, erasure of
    an annotation, ι on a constructor or a pair, and δ and ι of the
    signature. *)
Definition contract (t : term) : option term :=
  match t with
  | App (Lam b) a => Some (subst1 b a)
  | App _ _ => iota sg t
  | Ann t _ => Some t
  | ElimUnit _ c Tt => Some c
  | ElimBool _ t _ BTrue => Some t
  | ElimBool _ _ f BFalse => Some f
  | Fst (Pair a _) => Some a
  | Snd (Pair _ b) => Some b
  | Const g => sig_delta sg g
  | _ => None
  end.

Fixpoint classify (t : term) : shape :=
  match contract t with
  | Some u => Steps u
  | None =>
      match t with
      | Var _ | Const _ => IsNe
      | Srt _ | Void | Unit | Tt | Bool | BTrue | BFalse => IsNf
      | Pi A B =>
          next (classify A) (fun A' => Pi A' B) (fun _ =>
          next (classify B) (Pi A) (fun _ => IsNf))
      | Sigma A B =>
          next (classify A) (fun A' => Sigma A' B) (fun _ =>
          next (classify B) (Sigma A) (fun _ => IsNf))
      | Lam b => next (classify b) Lam (fun _ => IsNf)
      | App f a =>
          if full_elim sg t then
            next_head (classify a) (App f) (fun _ =>
            next_head (classify f) (fun f' => App f' a) (fun _ => IsNe))
          else
            next_head (classify f) (fun f' => App f' a) (fun _ =>
            next (classify a) (App f) (fun _ => IsNe))
      | Pair a b =>
          next (classify a) (fun a' => Pair a' b) (fun _ =>
          next (classify b) (Pair a) (fun _ => IsNf))
      | Fst p => next_head (classify p) Fst (fun _ => IsNe)
      | Snd p => next_head (classify p) Snd (fun _ => IsNe)
      | Ann _ _ => IsStuck    (** unreachable: [contract] erases it *)
      | ElimVoid C e =>
          next_head (classify e) (ElimVoid C) (fun _ =>
          next (classify C) (fun C' => ElimVoid C' e) (fun _ => IsNe))
      | ElimUnit C c u =>
          next_head (classify u) (ElimUnit C c) (fun _ =>
          next (classify C) (fun C' => ElimUnit C' c u) (fun _ =>
          next (classify c) (fun c' => ElimUnit C c' u) (fun _ => IsNe)))
      | ElimBool C t f b =>
          next_head (classify b) (ElimBool C t f) (fun _ =>
          next (classify C) (fun C' => ElimBool C' t f b) (fun _ =>
          next (classify t) (fun t' => ElimBool C t' f b) (fun _ =>
          next (classify f) (fun f' => ElimBool C t f' b) (fun _ => IsNe))))
      end
  end.

(** Weak-head reduction does not descend under binders or into arguments. *)
Fixpoint head_step (t : term) : option term :=
  match contract t with
  | Some u => Some u
  | None =>
      match t with
      | App f a =>
          if full_elim sg t then option_map (App f) (head_step a)
          else option_map (fun f' => App f' a) (head_step f)
      | Fst p => option_map Fst (head_step p)
      | Snd p => option_map Snd (head_step p)
      | ElimVoid C e => option_map (ElimVoid C) (head_step e)
      | ElimUnit C c u => option_map (ElimUnit C c) (head_step u)
      | ElimBool C t f b => option_map (ElimBool C t f) (head_step b)
      | _ => None
      end
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

(** The checker needs only the answer, so it does not build a trace. *)
Fixpoint normalize (fuel : nat) (t : term) : eval_result :=
  match classify t with
  | Steps u =>
      match fuel with
      | O => OutOfFuel t
      | S fuel' => normalize fuel' u
      end
  | IsNe | IsNf => NormalForm t
  | IsStuck => StuckTerm t
  end.

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
| ConvEqual : term -> conv_result    (** the common form both sides reach *)
| ConvDifferent : conv_result
| ConvOutOfFuel : conv_result
| ConvStuck : conv_result.

(** Syntactically equal terms are convertible without evaluation; this
    also settles identical terms without a normal form, such as the raw
    Ω of Tests.v.

    The answers:
    - [ConvEqual v]: both terms reach [v] by normal order, so they are
      convertible ([convert_equal_sound]); [v] is their common normal
      form, or the term itself when the two are syntactically equal;
    - [ConvStuck]: the terms differ syntactically and the normalization
      of one of them got stuck ([convert_stuck_sound]);
    - [ConvDifferent], [ConvOutOfFuel]: different normal forms, or not
      enough fuel.
    Stuckness is diagnosed only for syntactically different terms: two
    copies of the same stuck raw term are [ConvEqual], although
    [normalize] reports [StuckTerm] for each.  The checker relies on this
    only for types it has already validated, where stuck terms are ruled
    out by progress for normal order. *)
Definition convert (fuel : nat) (t u : term) : conv_result :=
  if term_eqb t u then ConvEqual t else
  match normalize fuel t, normalize fuel u with
  | NormalForm t', NormalForm u' =>
      if term_eqb t' u' then ConvEqual t' else ConvDifferent
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

Lemma contract_nstep : forall t u, contract t = Some u -> t ⇝ₙ u.
Proof.
  intros t u H. destruct t; cbn [contract] in H; try discriminate;
    repeat match type of H with
           | match ?x with _ => _ end = _ => destruct x; try discriminate
           end;
    first [ injection H as <-; constructor | apply N_Iota; exact H | apply N_Delta; exact H ].
Qed.

(** Off a β-redex, the contraction of an application is ι. *)
Lemma contract_app : forall f a, is_lam f = false -> contract (App f a) = iota sg (App f a).
Proof. intros f a H. destruct f; try discriminate H; reflexivity. Qed.

(** Closes a goal whose hypotheses give a component two incompatible
    shapes, or claim that a root redex is not one. *)
Ltac contra :=
  match goal with
  | H : ~ ne ?x, H' : ne ?x |- _ => exact (H H')
  | H : ~ nf ?x, H' : nf ?x |- _ => exact (H H')
  | H : ~ nf ?x, H' : ne ?x |- _ => exact (H (NF_Ne _ _ H'))
  | H : forall u, ~ ?x ⇝ₙ u, H' : ?x ⇝ₙ _ |- _ => exact (H _ H')
  | H : nf ?x, H' : ?x ⇝ₙ _ |- _ => exact (nf_no_nstep _ _ H H')
  | H : ne ?x, H' : ?x ⇝ₙ _ |- _ => exact (ne_no_nstep _ _ H H')
  | H : contract _ = None |- _ => cbn in H; discriminate H
  | H : iota _ _ = Some _ |- _ => no_iota
  | _ => congruence
  end.

(** The shape is truthful: a step of normal order, a neutral term, a
    normal one, or a stuck one.  Together with determinism of [nstep] this
    makes [classify] complete as well ([classify_complete]). *)
Lemma classify_spec : forall t, shape_spec t (classify t).
Proof.
  induction t; cbn [classify];
    match goal with |- context [contract ?x] =>
      destruct (contract x) as [u|] eqn:Ec; [now apply contract_nstep | ]
    end.
  all: try (cbn in Ec; discriminate Ec).
  (* what the absence of a root redex tells *)
  all: try match goal with Ec : contract (App ?f ?a) = None |- _ =>
         let Hl := fresh "Hl" in
         assert (Hl : is_lam f = false) by (destruct f; cbn in Ec; easy);
         assert (iota sg (App f a) = None) by (rewrite <- (contract_app f a Hl); exact Ec)
       end.
  all: try match goal with Ec : contract (Const ?g) = None |- _ =>
         assert (sig_delta sg g = None) by exact Ec
       end.
  all: try match goal with Ec : contract (Fst ?p) = None |- _ =>
         assert (is_pair p = false) by (destruct p; cbn in Ec; easy)
       end.
  all: try match goal with Ec : contract (Snd ?p) = None |- _ =>
         assert (is_pair p = false) by (destruct p; cbn in Ec; easy)
       end.
  all: try match goal with |- context [full_elim ?s ?x] => destruct (full_elim s x) eqn:Ef end.
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


Lemma normalize_trace_result : forall fuel t,
  snd (normalize_trace fuel t) = normalize fuel t.
Proof.
  induction fuel as [|fuel IH]; intros t; cbn [normalize_trace normalize];
    destruct (classify t) as [u| | |]; try reflexivity.
  rewrite <- IH. now destruct (normalize_trace fuel u).
Qed.

Lemma normalize_spec : forall fuel t,
  t ⇝ₙ* result_term (normalize fuel t) /\ result_spec (normalize fuel t).
Proof.
  intros fuel t. rewrite <- normalize_trace_result.
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
  intros fuel t u E. cbn [normalize]. now rewrite E.
Qed.

Lemma normalize_nf : forall fuel v, nf v -> normalize fuel v = NormalForm v.
Proof.
  intros fuel v H.
  destruct fuel; cbn [normalize];
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
  induction t; intros u H; cbn [head_step] in H;
    match type of H with context [contract ?x] =>
      destruct (contract x) as [v|] eqn:Ec; [injection H as <-; now apply contract_nstep | ]
    end; try discriminate.
  all: try match goal with Ec : contract (App ?f ?a) = None |- _ =>
         let Hl := fresh "Hl" in
         assert (Hl : is_lam f = false) by (destruct f; cbn in Ec; easy);
         assert (iota sg (App f a) = None) by (rewrite <- (contract_app f a Hl); exact Ec);
         destruct (full_elim sg (App f a)) eqn:Ef; cbv beta iota in H
       end.
  all: try match goal with Ec : contract (Fst ?p) = None |- _ =>
         assert (is_pair p = false) by (destruct p; cbn in Ec; easy) end.
  all: try match goal with Ec : contract (Snd ?p) = None |- _ =>
         assert (is_pair p = false) by (destruct p; cbn in Ec; easy) end.
  all: match type of H with
       | option_map _ ?x = _ => destruct x as [t'|] eqn:E; cbn in H
       end; try discriminate.
  all: injection H as <-;
       first [ apply N_ElimObj; [assumption | assumption | ]
             | apply N_AppFun; [assumption | assumption | ]
             | apply N_FstArg; [assumption | ]
             | apply N_SndArg; [assumption | ]
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

Lemma convert_stuck_sound : forall fuel t u,
  convert fuel t u = ConvStuck ->
  t <> u /\ exists v, normalize fuel t = StuckTerm v \/ normalize fuel u = StuckTerm v.
Proof.
  intros fuel t u H. unfold convert in H.
  destruct (term_eqb t u) eqn:E0; [discriminate | ].
  split; [intros ->; rewrite (proj2 (term_eqb_eq u u) eq_refl) in E0; discriminate | ].
  destruct (normalize fuel t) as [tn|ts|tf]; destruct (normalize fuel u) as [un|us|uf];
    try discriminate; eauto.
  destruct (term_eqb tn un); discriminate.
Qed.

(** Equality is sound for the declared conversion relation: both sides
    reach the reported common form.  A negative answer needs confluence
    and uniqueness of normal forms to be complete. *)
Lemma convert_equal_reaches : forall fuel t u v,
  convert fuel t u = ConvEqual v -> t ⇝ₙ* v /\ u ⇝ₙ* v.
Proof.
  intros fuel t u v H. unfold convert in H.
  destruct (term_eqb t u) eqn:E0.
  - apply term_eqb_eq in E0. injection H as <-. subst. split; apply rt_refl.
  - pose proof (proj1 (normalize_spec fuel t)) as Ht.
    pose proof (proj1 (normalize_spec fuel u)) as Hu.
    destruct (normalize fuel t) as [tn|ts|tf]; destruct (normalize fuel u) as [un|us|uf];
      try discriminate.
    destruct (term_eqb tn un) eqn:E; try discriminate.
    apply term_eqb_eq in E. injection H as <-. subst. auto.
Qed.

Lemma convert_equal_sound : forall fuel t u v,
  convert fuel t u = ConvEqual v -> t ≡ u.
Proof.
  intros fuel t u v H. destruct (convert_equal_reaches _ _ _ _ H) as [Ht Hu].
  apply conv_trans with v; [ | apply conv_sym ]; apply red_conv, nsteps_red; assumption.
Qed.

(** ** Joinability up to annotations

    Two terms without normal forms cannot be compared by [convert].  For
    them, [joinable fuel t u] looks for a common reduct in the two bounded
    normal-order traces, up to erasure of annotations.  A positive answer
    is a conversion ([joinable_sound]); a negative one says nothing. *)

Lemma normalize_trace_reaches : forall fuel t u,
  In u (fst (normalize_trace fuel t)) -> t ⇝ₙ* u.
Proof.
  induction fuel as [|fuel IH]; intros t u H; cbn [normalize_trace] in H;
    pose proof (classify_spec t) as Hs; destruct (classify t) as [v| | |]; cbn in Hs.
  all: try (destruct H as [<- | []]; apply rt_refl).
  destruct (normalize_trace fuel v) as [trace r] eqn:ER.
  destruct H as [<- | H]; [apply rt_refl | ].
  eapply rt_trans; [apply rt_step, Hs | apply IH; rewrite ER; exact H].
Qed.

Definition joinable (fuel : nat) (t u : term) : bool :=
  let us := map erase_ann (fst (normalize_trace fuel u)) in
  existsb (fun t' => existsb (term_eqb (erase_ann t')) us) (fst (normalize_trace fuel t)).

Lemma joinable_sound : forall fuel t u, joinable fuel t u = true -> t ≡ u.
Proof.
  intros fuel t u H. unfold joinable in H.
  apply existsb_exists in H as (t' & Ht' & H).
  apply existsb_exists in H as (w & Hw & E).
  apply term_eqb_eq in E. apply in_map_iff in Hw as (u' & <- & Hu').
  apply conv_trans with t'; [apply red_conv, nsteps_red, (normalize_trace_reaches fuel), Ht' | ].
  apply conv_trans with u'; [apply erase_conv, E | ].
  apply conv_sym, red_conv, nsteps_red, (normalize_trace_reaches fuel), Hu'.
Qed.
End Eval.

(** The lemmas take their signature implicitly: it is fixed by their
    statements. *)
Arguments contract_nstep {sg}.
Arguments contract_app {sg}.
Arguments classify_spec {sg}.
Arguments classify_complete {sg}.
Arguments classify_nf {sg}.
Arguments normalize_trace_spec {sg}.
Arguments normalize_trace_result {sg}.
Arguments normalize_spec {sg}.
Arguments normalize_step {sg}.
Arguments normalize_nf {sg}.
Arguments normalize_complete {sg}.
Arguments head_step_nstep {sg}.
Arguments whnf_reduces {sg}.
Arguments convert_stuck_sound {sg}.
Arguments convert_equal_reaches {sg}.
Arguments convert_equal_sound {sg}.
Arguments normalize_trace_reaches {sg}.
Arguments joinable_sound {sg}.
