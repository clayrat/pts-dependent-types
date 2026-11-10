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
    of an eliminator instance is scanned object first.

    [classify_nested] and [head_step_nested] state both scans one
    application at a time; at each one they test the contraction of the
    spine and whether it is full, which walks the spine again.
    [classify] and [head_step] find the head of a spine and the number of
    its arguments once, at its root, and compare the arity of the head
    with the number of arguments once, as the distance of the root above
    the full application ([gap]); on the way down this distance goes
    down by one at each application, and the full one is where it is
    zero.  The work is linear in the length of the spine, in the
    extracted code and under [vm_compute], with unary numbers, alike.
    They are proved equal to the first ones ([classify_nested_eq],
    [head_step_nested_eq]), which carry the proofs of correctness. *)

From Stdlib Require Import List Relations Lia Bool Arith.
From Stdlib Require String.
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

(** The branches of a match, from the left: once all are normal, the
    match is neutral. *)
Fixpoint next_branches (cls : term -> shape) (rebuild : list term -> term) (bs : list term) : shape :=
  match bs with
  | [] => IsNe
  | b :: bs' =>
      next (cls b) (fun b' => rebuild (b' :: bs')) (fun _ =>
      next_branches cls (fun bs'' => rebuild (b :: bs'')) bs')
  end.

(** The redexes at the root, shared by both evaluators: β, erasure of
    an annotation, ι on a constructor or a pair, δ and ι of the
    signature, ι of match and the unfolding of fix. *)
Definition contract (t : term) : option term :=
  match t with
  | App (Lam b) a => Some (subst1 b a)
  | App _ _ => spine_iota sg t
  | Case _ _ _ _ _ => case_iota sg t
  | Ann t _ => Some t
  | ElimUnit _ c Tt => Some c
  | ElimBool _ t _ BTrue => Some t
  | ElimBool _ _ f BFalse => Some f
  | Fst (Pair a _) => Some a
  | Snd (Pair _ b) => Some b
  | Const g => sig_delta sg g
  | _ => None
  end.

(** ** One node

    Everything but an application, whose contraction and scan depend on
    its spine; [cl] and [hs] classify and step the subterms.  The
    application is left to [classify_nested] and [classify] (resp.
    [head_step_nested] and [head_step]) below. *)

Definition classify_node (cl : term -> shape) (t : term) : shape :=
  match contract t with
  | Some u => Steps u
  | None =>
      match t with
      | Var _ | Const _ => IsNe
      | Srt _ | Void | Unit | Tt | Bool | BTrue | BFalse => IsNf
      | Pi A B =>
          next (cl A) (fun A' => Pi A' B) (fun _ =>
          next (cl B) (Pi A) (fun _ => IsNf))
      | Sigma A B =>
          next (cl A) (fun A' => Sigma A' B) (fun _ =>
          next (cl B) (Sigma A) (fun _ => IsNf))
      | Lam b => next (cl b) Lam (fun _ => IsNf)
      | App _ _ => IsStuck    (** unreachable: applications are classified by their spine *)
      | Pair a b =>
          next (cl a) (fun a' => Pair a' b) (fun _ =>
          next (cl b) (Pair a) (fun _ => IsNf))
      | Fst p => next_head (cl p) Fst (fun _ => IsNe)
      | Snd p => next_head (cl p) Snd (fun _ => IsNe)
      | Ann _ _ => IsStuck    (** unreachable: [contract] erases it *)
      | ElimVoid C e =>
          next_head (cl e) (ElimVoid C) (fun _ =>
          next (cl C) (fun C' => ElimVoid C' e) (fun _ => IsNe))
      | ElimUnit C c u =>
          next_head (cl u) (ElimUnit C c) (fun _ =>
          next (cl C) (fun C' => ElimUnit C' c u) (fun _ =>
          next (cl c) (fun c' => ElimUnit C c' u) (fun _ => IsNe)))
      | ElimBool C t f b =>
          next_head (cl b) (ElimBool C t f) (fun _ =>
          next (cl C) (fun C' => ElimBool C' t f b) (fun _ =>
          next (cl t) (fun t' => ElimBool C t' f b) (fun _ =>
          next (cl f) (fun f' => ElimBool C t f' b) (fun _ => IsNe))))
      | Case D s P x bs =>
          next_head (cl x) (fun x' => Case D s P x' bs) (fun _ =>
          next (cl P) (fun P' => Case D s P' x bs) (fun _ =>
          next_branches cl (Case D s P x) bs))
      | Fix A k b =>
          next (cl A) (fun A' => Fix A' k b) (fun _ =>
          next (cl b) (Fix A k) (fun _ => IsNe))
      end
  end.

Definition head_node (hs : term -> option term) (t : term) : option term :=
  match contract t with
  | Some u => Some u
  | None =>
      match t with
      | Case D s P x bs => option_map (fun x' => Case D s P x' bs) (hs x)
      | Fst p => option_map Fst (hs p)
      | Snd p => option_map Snd (hs p)
      | ElimVoid C e => option_map (ElimVoid C) (hs e)
      | ElimUnit C c u => option_map (ElimUnit C c) (hs u)
      | ElimBool C t f b => option_map (ElimBool C t f) (hs b)
      | _ => None
      end
  end.

(** ** One application at a time: the specification

    At every application the contraction of the spine and [full_spine]
    are tested, which walks the spine again: on a spine of [n]
    arguments, the work is quadratic in [n]. *)

Fixpoint classify_nested (t : term) : shape :=
  match t with
  | App f a =>
      match contract t with
      | Some u => Steps u
      | None =>
          if full_spine sg t then
            next_head (classify_nested a) (App f) (fun _ =>
            next_head (classify_nested f) (fun f' => App f' a) (fun _ => IsNe))
          else
            next_head (classify_nested f) (fun f' => App f' a) (fun _ =>
            next (classify_nested a) (App f) (fun _ => IsNe))
      end
  | _ => classify_node classify_nested t
  end.

(** Weak-head reduction does not descend under binders or into arguments. *)
Fixpoint head_step_nested (t : term) : option term :=
  match t with
  | App f a =>
      match contract t with
      | Some u => Some u
      | None =>
          if full_spine sg t then option_map (App f) (head_step_nested a)
          else option_map (fun f' => App f' a) (head_step_nested f)
      end
  | _ => head_node head_step_nested t
  end.

(** ** Whole spines

    [classify] and [head_step] compute the same functions
    ([classify_nested_eq], [head_step_nested_eq]) with one walk of each
    spine, linear in its length.  At the root of a spine they find its
    head, the arity of the head ([head_arity]) and the number of its
    arguments once, and hand down to every application of the spine how
    far it lies above the full one ([gap]): whether it is full, and so
    whether it may be contracted, is whether that distance is zero.  The
    arguments are put together only to contract the full application. *)

Definition beta (f a : term) : option term :=
  match f with
  | Lam b => Some (subst1 b a)
  | _ => None
  end.

(** How far an application of a spine lies above the full one: [Some g]
    when the head has arity [m] and the application has [m + g]
    arguments, [None] when the head has no arity or the application is
    short of it.  It is computed once at the root of the spine, and goes
    down by one at each application towards the head ([gap_down]):
    whether an application is full is then the test [Some 0], in
    constant time even with the unary numbers of [vm_compute]. *)
Definition gap (m : option nat) (j : nat) : option nat :=
  match m with
  | Some m' => if Nat.leb m' j then Some (j - m') else None
  | None => None
  end.

Definition gap_down (g : option nat) : option nat :=
  match g with Some (S g') => Some g' | _ => None end.

Definition gap_full (g : option nat) : bool :=
  match g with Some 0 => true | _ => false end.

Lemma gap_full_at_arity : forall m j, gap_full (gap m j) = at_arity m j.
Proof.
  intros [m|] j; [ | reflexivity]. unfold gap, at_arity.
  destruct (Nat.leb m j) eqn:E.
  - apply Nat.leb_le in E. destruct (j - m) eqn:E2; unfold gap_full; symmetry;
      [apply Nat.eqb_eq; lia | apply Nat.eqb_neq; lia].
  - apply Nat.leb_gt in E. symmetry. apply Nat.eqb_neq. lia.
Qed.

Lemma gap_down_succ : forall m j, gap m j = gap_down (gap m (S j)).
Proof.
  intros [m|] j; [ | reflexivity]. unfold gap.
  destruct (Nat.leb m j) eqn:E1; destruct (Nat.leb m (S j)) eqn:E2.
  - apply Nat.leb_le in E1. replace (S j - m) with (S (j - m)) by lia. reflexivity.
  - apply Nat.leb_le in E1. apply Nat.leb_gt in E2. lia.
  - apply Nat.leb_gt in E1. apply Nat.leb_le in E2. replace (S j - m) with 0 by lia. reflexivity.
  - reflexivity.
Qed.

(** The application [t = App f a], [g] above the full one: it contracts
    (β, or the full spine contracted), or it is a full spine that does
    not contract, its object scanned first, or another application, its
    function scanned first. *)
Inductive app_shape : Type :=
| AppContracts : term -> app_shape
| AppFull : app_shape
| AppPartial : app_shape.

Definition app_shape_at (g : option nat) (t f a : term) : app_shape :=
  match beta f a with
  | Some u => AppContracts u
  | None =>
      if gap_full g then
        match head_iota sg (spine_head t) (spine_args t) with
        | Some u => AppContracts u
        | None => AppFull
        end
      else AppPartial
  end.

Definition classify_level (cl : term -> shape) (cls : option nat -> term -> shape) (g : option nat)
  (t f a : term) : shape :=
  match app_shape_at g t f a with
  | AppContracts u => Steps u
  | AppFull =>
      next_head (cl a) (App f) (fun _ =>
      next_head (cls (gap_down g) f) (fun f' => App f' a) (fun _ => IsNe))
  | AppPartial =>
      next_head (cls (gap_down g) f) (fun f' => App f' a) (fun _ =>
      next (cl a) (App f) (fun _ => IsNe))
  end.

Fixpoint classify (t : term) : shape :=
  match t with
  | App f a =>
      classify_level (fun u => classify u) (fun g u => classify_spine g u)
        (gap (head_arity sg (spine_head t)) (length (spine_args t))) t f a
  | _ => classify_node (fun u => classify u) t
  end

with classify_spine (g : option nat) (t : term) {struct t} : shape :=
  match t with
  | App f a => classify_level (fun u => classify u) (fun g' u => classify_spine g' u) g t f a
  | _ => classify_node (fun u => classify u) t
  end.

Definition head_level (hs : term -> option term) (hss : option nat -> term -> option term) (g : option nat)
  (t f a : term) : option term :=
  match app_shape_at g t f a with
  | AppContracts u => Some u
  | AppFull => option_map (App f) (hs a)
  | AppPartial => option_map (fun f' => App f' a) (hss (gap_down g) f)
  end.

Fixpoint head_step (t : term) : option term :=
  match t with
  | App f a =>
      head_level (fun u => head_step u) (fun g u => head_spine g u)
        (gap (head_arity sg (spine_head t)) (length (spine_args t))) t f a
  | _ => head_node (fun u => head_step u) t
  end

with head_spine (g : option nat) (t : term) {struct t} : option term :=
  match t with
  | App f a => head_level (fun u => head_step u) (fun g' u => head_spine g' u) g t f a
  | _ => head_node (fun u => head_step u) t
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

(** Conversion by normalizing both sides; [convert], after the section,
    tries a lazy comparison first when the signature has δ-constants.
    Syntactically equal terms are convertible without evaluation; this
    also settles identical terms without a normal form, such as the raw
    Ω of Tests.v.

    The answers:
    - [ConvEqual v]: both terms reach [v] by normal order, so they are
      convertible ([convert_full_equal_reaches]); [v] is their common
      normal form, or the term itself when the two are syntactically
      equal;
    - [ConvStuck]: the terms differ syntactically and the normalization
      of one of them got stuck ([convert_full_stuck_sound]);
    - [ConvDifferent], [ConvOutOfFuel]: different normal forms, or not
      enough fuel.
    Stuckness is diagnosed only for syntactically different terms: two
    copies of the same stuck raw term are [ConvEqual], although
    [normalize] reports [StuckTerm] for each.  The checker relies on this
    only for types it has already validated, where stuck terms are ruled
    out by progress for normal order. *)
Definition convert_full (fuel : nat) (t u : term) : conv_result :=
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
    first [ injection H as <-; constructor | apply N_Iota; exact H | apply N_Delta; exact H
          | apply N_Case; exact H ].
Qed.

(** Off a β-redex, the contraction of an application is ι of a spine. *)
Lemma contract_app : forall f a, is_lam f = false -> contract (App f a) = spine_iota sg (App f a).
Proof. intros f a H. destruct f; try discriminate H; reflexivity. Qed.

(** The branches of a match after normal ones [pre]: the shape of the
    match is that of its first branch that is not normal. *)
Lemma next_branches_spec : forall bs pre rebuild D s P x,
  (forall l, rebuild l = Case D s P x (pre ++ l)) ->
  case_iota sg (Case D s P x (pre ++ bs)) = None -> ne x -> nf P -> nfs sg pre ->
  Forall (fun b => shape_spec b (classify_nested b)) bs ->
  shape_spec (Case D s P x (pre ++ bs)) (next_branches classify_nested rebuild bs).
Proof.
  induction bs as [|b bs IH]; intros pre rebuild D s P x Hr Hc Hx HP Hpre Hb.
  - cbn. rewrite app_nil_r in *. constructor; assumption.
  - inversion Hb as [|? ? Hb1 Hbs]; subst. cbn [next_branches].
    destruct (classify_nested b) as [b'| | |] eqn:Eb; cbn [next shape_spec] in *.
    + rewrite Hr. apply N_CaseBr; assumption.
    + replace (pre ++ b :: bs) with ((pre ++ [b]) ++ bs) in * by now rewrite <- app_assoc.
      apply IH; try assumption.
      * intros l. rewrite Hr, <- app_assoc. reflexivity.
      * apply nfs_app; [assumption | constructor; [apply NF_Ne, Hb1 | constructor]].
    + destruct Hb1 as [Hb1 _].
      replace (pre ++ b :: bs) with ((pre ++ [b]) ++ bs) in * by now rewrite <- app_assoc.
      apply IH; try assumption.
      * intros l. rewrite Hr, <- app_assoc. reflexivity.
      * apply nfs_app; [assumption | constructor; [exact Hb1 | constructor]].
    + destruct Hb1 as [Hn Hs]. split.
      * intros H. inversion H as [| | | | | | | | | | | ? Hne]; subst. inversion Hne; subst.
        apply Hn, (nfs_app_inv _ _ _ ltac:(eassumption)).
      * intros u Hu. inversion Hu; subst;
          first
            [ exact (ne_no_nstep _ _ Hx ltac:(eassumption))
            | exact (nf_no_nstep _ _ HP ltac:(eassumption))
            | congruence
            | no_iota
            | match goal with
              | E : ?l1 ++ ?b1 :: ?r1 = pre ++ b :: bs, S : ?b1 ⇝ₙ _ |- _ =>
                  destruct (branch_first _ _ _ _ _ _ _ ltac:(eassumption) Hpre S Hn E) as (_ & -> & _);
                  exact (Hs _ S)
              end ].
Qed.

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
  | H : spine_iota _ _ = Some _ |- _ => no_iota
  | H : case_iota _ _ = Some _ |- _ => no_iota
  | _ => congruence
  end.

(** The shape is truthful: a step of normal order, a neutral term, a
    normal one, or a stuck one.  Together with determinism of [nstep] this
    makes [classify] complete as well ([classify_complete]). *)
Lemma classify_nested_spec : forall t, shape_spec t (classify_nested t).
Proof.
  induction t using term_ind'; cbn [classify_nested]; cbv beta iota delta [classify_node];
    match goal with |- context [contract ?x] =>
      destruct (contract x) as [u|] eqn:Ec; [now apply contract_nstep | ]
    end.
  all: try (cbn in Ec; discriminate Ec).
  (* what the absence of a root redex tells *)
  all: try match goal with Ec : contract (App ?f ?a) = None |- _ =>
         let Hl := fresh "Hl" in
         assert (Hl : is_lam f = false) by (destruct f; cbn in Ec; easy);
         assert (spine_iota sg (App f a) = None) by (rewrite <- (contract_app f a Hl); exact Ec)
       end.
  all: try match goal with Ec : contract (Const ?g) = None |- _ =>
         assert (sig_delta sg g = None) by exact Ec
       end.
  all: try match goal with Ec : contract (Case ?D ?s ?P ?x ?bs) = None |- _ =>
         assert (case_iota sg (Case D s P x bs) = None) by exact Ec
       end.
  all: try match goal with Ec : contract (Fst ?p) = None |- _ =>
         assert (is_pair p = false) by (destruct p; cbn in Ec; easy)
       end.
  all: try match goal with Ec : contract (Snd ?p) = None |- _ =>
         assert (is_pair p = false) by (destruct p; cbn in Ec; easy)
       end.
  all: try match goal with |- context [full_spine ?s ?x] => destruct (full_spine s x) eqn:Ef end.
  all: repeat (cbn [next next_head shape_spec] in *;
               match goal with |- context [classify_nested ?x] => destruct (classify_nested x) end).
  all: repeat match goal with |- context [match ?x with _ => _ end] => destruct x end.
  all: cbn [next next_head shape_spec] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H | H : stuck _ |- _ => destruct H end.
  all: try lazymatch goal with
       | |- shape_spec (Case ?D ?s ?P ?x ?bs) (next_branches _ _ _) =>
           apply (next_branches_spec bs [] (Case D s P x));
           solve [reflexivity | assumption | constructor | eauto using NF_Ne]
       end.
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

(** ** [classify] and [head_step] compute their specifications *)

Lemma contract_beta : forall f a,
  contract (App f a) = match beta f a with Some u => Some u | None => spine_iota sg (App f a) end.
Proof. intros f a. destruct f; reflexivity. Qed.

Lemma next_branches_ext : forall cl cl' rebuild bs,
  Forall (fun b => cl b = cl' b) bs -> next_branches cl rebuild bs = next_branches cl' rebuild bs.
Proof.
  intros cl cl' rebuild bs H. revert rebuild.
  induction H as [|b bs Hb _ IH]; intros rebuild; [reflexivity | ].
  cbn [next_branches]. rewrite Hb, IH. reflexivity.
Qed.

(** Under the arity of its head, an application with [j] arguments is
    classified as one application at a time classifies it. *)
Theorem classify_nested_eq : forall t,
  classify t = classify_nested t /\
  (forall g, g = gap (head_arity sg (spine_head t)) (length (spine_args t)) ->
     classify_spine g t = classify_nested t).
Proof.
  induction t using term_ind'.
  (* an application *)
  5: { assert (Happ : forall g, g = gap (head_arity sg (spine_head (App t1 t2))) (length (spine_args (App t1 t2))) ->
         classify_level (fun u => classify u) (fun g' u => classify_spine g' u) g (App t1 t2) t1 t2 = classify_nested (App t1 t2)).
       { intros g Hg. cbn [classify_nested]. rewrite contract_beta. unfold classify_level, app_shape_at. cbv beta.
         destruct (beta t1 t2) as [u|]; [reflexivity | ].
         rewrite spine_iota_full_head, full_spine_head, <- gap_full_at_arity, <- Hg.
         assert (Hg1 : gap_down g = gap (head_arity sg (spine_head t1)) (length (spine_args t1))).
         { rewrite Hg, spine_args_App, length_app. cbn [spine_head length].
           rewrite Nat.add_1_r. symmetry. apply gap_down_succ. }
         rewrite (proj2 IHt1 _ Hg1), (proj1 IHt2).
         destruct (gap_full g); [ | reflexivity].
         destruct (head_iota sg (spine_head (App t1 t2)) (spine_args (App t1 t2))); reflexivity. }
       split; [exact (Happ _ eq_refl) | intros g Hg; exact (Happ g Hg)]. }
  (* every other former: one node *)
  all: lazymatch goal with |- classify ?t = _ /\ _ =>
         assert (Hn : classify_node (fun u => classify u) t = classify_node classify_nested t);
         [ | split; [exact Hn | intros ? _; exact Hn] ]
       end.
  all: unfold classify_node; cbv beta;
       repeat match goal with IH : classify ?x = _ /\ _ |- _ => rewrite (proj1 IH) end.
  all: try reflexivity.
  (* the branches of a match *)
  rewrite (next_branches_ext (fun u => classify u) classify_nested _ l)
    by (eapply Forall_impl; [ | exact IHl]; intros b Hb; exact (proj1 Hb)).
  reflexivity.
Qed.

Lemma classify_spec : forall t, shape_spec t (classify t).
Proof. intros t. rewrite (proj1 (classify_nested_eq t)). apply classify_nested_spec. Qed.

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
Lemma head_step_nested_nstep : forall t u, head_step_nested t = Some u -> t ⇝ₙ u.
Proof.
  induction t; intros u H; cbn [head_step_nested] in H; cbv beta iota delta [head_node] in H;
    match type of H with context [contract ?x] =>
      destruct (contract x) as [v|] eqn:Ec; [injection H as <-; now apply contract_nstep | ]
    end; try discriminate.
  all: try match goal with Ec : contract (App ?f ?a) = None |- _ =>
         let Hl := fresh "Hl" in
         assert (Hl : is_lam f = false) by (destruct f; cbn in Ec; easy);
         assert (spine_iota sg (App f a) = None) by (rewrite <- (contract_app f a Hl); exact Ec);
         destruct (full_spine sg (App f a)) eqn:Ef; cbv beta iota in H
       end.
  all: try match goal with Ec : contract (Case ?D ?s ?P ?x ?bs) = None |- _ =>
         assert (case_iota sg (Case D s P x bs) = None) by exact Ec
       end.
  all: try match goal with Ec : contract (Fst ?p) = None |- _ =>
         assert (is_pair p = false) by (destruct p; cbn in Ec; easy) end.
  all: try match goal with Ec : contract (Snd ?p) = None |- _ =>
         assert (is_pair p = false) by (destruct p; cbn in Ec; easy) end.
  all: match type of H with
       | option_map _ ?x = _ => destruct x as [t'|] eqn:E; cbn in H
       end; try discriminate.
  all: injection H as <-;
       first [ apply N_SpineObj; [assumption | assumption | ]
             | apply N_AppFun; [assumption | assumption | ]
             | apply N_CaseScr; [assumption | ]
             | apply N_FstArg; [assumption | ]
             | apply N_SndArg; [assumption | ]
             | apply N_ElimVoidScr | apply N_ElimUnitScr | apply N_ElimBoolScr ].
  all: match goal with
       | IH : forall u, _ = Some u -> ?x ⇝ₙ u |- ?x ⇝ₙ _ =>
           apply IH; first [exact E | reflexivity]
       end.
Qed.

Theorem head_step_nested_eq : forall t,
  head_step t = head_step_nested t /\
  (forall g, g = gap (head_arity sg (spine_head t)) (length (spine_args t)) ->
     head_spine g t = head_step_nested t).
Proof.
  induction t.
  (* an application *)
  5: { assert (Happ : forall g, g = gap (head_arity sg (spine_head (App t1 t2))) (length (spine_args (App t1 t2))) ->
         head_level (fun u => head_step u) (fun g' u => head_spine g' u) g (App t1 t2) t1 t2 = head_step_nested (App t1 t2)).
       { intros g Hg. cbn [head_step_nested]. rewrite contract_beta. unfold head_level, app_shape_at. cbv beta.
         destruct (beta t1 t2) as [u|]; [reflexivity | ].
         rewrite spine_iota_full_head, full_spine_head, <- gap_full_at_arity, <- Hg.
         assert (Hg1 : gap_down g = gap (head_arity sg (spine_head t1)) (length (spine_args t1))).
         { rewrite Hg, spine_args_App, length_app. cbn [spine_head length].
           rewrite Nat.add_1_r. symmetry. apply gap_down_succ. }
         rewrite (proj2 IHt1 _ Hg1), (proj1 IHt2).
         destruct (gap_full g); [ | reflexivity].
         destruct (head_iota sg (spine_head (App t1 t2)) (spine_args (App t1 t2))); reflexivity. }
       split; [exact (Happ _ eq_refl) | intros g Hg; exact (Happ g Hg)]. }
  (* every other former: one node *)
  all: lazymatch goal with |- head_step ?t = _ /\ _ =>
         assert (Hn : head_node (fun u => head_step u) t = head_node head_step_nested t);
         [ | split; [exact Hn | intros ? _; exact Hn] ]
       end.
  all: unfold head_node; cbv beta;
       repeat match goal with IH : head_step ?x = _ /\ _ |- _ => rewrite (proj1 IH) end.
  all: reflexivity.
Qed.

Lemma head_step_nstep : forall t u, head_step t = Some u -> t ⇝ₙ u.
Proof. intros t u. rewrite (proj1 (head_step_nested_eq t)). apply head_step_nested_nstep. Qed.

Lemma whnf_reduces : forall fuel t v, whnf fuel t = HeadForm v -> t ⇝ₙ* v.
Proof.
  induction fuel as [|fuel IH]; intros t v H; cbn [whnf] in H;
    destruct (head_step t) as [u|] eqn:E; try discriminate.
  - injection H as <-. apply rt_refl.
  - eapply rt_trans; [apply rt_step, head_step_nstep, E | apply IH, H].
  - injection H as <-. apply rt_refl.
Qed.

Lemma convert_full_stuck_sound : forall fuel t u,
  convert_full fuel t u = ConvStuck ->
  t <> u /\ exists v, normalize fuel t = StuckTerm v \/ normalize fuel u = StuckTerm v.
Proof.
  intros fuel t u H. unfold convert_full in H.
  destruct (term_eqb t u) eqn:E0; [discriminate | ].
  split; [intros ->; rewrite (proj2 (term_eqb_eq u u) eq_refl) in E0; discriminate | ].
  destruct (normalize fuel t) as [tn|ts|tf]; destruct (normalize fuel u) as [un|us|uf];
    try discriminate; eauto.
  destruct (term_eqb tn un); discriminate.
Qed.

(** Equality is sound for the declared conversion relation: both sides
    reach the reported common form.  A negative answer needs confluence
    and uniqueness of normal forms to be complete. *)
Lemma convert_full_equal_reaches : forall fuel t u v,
  convert_full fuel t u = ConvEqual v -> t ⇝ₙ* v /\ u ⇝ₙ* v.
Proof.
  intros fuel t u v H. unfold convert_full in H.
  destruct (term_eqb t u) eqn:E0.
  - apply term_eqb_eq in E0. injection H as <-. subst. split; apply rt_refl.
  - pose proof (proj1 (normalize_spec fuel t)) as Ht.
    pose proof (proj1 (normalize_spec fuel u)) as Hu.
    destruct (normalize fuel t) as [tn|ts|tf]; destruct (normalize fuel u) as [un|us|uf];
      try discriminate.
    destruct (term_eqb tn un) eqn:E; try discriminate.
    apply term_eqb_eq in E. injection H as <-. subst. auto.
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
Arguments contract_beta {sg}.
Arguments classify_nested_spec {sg}.
Arguments classify_nested_eq {sg}.
Arguments head_step_nested_nstep {sg}.
Arguments head_step_nested_eq {sg}.
Arguments contract_app {sg}.
Arguments next_branches_spec {sg}.
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
Arguments convert_full_stuck_sound {sg}.
Arguments convert_full_equal_reaches {sg}.
Arguments normalize_trace_reaches {sg}.
Arguments joinable_sound {sg}.

(** ** Conversion with lazy δ

    [convert_full] normalizes both sides with every δ-constant unfolded.
    When a side mentions a δ-constant, [convert] first compares the two
    with δ-constants folded.  It normalizes both in the signature whose
    δ-constants are opaque ([sig_opaque]), where a constant [f a] stays
    as it is, and compares the two forms position by position in one
    pass ([conv_lazy]).  Where they differ, the nearest spine around the
    difference with a δ-constant at the head on one of the sides is
    normalized with δ on both sides and compared ([conv_unfold]); a
    constant that is the same on both sides is not unfolded.  A spine is
    unfolded only when nothing inside it has been, and the pass gives up
    when an unfolding does not make the two spines equal.  So no subterm
    is normalized twice by the pass, and apart from these normalizations
    its cost is linear in the size of the two forms.  When the pass does
    not show the sides equal, [convert_full] decides; the answers other
    than [ConvEqual], and every answer for sides without δ-constants, are
    those of [convert_full].

    [ConvEqual v] reports a common reduct [v] of both sides
    ([convert_equal_reaches]): their common normal form when
    [convert_full] decides, and otherwise the two forms put together
    position by position. *)

(** A comparison of the pass gives the common reduct of its two sides,
    if it finds one, and whether it has unfolded δ-constants. *)
Definition lazy_ret {A} (a : A) : option A * bool := (Some a, false).

Definition lazy_bind {A B} (m : option A * bool) (k : A -> option B * bool) : option B * bool :=
  match m with
  | (Some a, d) => let (r, d') := k a in (r, d || d')
  | (None, d) => (None, d)
  end.

Lemma lazy_bind_some : forall {A B} m (k : A -> option B * bool) v,
  fst (lazy_bind m k) = Some v -> exists a, fst m = Some a /\ fst (k a) = Some v.
Proof.
  intros A B [[a|] d] k v H; cbn in H; [ | discriminate H].
  exists a. split; [reflexivity | ]. destruct (k a). exact H.
Qed.

Local Notation "'let?' x ':=' o 'in' body" := (lazy_bind o (fun x => body))
  (at level 200, x name, o at level 100, body at level 200).

Section Lazy.
  Variable sg : signature.
  Variable fuel : nat.

  (** Two leaves, or two different formers. *)
  Definition conv_leaf (t u : term) : option term * bool :=
    (if term_eqb t u then Some t else None, false).

  (** Two spines that differ, normalized with δ and compared. *)
  Definition conv_unfold (t u : term) : option term * bool :=
    (match convert_full sg fuel t u with ConvEqual v => Some v | _ => None end, true).

  (** The branches of two matches, pairwise. *)
  Fixpoint conv_list (cl : term -> term -> option term * bool) (bs bs' : list term) {struct bs}
    : option (list term) * bool :=
    match bs, bs' with
    | [], [] => lazy_ret []
    | b :: bs1, b' :: bs1' => let? c := cl b b' in let? cs := conv_list cl bs1 bs1' in lazy_ret (c :: cs)
    | _, _ => (None, false)
    end.

  (** The same former on both sides, the function of an application
      compared by [cf] and the other components, each the root of a
      spine, by [cl].  Normal forms have no annotation, so [Ann] is
      compared as a leaf. *)
  Definition conv_step (cl cf : term -> term -> option term * bool) (t u : term)
    : option term * bool :=
    match t, u with
    | Pi A B, Pi A' B' => let? a := cl A A' in let? b := cl B B' in lazy_ret (Pi a b)
    | Sigma A B, Sigma A' B' => let? a := cl A A' in let? b := cl B B' in lazy_ret (Sigma a b)
    | Lam b, Lam b' => let? c := cl b b' in lazy_ret (Lam c)
    | App f a, App f' a' => let? g := cf f f' in let? c := cl a a' in lazy_ret (App g c)
    | Pair a b, Pair a' b' => let? c := cl a a' in let? d := cl b b' in lazy_ret (Pair c d)
    | Fst p, Fst p' => let? q := cl p p' in lazy_ret (Fst q)
    | Snd p, Snd p' => let? q := cl p p' in lazy_ret (Snd q)
    | ElimVoid C e, ElimVoid C' e' => let? C1 := cl C C' in let? e1 := cl e e' in lazy_ret (ElimVoid C1 e1)
    | ElimUnit C c x, ElimUnit C' c' x' =>
        let? C1 := cl C C' in let? c1 := cl c c' in let? x1 := cl x x' in lazy_ret (ElimUnit C1 c1 x1)
    | ElimBool C bt bf b, ElimBool C' bt' bf' b' =>
        let? C1 := cl C C' in let? bt1 := cl bt bt' in let? bf1 := cl bf bf' in let? b1 := cl b b' in
        lazy_ret (ElimBool C1 bt1 bf1 b1)
    | Case D s P x bs, Case D' s' P' x' bs' =>
        if String.eqb D D' && sort_eqb s s' then
          let? P1 := cl P P' in let? x1 := cl x x' in let? bs1 := conv_list cl bs bs' in
          lazy_ret (Case D s P1 x1 bs1)
        else (None, false)
    | Fix A k b, Fix A' k' b' =>
        if Nat.eqb k k' then let? A1 := cl A A' in let? b1 := cl b b' in lazy_ret (Fix A1 k b1)
        else (None, false)
    | _, _ => conv_leaf t u
    end.

  (** Two normal forms of the opaque signature; [root]: they are not the
      function of an application.  A difference found without unfolding
      unfolds the spine if a δ-constant is at its head. *)
  Fixpoint conv_lazy (root : bool) (t u : term) {struct t} : option term * bool :=
    match conv_step (fun x y => conv_lazy true x y) (fun x y => conv_lazy false x y) t u with
    | (None, false) => if root && (def_head t || def_head u) then conv_unfold t u else (None, false)
    | r => r
    end.

  Lemma conv_leaf_sound : forall t u v, fst (conv_leaf t u) = Some v -> red sg t v /\ red sg u v.
  Proof.
    intros t u v H. unfold conv_leaf in H.
    destruct (term_eqb t u) eqn:E; cbn in H; [ | discriminate H].
    apply term_eqb_eq in E as <-. injection H as <-. split; apply rt_refl.
  Qed.

  Lemma conv_unfold_sound : forall t u v, fst (conv_unfold t u) = Some v -> red sg t v /\ red sg u v.
  Proof.
    intros t u v H. unfold conv_unfold in H. cbn [fst] in H.
    destruct (convert_full sg fuel t u) as [w| | |] eqn:E; try discriminate H. injection H as <-.
    destruct (convert_full_equal_reaches _ _ _ _ E) as [Ht Hu]. split; apply nsteps_red; assumption.
  Qed.

  Lemma conv_list_sound : forall cl bs bs' cs,
    Forall (fun b => forall b' c, fst (cl b b') = Some c -> red sg b c /\ red sg b' c) bs ->
    fst (conv_list cl bs bs') = Some cs -> Forall2 (red sg) bs cs /\ Forall2 (red sg) bs' cs.
  Proof.
    intros cl bs. induction bs as [|b bs IH]; intros [|b' bs'] cs Hb H; cbn [conv_list] in H;
      try discriminate H.
    - injection H as <-. split; constructor.
    - inversion Hb as [|? ? Hb1 Hbs]; subst.
      apply lazy_bind_some in H as (c & Ec & H). apply lazy_bind_some in H as (cs' & Ecs & H).
      injection H as <-. destruct (Hb1 _ _ Ec). destruct (IH _ _ Hbs Ecs).
      split; constructor; assumption.
  Qed.

  Theorem conv_lazy_sound : forall t root u v,
    fst (conv_lazy root t u) = Some v -> red sg t v /\ red sg u v.
  Proof.
    induction t using term_ind'; intros root u v H; cbn [conv_lazy] in H.
    all: destruct (conv_step _ _ _ u) as [[w|] [|]] eqn:Es; cbn [fst] in H; try discriminate H;
      try (lazymatch type of H with
           | fst (if ?c then _ else _) = _ =>
               destruct c; [exact (conv_unfold_sound _ _ _ H) | discriminate H]
           end);
      injection H as <-; apply (f_equal fst) in Es; cbn [fst] in Es.
    all: unfold conv_step in Es; destruct u; cbv beta iota in Es;
      try exact (conv_leaf_sound _ _ _ Es).
    all: repeat match type of Es with
         | fst (if String.eqb ?a ?b && sort_eqb ?c ?d then _ else _) = _ =>
             let E1 := fresh "E" in let E2 := fresh "E" in
             destruct (String.eqb a b) eqn:E1; [ | discriminate Es];
             destruct (sort_eqb c d) eqn:E2; [ | discriminate Es]; cbn [andb] in Es;
             apply String.eqb_eq in E1; apply sort_eqb_eq in E2; subst
         | fst (if Nat.eqb ?a ?b then _ else _) = _ =>
             let E1 := fresh "E" in
             destruct (Nat.eqb a b) eqn:E1; [ | discriminate Es]; apply Nat.eqb_eq in E1; subst
         | fst (lazy_bind _ _) = _ => apply lazy_bind_some in Es as (? & ?E & Es); cbv beta in Es
         end.
    all: injection Es as <-.
    all: repeat match goal with
         | IH : forall r u v, fst (conv_lazy r ?x u) = Some v -> _, E : fst (conv_lazy _ ?x ?y) = Some ?z |- _ =>
             destruct (IH _ _ _ E); clear E
         | IHl : Forall _ ?l, E : fst (conv_list _ ?l ?l') = Some ?cs |- _ =>
             let Hl := fresh "Hl" in
             assert (Hl : Forall (fun b => forall b' c, fst (conv_lazy true b b') = Some c ->
                                                     red sg b c /\ red sg b' c) l)
               by (eapply Forall_impl; [ | exact IHl]; intros ? Hb ? ?; apply Hb);
             destruct (conv_list_sound _ _ _ _ Hl E); clear E Hl
         end.
    all: split;
      first [ apply red_pi | apply red_sigma | apply red_lam | apply red_app | apply red_pair
            | apply red_fst | apply red_snd | apply red_elim_void | apply red_elim_unit
            | apply red_elim_bool | apply red_case | apply red_fix ]; assumption.
  Qed.
End Lazy.

(** The lazy comparison, when a side mentions a δ-constant and the sides
    differ syntactically: the sides normalized with δ-constants opaque,
    compared by [conv_lazy]. *)
Definition convert_lazy (sg : signature) (fuel : nat) (t u : term) : option term :=
  if (has_def t || has_def u) && negb (term_eqb t u) then
    match normalize (sig_opaque sg) fuel t, normalize (sig_opaque sg) fuel u with
    | NormalForm t1, NormalForm u1 => fst (conv_lazy sg fuel true t1 u1)
    | _, _ => None
    end
  else None.

Definition convert (sg : signature) (fuel : nat) (t u : term) : conv_result :=
  match convert_lazy sg fuel t u with
  | Some v => ConvEqual v
  | None => convert_full sg fuel t u
  end.

Lemma convert_lazy_sound : forall sg fuel t u v,
  convert_lazy sg fuel t u = Some v -> red sg t v /\ red sg u v.
Proof.
  intros sg fuel t u v H. unfold convert_lazy in H.
  destruct ((has_def t || has_def u) && negb (term_eqb t u)); [ | discriminate H].
  pose proof (proj1 (normalize_spec (sg := sig_opaque sg) fuel t)) as Ht.
  pose proof (proj1 (normalize_spec (sg := sig_opaque sg) fuel u)) as Hu.
  destruct (normalize (sig_opaque sg) fuel t) as [t1| |];
    destruct (normalize (sig_opaque sg) fuel u) as [u1| |]; try discriminate H.
  cbn in Ht, Hu. destruct (conv_lazy_sound sg fuel _ _ _ _ H) as [H1 H2].
  split; eapply rt_trans; [apply red_opaque, nsteps_red, Ht | exact H1 | apply red_opaque, nsteps_red, Hu | exact H2].
Qed.

(** Equality is sound for the declared conversion relation: both sides
    reach the reported common form.  A negative answer needs confluence
    and uniqueness of normal forms to be complete. *)
Theorem convert_equal_reaches : forall sg fuel t u v,
  convert sg fuel t u = ConvEqual v -> red sg t v /\ red sg u v.
Proof.
  intros sg fuel t u v H. unfold convert in H.
  destruct (convert_lazy sg fuel t u) as [w|] eqn:E.
  - injection H as <-. exact (convert_lazy_sound _ _ _ _ _ E).
  - destruct (convert_full_equal_reaches _ _ _ _ H) as [Ht Hu]. split; apply nsteps_red; assumption.
Qed.

Theorem convert_equal_sound : forall sg fuel t u v, convert sg fuel t u = ConvEqual v -> conv sg t u.
Proof.
  intros sg fuel t u v H. destruct (convert_equal_reaches _ _ _ _ _ H) as [Ht Hu].
  apply conv_trans with v; [ | apply conv_sym ]; apply red_conv; assumption.
Qed.

Theorem convert_stuck_sound : forall sg fuel t u,
  convert sg fuel t u = ConvStuck ->
  t <> u /\ exists v, normalize sg fuel t = StuckTerm v \/ normalize sg fuel u = StuckTerm v.
Proof.
  intros sg fuel t u H. unfold convert in H.
  destruct (convert_lazy sg fuel t u); [discriminate H | exact (convert_full_stuck_sound _ _ _ H)].
Qed.

Arguments convert_lazy_sound {sg}.
Arguments convert_equal_reaches {sg}.
Arguments convert_equal_sound {sg}.
Arguments convert_stuck_sound {sg}.
