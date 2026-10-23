(** * Normal-order reduction: the strategy of the evaluator

    [red1] of PTS.Reduction is a conversion relation: it contracts any
    redex.  Running a translated PCF program needs a fixed strategy, and
    the observable behaviour of PCF (arguments passed by name, unused
    arguments never evaluated) is that of normal order: always contract
    the leftmost-outermost redex.  [nstep] is that strategy as a
    deterministic one-step relation.

    The order of positions:
    - a redex at the root is contracted first;
    - in [App f a], the function [f] before the argument [a]; the
      argument is reduced only once [f] is neutral;
    - in an eliminator, the scrutinee first (it plays the role of the
      head), then, once it is neutral, the family and the branches from
      left to right;
    - an eliminator instance of the signature with active rules, applied
      to its full arity, is an eliminator too: its last argument, the
      object, first, then the rest of the spine; other spines of
      constants are applications;
    - in a projection, the pair;
    - in [Pi A B] and [Sigma A B], [A] before [B]; in [Pair a b], [a]
      before [b]; under [Lam] the body.

    Normal forms [nf] and neutral terms [ne] are the terms without a redex
    in this sense.  A constant that is not a δ-redex heads a neutral
    spine, like a variable; this includes constructors, so a constructor
    applied to normal arguments is [ne], and a full spine of an
    eliminator is neutral when its object is neutral and no ι-rule
    applies.  The observation of a closed program of type ℕ in the
    PCF translation is an [nf] of the chosen numeral encoding reached by
    [nstep]; a weak-head normal form is not enough.

    [nstep] is defined only on well-shaped terms, so on a raw term the
    absence of a step does not mean a normal form: [App Tt (Ann Tt Unit)]
    has a [red1]-redex in the argument, but no [nstep], since [Tt] is
    neither a λ nor neutral (see Tests.v).  Such a term is [stuck].  The
    evaluator therefore has three answers: a normal form, a stuck term,
    and running out of fuel.  That well-typed terms never get stuck
    (progress for normal order) is a separate obligation; it needs
    inversion of typing up to conversion, hence confluence. *)

From Stdlib Require Import Relations.
From DepTypes.PTS Require Import Syntax Signature Reduction.

Reserved Notation "t ⇝ₙ u" (at level 70, no associativity).
Reserved Notation "t ⇝ₙ* u" (at level 70, no associativity).

(** An ι-step needs a full spine of an eliminator: a hypothesis
    [iota sg t = Some u] is absurd unless [t] is an application, and
    there it contradicts [full_elim sg t = false]. *)
Ltac no_iota :=
  match goal with
  | H : iota _ (App (Lam _) _) = Some _ |- _ => rewrite iota_lam in H; discriminate H
  | H : full_elim _ (App (Lam _) _) = true |- _ =>
      unfold full_elim in H; rewrite elim_view_lam in H; discriminate H
  | H : iota _ _ = Some _ |- _ =>
      first
        [ let f := fresh "f" in let a := fresh "a" in let E := fresh "E" in
          destruct (iota_app _ _ _ H) as (f & a & E); discriminate E
        | let Hf := fresh "Hf" in pose proof (iota_full_elim _ _ _ H) as Hf; congruence ]
  end.

Section NormalOrder.
Variable sg : signature.
Local Notation "t ⇝ u" := (red1 sg t u).
Local Notation "t ⇝* u" := (red sg t u).

(** ** Normal and neutral forms *)

Inductive nf : term -> Prop :=
| NF_Sort : forall s, nf (Srt s)
| NF_Pi : forall A B, nf A -> nf B -> nf (Pi A B)
| NF_Lam : forall b, nf b -> nf (Lam b)
| NF_Void : nf Void
| NF_Unit : nf Unit
| NF_Tt : nf Tt
| NF_Bool : nf Bool
| NF_True : nf BTrue
| NF_False : nf BFalse
| NF_Sigma : forall A B, nf A -> nf B -> nf (Sigma A B)
| NF_Pair : forall a b, nf a -> nf b -> nf (Pair a b)
| NF_Ne : forall n, ne n -> nf n

with ne : term -> Prop :=
| NE_Var : forall n, ne (Var n)
| NE_App : forall n v, full_elim sg (App n v) = false -> ne n -> nf v -> ne (App n v)
| NE_Elim : forall n v, full_elim sg (App n v) = true -> iota sg (App n v) = None ->
    ne n -> ne v -> ne (App n v)
| NE_ElimVoid : forall C n, nf C -> ne n -> ne (ElimVoid C n)
| NE_ElimUnit : forall C c n, nf C -> nf c -> ne n -> ne (ElimUnit C c n)
| NE_ElimBool : forall C t f n, nf C -> nf t -> nf f -> ne n -> ne (ElimBool C t f n)
| NE_Fst : forall n, ne n -> ne (Fst n)
| NE_Snd : forall n, ne n -> ne (Snd n)
| NE_Const : forall g, sig_delta sg g = None -> ne (Const g).

Scheme nf_mut := Induction for nf Sort Prop
  with ne_mut := Induction for ne Sort Prop.
Combined Scheme nf_ne_mut from nf_mut, ne_mut.

Definition is_lam (t : term) : bool :=
  match t with
  | Lam _ => true
  | _ => false
  end.

Definition is_pair (t : term) : bool :=
  match t with
  | Pair _ _ => true
  | _ => false
  end.

(** ** One step of normal order *)

Inductive nstep : term -> term -> Prop :=
(** contractions at the root *)
| N_Beta : forall b u, App (Lam b) u ⇝ₙ subst1 b u
| N_Ann : forall t A, Ann t A ⇝ₙ t
| N_UnitTt : forall C c, ElimUnit C c Tt ⇝ₙ c
| N_BoolTrue : forall C t f, ElimBool C t f BTrue ⇝ₙ t
| N_BoolFalse : forall C t f, ElimBool C t f BFalse ⇝ₙ f
| N_FstPair : forall a b, Fst (Pair a b) ⇝ₙ a
| N_SndPair : forall a b, Snd (Pair a b) ⇝ₙ b
(** application: the function, then the argument *)
| N_AppFun : forall f f' a, full_elim sg (App f a) = false -> is_lam f = false -> f ⇝ₙ f' ->
    App f a ⇝ₙ App f' a
| N_AppArg : forall f a a', full_elim sg (App f a) = false -> ne f -> a ⇝ₙ a' ->
    App f a ⇝ₙ App f a'
(** a full spine of an eliminator instance: the object, then the rest *)
| N_ElimObj : forall f a a', full_elim sg (App f a) = true -> iota sg (App f a) = None ->
    a ⇝ₙ a' -> App f a ⇝ₙ App f a'
| N_ElimRest : forall f f' a, full_elim sg (App f a) = true -> iota sg (App f a) = None ->
    ne a -> f ⇝ₙ f' -> App f a ⇝ₙ App f' a
(** binders *)
| N_PiDom : forall A A' B, A ⇝ₙ A' -> Pi A B ⇝ₙ Pi A' B
| N_PiCod : forall A B B', nf A -> B ⇝ₙ B' -> Pi A B ⇝ₙ Pi A B'
| N_Lam : forall b b', b ⇝ₙ b' -> Lam b ⇝ₙ Lam b'
| N_SigmaDom : forall A A' B, A ⇝ₙ A' -> Sigma A B ⇝ₙ Sigma A' B
| N_SigmaCod : forall A B B', nf A -> B ⇝ₙ B' -> Sigma A B ⇝ₙ Sigma A B'
(** pairs and projections *)
| N_PairL : forall a a' b, a ⇝ₙ a' -> Pair a b ⇝ₙ Pair a' b
| N_PairR : forall a b b', nf a -> b ⇝ₙ b' -> Pair a b ⇝ₙ Pair a b'
| N_FstArg : forall p p', is_pair p = false -> p ⇝ₙ p' -> Fst p ⇝ₙ Fst p'
| N_SndArg : forall p p', is_pair p = false -> p ⇝ₙ p' -> Snd p ⇝ₙ Snd p'
(** eliminators: the scrutinee, then the family and the branches *)
| N_ElimVoidScr : forall C e e', e ⇝ₙ e' -> ElimVoid C e ⇝ₙ ElimVoid C e'
| N_ElimVoidFam : forall C C' e, ne e -> C ⇝ₙ C' -> ElimVoid C e ⇝ₙ ElimVoid C' e
| N_ElimUnitScr : forall C c u u', u ⇝ₙ u' -> ElimUnit C c u ⇝ₙ ElimUnit C c u'
| N_ElimUnitFam : forall C C' c u, ne u -> C ⇝ₙ C' -> ElimUnit C c u ⇝ₙ ElimUnit C' c u
| N_ElimUnitBr : forall C c c' u, ne u -> nf C -> c ⇝ₙ c' ->
    ElimUnit C c u ⇝ₙ ElimUnit C c' u
| N_ElimBoolScr : forall C t f b b', b ⇝ₙ b' -> ElimBool C t f b ⇝ₙ ElimBool C t f b'
| N_ElimBoolFam : forall C C' t f b, ne b -> C ⇝ₙ C' ->
    ElimBool C t f b ⇝ₙ ElimBool C' t f b
| N_ElimBoolTrue : forall C t t' f b, ne b -> nf C -> t ⇝ₙ t' ->
    ElimBool C t f b ⇝ₙ ElimBool C t' f b
| N_ElimBoolFalse : forall C t f f' b, ne b -> nf C -> nf t -> f ⇝ₙ f' ->
    ElimBool C t f b ⇝ₙ ElimBool C t f' b
(** the contractions of the signature at the root, last *)
| N_Delta : forall g b, sig_delta sg g = Some b -> Const g ⇝ₙ b
| N_Iota : forall t u, iota sg t = Some u -> t ⇝ₙ u
where "t ⇝ₙ u" := (nstep t u).

Local Notation "t ⇝ₙ* u" := (clos_refl_trans term nstep t u).

(** ** Normal order is a reduction strategy *)

Lemma nstep_red1 : forall t u, t ⇝ₙ u -> t ⇝ u.
Proof. intros t u H. induction H; constructor; assumption. Qed.

Lemma nsteps_red : forall t u, t ⇝ₙ* u -> t ⇝* u.
Proof.
  intros t u H. induction H;
    [apply rt_step, nstep_red1; assumption | apply rt_refl | eapply rt_trans; eassumption].
Qed.

Lemma nf_ne_no_nstep :
  (forall t, nf t -> forall u, ~ t ⇝ₙ u) /\
  (forall t, ne t -> forall u, ~ t ⇝ₙ u).
Proof.
  apply nf_ne_mut; repeat intro;
    match goal with Hs : _ ⇝ₙ _ |- False => inversion Hs; subst end;
    try congruence; try no_iota;
    repeat match goal with
    | N : ne ?c |- _ =>
        match c with
        | Lam _ => inversion N | Tt => inversion N | BTrue => inversion N
        | BFalse => inversion N | Pair _ _ => inversion N
        end
    end;
    match goal with
    | IH : forall u, ~ ?x ⇝ₙ u, H : ?x ⇝ₙ _ |- _ => exact (IH _ H)
    end.
Qed.

(** ** Stuck terms *)

Definition stuck (t : term) : Prop := ~ nf t /\ forall u, ~ t ⇝ₙ u.

Lemma nf_not_stuck : forall t, nf t -> ~ stuck t.
Proof. intros t H [Hn _]. exact (Hn H). Qed.

Lemma nf_no_nstep : forall t u, nf t -> ~ t ⇝ₙ u.
Proof. intros t u H. now apply (proj1 nf_ne_no_nstep). Qed.

Lemma ne_no_nstep : forall t u, ne t -> ~ t ⇝ₙ u.
Proof. intros t u H. now apply (proj2 nf_ne_no_nstep). Qed.

Lemma nstep_det : forall t u v, t ⇝ₙ u -> t ⇝ₙ v -> u = v.
Proof.
  intros t u v H. revert v.
  induction H; intros v Hv; inversion Hv; subst;
    try congruence; try no_iota;
    repeat match goal with
    | H : is_lam (Lam _) = false |- _ => discriminate H
    | H : is_pair (Pair _ _) = false |- _ => discriminate H
    | H : ?x ⇝ₙ _, N : ne ?x |- _ => destruct (ne_no_nstep _ _ N H)
    | H : ?x ⇝ₙ _, N : nf ?x |- _ => destruct (nf_no_nstep _ _ N H)
    | H : Tt ⇝ₙ _ |- _ => destruct (nf_no_nstep _ _ NF_Tt H)
    | H : BTrue ⇝ₙ _ |- _ => destruct (nf_no_nstep _ _ NF_True H)
    | H : BFalse ⇝ₙ _ |- _ => destruct (nf_no_nstep _ _ NF_False H)
    | N : ne ?c |- _ =>
        match c with
        | Lam _ => inversion N | Tt => inversion N | BTrue => inversion N
        | BFalse => inversion N | Pair _ _ => inversion N
        end
    end;
    try reflexivity;
    try (f_equal; eauto).
Qed.
End NormalOrder.

(** The lemmas take their signature implicitly: it is fixed by their
    statements. *)
Arguments nstep_red1 {sg}.
Arguments nsteps_red {sg}.
Arguments nf_ne_no_nstep {sg}.
Arguments nf_not_stuck {sg}.
Arguments nf_no_nstep {sg}.
Arguments ne_no_nstep {sg}.
Arguments nstep_det {sg}.
