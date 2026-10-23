(** * Soundness of the checker against the annotated kernel

    A successful run of the checker yields the judgment of PTS.Bidir it
    claims: [tc Γ t None] succeeding with [A] gives [Γ ⊢ t ⇑ A], and
    [tc Γ t (Some T)] gives [Γ ⊢ t ⇓ T]; the validation of inputs gives
    [bwf_ctx] and [btype].  This holds for every specification and any
    fuel and every signature, and does not look at the trace.

    The bridge from the executable helpers to the relations: unfolding by
    [whnf] is normal-order reduction ([whnf_reduces]), hence [⇝*]; an
    equality of [convert] is conversion ([convert_equal_sound]). *)

From Stdlib Require Import List.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From Stdlib Require Import Relations.
From DepTypes.PTS Require Import Syntax Spec Signature Reduction NormalOrder Eval Bidir Check.

Section Sound.
  Variable S : spec.
  Variable sg : signature.
  Variable fuel : nat.
  Local Notation "t ⇝* u" := (red sg t u).
  Local Notation "t ≡ u" := (conv sg t u).
  Local Notation "S ;; G ⊢ t ⇑ A" := (synth S sg G t A).
  Local Notation "S ;; G ⊢ t ⇓ A" := (chk S sg G t A).
  Local Notation bwf_ctx S := (bwf_ctx S sg).
  Local Notation btype S := (btype S sg).

  (** ** Failures never succeed *)

  Lemma reject_ok : forall {A} e log log' (a : A), reject e log = (log', Ok a) -> False.
  Proof. intros A e log log' a H. discriminate H. Qed.

  Lemma no_fuel_ok : forall {A} t log log' (a : A), no_fuel t log = (log', Ok a) -> False.
  Proof. intros A t log log' a H. discriminate H. Qed.

  (** ** What the success of a helper means *)

  Lemma axiom_ok : forall s log log' s',
    axiom S s log = (log', Ok s') -> spec_axiom S s = Some s'.
  Proof.
    intros s log log' s' H. unfold axiom in H.
    destruct (spec_axiom S s); [ | destruct (spec_sort S s); discriminate H].
    cbv in H. congruence.
  Qed.

  Lemma rule_ok : forall t s1 s2 log log' s3,
    rule S t s1 s2 log = (log', Ok s3) -> spec_rule S s1 s2 = Some s3.
  Proof.
    intros t s1 s2 log log' s3 H. unfold rule in H.
    destruct (spec_rule S s1 s2); [ | discriminate H]. cbv in H. congruence.
  Qed.

  Lemma prim_ok : forall t log log' s0,
    prim S t log = (log', Ok s0) -> spec_prim S = Some s0.
  Proof.
    intros t log log' s0 H. unfold prim in H.
    destruct (spec_prim S); [ | discriminate H]. cbv in H. congruence.
  Qed.

  Lemma sigma_rule_ok : forall t s1 s2 log log' s3,
    sigma_rule S t s1 s2 log = (log', Ok s3) -> spec_sigma S s1 s2 = Some s3.
  Proof.
    intros t s1 s2 log log' s3 H. unfold sigma_rule in H.
    destruct (spec_sigma S s1 s2); [ | discriminate H]. cbv in H. congruence.
  Qed.

  Lemma decls_ok : forall t log log' u,
    decls S t log = (log', Ok u) -> spec_decls S = true.
  Proof.
    intros t log log' u H. unfold decls in H.
    destruct (spec_decls S); [reflexivity | discriminate H].
  Qed.

  Lemma whnf_red : forall T V, whnf sg fuel T = HeadForm V -> T ⇝* V.
  Proof. intros T V H. apply nsteps_red, (whnf_reduces fuel), H. Qed.

  Lemma as_sort_ok : forall t T log log' s,
    as_sort sg fuel t T log = (log', Ok s) -> T ⇝* Srt s.
  Proof.
    intros t T log log' s H. unfold as_sort in H.
    destruct (whnf sg fuel T) as [V | V] eqn:W; [ | discriminate H].
    apply whnf_red in W.
    destruct V; try discriminate H.
    destruct T; cbv in H; congruence.
  Qed.

  Lemma as_pi_ok : forall t T log log' A B,
    as_pi sg fuel t T log = (log', Ok (A, B)) -> T ⇝* Pi A B.
  Proof.
    intros t T log log' A B H. unfold as_pi in H.
    destruct (whnf sg fuel T) as [V | V] eqn:W; [ | discriminate H].
    apply whnf_red in W.
    destruct V; try discriminate H. cbv in H. congruence.
  Qed.

  Lemma as_sigma_ok : forall t T log log' A B,
    as_sigma sg fuel t T log = (log', Ok (A, B)) -> T ⇝* Sigma A B.
  Proof.
    intros t T log log' A B H. unfold as_sigma in H.
    destruct (whnf sg fuel T) as [V | V] eqn:W; [ | discriminate H].
    apply whnf_red in W.
    destruct V; try discriminate H. cbv in H. congruence.
  Qed.

  Lemma check_conv_ok : forall t A T log log' u,
    check_conv sg fuel t A T log = (log', Ok u) -> A ≡ T.
  Proof.
    intros t A T log log' u H. unfold check_conv in H.
    destruct (convert sg fuel A T) eqn:E; try discriminate H.
    eapply convert_equal_sound; exact E.
  Qed.

  Lemma family_ok : forall C TC D0 log log' u,
    family sg fuel C TC D0 log = (log', Ok u) ->
    exists D K s, TC ⇝* Pi D K /\ D ≡ D0 /\ K ⇝* Srt s.
  Proof.
    intros C TC D0 log log' u H. unfold family in H.
    apply tbind_ok in H as (log1 & [D K] & Hp & H). apply as_pi_ok in Hp.
    cbv beta iota in H.
    destruct (convert sg fuel D D0) eqn:E; try discriminate H.
    apply tbind_ok in H as (log2 & s & Hs & _). apply as_sort_ok in Hs.
    exists D, K, s. split; [exact Hp | split; [eapply convert_equal_sound; exact E | exact Hs]].
  Qed.

  (** ** Checking a term other than a λ or a pair is synthesis followed
         by conversion *)

  Lemma tc_check_eq : forall G t T, is_lam t = false -> is_pair t = false ->
    tc S sg fuel G t (Some T) =
    (let! A := tc S sg fuel G t None in let! _ := check_conv sg fuel t A T in tret T).
  Proof. intros G t T H H'. destruct t; try discriminate H; try discriminate H'; reflexivity. Qed.

  (** Decomposes a successful run into the facts its steps establish. *)
  Ltac inv_run :=
    repeat match goal with
    | H : tbind _ _ _ = (_, Ok _) |- _ =>
        let l := fresh "log" in let a := fresh "a" in let Ha := fresh "Ha" in
        apply tbind_ok in H as (l & a & Ha & H); cbv beta in H
    | p : (term * term)%type |- _ => destruct p; cbv beta iota in *
    | H : tret _ _ = (_, Ok _) |- _ => apply tret_ok in H; subst
    | H : temit _ _ = (_, Ok _) |- _ => clear H
    | H : reject _ _ = (_, Ok _) |- _ => destruct (reject_ok _ _ _ _ H)
    | H : axiom _ _ _ = (_, Ok _) |- _ => apply axiom_ok in H
    | H : rule _ _ _ _ _ = (_, Ok _) |- _ => apply rule_ok in H
    | H : prim _ _ _ = (_, Ok _) |- _ => apply prim_ok in H
    | H : sigma_rule _ _ _ _ _ = (_, Ok _) |- _ => apply sigma_rule_ok in H
    | H : decls _ _ _ = (_, Ok _) |- _ => apply decls_ok in H
    | H : as_sort _ _ _ _ _ = (_, Ok _) |- _ => apply as_sort_ok in H
    | H : as_pi _ _ _ _ _ = (_, Ok (_, _)) |- _ => apply as_pi_ok in H
    | H : as_sigma _ _ _ _ _ = (_, Ok (_, _)) |- _ => apply as_sigma_ok in H
    | H : family _ _ _ _ _ _ = (_, Ok _) |- _ =>
        let D := fresh "D" in let K := fresh "K" in let s := fresh "s" in
        apply family_ok in H as (D & K & s & ? & ? & ?)
    | H : context [match sig_type ?s ?g with _ => _ end] |- _ =>
        let E := fresh "E" in destruct (sig_type s g) eqn:E
    | H : tc _ _ _ _ _ None _ = (_, Ok _), IH : forall G, _ /\ _ |- _ =>
        apply (proj1 (IH _)) in H
    | H : tc _ _ _ _ _ (Some _) _ = (_, Ok _), IH : forall G, _ /\ _ |- _ =>
        apply (proj2 (IH _)) in H as [? ?]; subst
    end.

  Lemma check_from_synth : forall G t, is_lam t = false -> is_pair t = false ->
    (forall log log' A, tc S sg fuel G t None log = (log', Ok A) -> S ;; G ⊢ t ⇑ A) ->
    forall T log log' A, tc S sg fuel G t (Some T) log = (log', Ok A) ->
      S ;; G ⊢ t ⇓ T /\ A = T.
  Proof.
    intros G t Hl Hp Hs T log log' A H. rewrite (tc_check_eq G t T Hl Hp) in H.
    apply tbind_ok in H as (log1 & A0 & H0 & H). apply Hs in H0.
    apply tbind_ok in H as (log2 & u & Hc & H). apply check_conv_ok in Hc.
    apply tret_ok in H. subst. split; [eapply C_Synth; eassumption | reflexivity].
  Qed.

  (** ** The main lemma *)

  (** A λ or a pair only checks: synthesis fails, and checking unfolds the
      expected type to a Π or a Σ by [rule] and checks the components. *)
  Ltac checking_only rule :=
    split;
    [ intros log log' A H; discriminate H
    | intros T log log' A H; cbn [tc] in H; inv_run;
      split; [eapply rule; eassumption | reflexivity] ].

  (** Any other former synthesizes, and checking it is synthesis followed
      by conversion. *)
  Ltac synthesizing G t :=
    assert (Hs : forall log log' A,
               tc S sg fuel G t None log = (log', Ok A) -> S ;; G ⊢ t ⇑ A)
      by (intros log log' A H; cbn [tc] in H;
          try lazymatch t with
              | Var ?n => destruct (lookup G n) eqn:E; [ | discriminate H]
              end;
          inv_run; econstructor; eauto);
    split; [exact Hs | apply check_from_synth; [reflexivity | reflexivity | exact Hs]].

  (** The cases are told apart by the shape of the term, not by their
      position among the constructors of [term]. *)
  Theorem tc_sound : forall t G,
    (forall log log' A, tc S sg fuel G t None log = (log', Ok A) -> S ;; G ⊢ t ⇑ A) /\
    (forall T log log' A, tc S sg fuel G t (Some T) log = (log', Ok A) ->
       S ;; G ⊢ t ⇓ T /\ A = T).
  Proof.
    induction t; intros G.
    all: lazymatch goal with
         | |- (forall log log' A, tc _ _ _ _ ?t None _ = _ -> _) /\ _ =>
             lazymatch t with
             | Lam _ => checking_only C_Lam
             | Pair _ _ => checking_only C_Pair
             | _ => synthesizing G t
             end
         end.
  Qed.

  Corollary infer_sound : forall G t log log' A,
    infer S sg fuel G t log = (log', Ok A) -> S ;; G ⊢ t ⇑ A.
  Proof. intros G t. apply (proj1 (tc_sound t G)). Qed.

  Corollary check_sound : forall G t T log log' u,
    check S sg fuel G t T log = (log', Ok u) -> S ;; G ⊢ t ⇓ T.
  Proof.
    intros G t T log log' u H. unfold check in H.
    apply tbind_ok in H as (log1 & A & H & _).
    exact (proj1 (proj2 (tc_sound t G) _ _ _ _ H)).
  Qed.

  Lemma infer_sort_ok : forall G A log log' s,
    infer_sort S sg fuel G A log = (log', Ok s) -> exists K, S ;; G ⊢ A ⇑ K /\ K ⇝* Srt s.
  Proof.
    intros G A log log' s H. unfold infer_sort in H.
    apply tbind_ok in H as (log1 & K & HK & H). apply infer_sound in HK.
    apply as_sort_ok in H. now exists K.
  Qed.

  (** ** Validation of inputs *)

  Lemma check_ctx_sound : forall G log log' u,
    check_ctx S sg fuel G log = (log', Ok u) -> bwf_ctx S G.
  Proof.
    induction G as [| A G IH]; intros log log' u H; [constructor | ].
    cbn [check_ctx] in H.
    apply tbind_ok in H as (log1 & u1 & H1 & H). apply IH in H1.
    apply tbind_ok in H as (log2 & u2 & _ & H).
    apply tbind_ok in H as (log3 & s & Hs & _). apply infer_sort_ok in Hs as (K & HK & Hs).
    econstructor; eassumption.
  Qed.

  Lemma check_type_sound : forall G A log log' u,
    check_type S sg fuel G A log = (log', Ok u) -> btype S G A.
  Proof.
    intros G A log log' u H.
    assert (Hgen : forall log log' u,
      (let! _ := infer_sort S sg fuel G A in tret tt) log = (log', Ok u) -> btype S G A).
    { intros l l' v H'. apply tbind_ok in H' as (l1 & s & Hs & _).
      apply infer_sort_ok in Hs as (K & HK & Hs).
      right. exists K, s. split; assumption. }
    destruct A; try exact (Hgen _ _ _ H).
    cbn [check_type] in H. destruct (spec_sort S s) eqn:E; [ | discriminate H].
    left. exists s. split; [reflexivity | exact E].
  Qed.
End Sound.

(** ** The entry points *)

Lemma run_answer_accepted : forall {A} (m : traced event failure A) a,
  snd (run_answer m) = Accepted a -> exists log, m [] = (log, Ok a).
Proof.
  intros A m a H. unfold run_answer in H.
  destruct (run_traced m) as [log r] eqn:E. cbn in H.
  destruct r as [b | [e | t]]; cbn in H; try discriminate H.
  injection H as ->. apply run_traced_ok. rewrite E. reflexivity.
Qed.

Theorem run_infer_sound : forall S sg fuel G t A,
  snd (run_infer S sg fuel G t) = Accepted A ->
  bwf_ctx S sg G /\ synth S sg G t A.
Proof.
  intros S sg fuel G t A H. apply run_answer_accepted in H as [log H].
  unfold infer_in in H.
  apply tbind_ok in H as (l1 & u1 & Hc & H). apply check_ctx_sound in Hc.
  apply tbind_ok in H as (l2 & u2 & _ & H). apply infer_sound in H.
  split; assumption.
Qed.

Theorem run_check_sound : forall S sg fuel G t T u,
  snd (run_check S sg fuel G t T) = Accepted u ->
  bwf_ctx S sg G /\ btype S sg G T /\ chk S sg G t T.
Proof.
  intros S sg fuel G t T u H. apply run_answer_accepted in H as [log H].
  unfold check_in in H.
  apply tbind_ok in H as (l1 & u1 & Hc & H). apply check_ctx_sound in Hc.
  apply tbind_ok in H as (l2 & u2 & _ & H).
  apply tbind_ok in H as (l3 & u3 & Ht & H). apply check_type_sound in Ht.
  apply tbind_ok in H as (l4 & u4 & _ & H). apply check_sound in H.
  repeat split; assumption.
Qed.
