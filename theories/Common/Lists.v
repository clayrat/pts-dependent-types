(** * Pointwise relations on lists

    Facts about [Forall2] that the standard library does not state:
    splitting at a known length, taking apart a [cons] on the left, the
    pointwise elements and the reversal. *)

From Stdlib Require Import List Lia.
Import ListNotations.

Lemma forall2_app_split : forall {A B} (R : A -> B -> Prop) l1 l1' l2 l2', length l1 = length l1' ->
  Forall2 R (l1 ++ l2) (l1' ++ l2') -> Forall2 R l1 l1' /\ Forall2 R l2 l2'.
Proof.
  intros A B R l1. induction l1 as [|a l1 IH]; intros l1' l2 l2' Hl H.
  - destruct l1'; [ | discriminate Hl]. split; [constructor | exact H].
  - destruct l1' as [|a' l1']; [discriminate Hl | ]. cbn [app] in H. inversion H; subst.
    destruct (IH l1' l2 l2' ltac:(cbn in Hl; lia) ltac:(assumption)) as [H1 H2].
    split; [constructor; assumption | exact H2].
Qed.

Lemma forall2_cons_inv : forall {A B} (R : A -> B -> Prop) x l l', Forall2 R (x :: l) l' ->
  exists y l'', l' = y :: l'' /\ R x y /\ Forall2 R l l''.
Proof. intros A B R x l l' H. inversion H; subst. eexists _, _. split; [reflexivity | split; assumption]. Qed.

Lemma forall2_nth : forall {A B} (R : A -> B -> Prop) l l' i d d', Forall2 R l l' -> i < length l ->
  R (nth i l d) (nth i l' d').
Proof.
  intros A B R l l' i d d' H. revert i. induction H as [|x y xs ys Hxy _ IH]; intros i Hi; [cbn in Hi; lia | ].
  destruct i as [|i]; [exact Hxy | apply IH; cbn in Hi; lia].
Qed.

Lemma forall2_rev : forall {A B} (R : A -> B -> Prop) l l', Forall2 R l l' -> Forall2 R (rev l) (rev l').
Proof.
  intros A B R l l' H. induction H; cbn [rev]; [constructor | ].
  apply Forall2_app; [assumption | constructor; [assumption | constructor]].
Qed.

Lemma forallb_firstn : forall {A} (f : A -> bool) n l, forallb f l = true -> forallb f (firstn n l) = true.
Proof.
  intros A f n l H. rewrite <- (firstn_skipn n l), forallb_app in H. apply andb_prop in H. exact (proj1 H).
Qed.
