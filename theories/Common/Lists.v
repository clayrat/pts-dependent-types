(** * Pointwise relations on lists

    Facts about [Forall2] that the standard library does not state:
    splitting at a known length, taking apart a [cons] or a singleton on
    the left, the pointwise elements, a partner of a member on either
    side and the reversal; and [firstn] and [skipn] at the length of a
    prefix. *)

From Stdlib Require Import List Arith Lia.
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

Lemma forall2_in_l : forall {A B} (R : A -> B -> Prop) l l' x, Forall2 R l l' -> In x l -> exists y, R x y.
Proof.
  intros A B R l l' x H. induction H as [|a b l l' Hab _ IH]; intros Hin; [destruct Hin | ].
  destruct Hin as [-> | Hin]; [exists b; exact Hab | exact (IH Hin)].
Qed.

Lemma forall2_in_r : forall {A B} (R : A -> B -> Prop) l l' y, Forall2 R l l' -> In y l' -> exists x, In x l /\ R x y.
Proof.
  intros A B R l l' y H. induction H as [|a b l l' Hab _ IH]; intros Hin; [destruct Hin | ].
  destruct Hin as [-> | Hin]; [exists a; split; [left; reflexivity | exact Hab] | ].
  destruct (IH Hin) as (x & Hx & Hr). exists x. split; [right; exact Hx | exact Hr].
Qed.

Lemma forall2_singleton : forall {A B} (R : A -> B -> Prop) a l, Forall2 R [a] l -> exists b, l = [b] /\ R a b.
Proof. intros A B R a l H. inversion H as [| ? b ? l' Hab Hl]; subst. inversion Hl; subst. eauto. Qed.

Lemma forallb_firstn : forall {A} (f : A -> bool) n l, forallb f l = true -> forallb f (firstn n l) = true.
Proof.
  intros A f n l H. rewrite <- (firstn_skipn n l), forallb_app in H. apply andb_prop in H. exact (proj1 H).
Qed.

Lemma firstn_app_exact : forall {A} (l1 l2 : list A) n, n = length l1 -> firstn n (l1 ++ l2) = l1.
Proof. intros A l1 l2 n ->. rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity. Qed.

Lemma skipn_app_exact : forall {A} (l1 l2 : list A) n, n = length l1 -> skipn n (l1 ++ l2) = l2.
Proof. intros A l1 l2 n ->. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. Qed.
