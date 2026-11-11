(** * Inversion and validity for the declarative rules

    The lemmas subject reduction (PTS.SubjectRed) rests on, besides
    weakening and substitution (PTS.TypingSubst):
    - inversion: a judgment on a former is the rule of that former
      followed by conversions.  [ctype Γ X T] says that [T] is the
      natural type [X] of the rule, or a well-sorted type convertible to
      it ([inv_pi] … [inv_fix]);
    - context conversion: the type of the last variable may be replaced
      by a convertible well-sorted one ([ctx_conv1]): weakening past the
      new type, then substituting the new variable for the old one;
    - telescopes: arguments typed one after the other against a
      telescope ([args_typed]), all of them substituted at once by
      [tsub] of PTS.Telescope.  A function of type [Π Ts. R] applied to
      them has type [R[args]] ([typed_apps]); a spine of a head whose
      types are all convertible to [Π Ts. R] has its arguments typed
      against [Ts] and a type convertible to [R[args]] ([apps_inv]);
    - validity: in a type-correct signature, the type of a typed term is
      a sort or a type of some sort ([validity]).  The type of a match,
      [P ū x], is a type: the indices [ū] are typed against the
      telescope of the family, which its type gives.

    Types are not unique: λ is unannotated, and [λx. x] has every type
    [A → A].  Subject reduction is proved without uniqueness. *)

From Stdlib Require Import List Arith Lia Relations.
From Stdlib Require String.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Telescope Spec Signature Reduction SubstLaws Confluence
  Guard Typing TypingSubst.
(* TODO(elim-inductive-types): remove this export once theories/Checked/
   IotaTyped.v of elim-inductive-types (the copy vendored in erasure-cic)
   imports PTS.Confluence.  The spines of a family ([conv_ind_spine]) were
   proved here; they are re-exported for the files that use them from
   this module. *)
From DepTypes.PTS Require Export Confluence.

(** The first condition of [signature_typed]: the types of the constants
    are types.  Validity needs no more. *)
Definition sig_types_typed (S : spec) (sg : signature) : Prop :=
  forall g A, sig_type sg g = Some A -> exists s, has_type S sg [] A (Srt s).

Section Inversion.
  Variable S : spec.
  Variable sg : signature.
  Local Notation typed := (has_type S sg).
  Local Notation wf := (wf_ctx S sg).
  Local Notation "t ≡ u" := (conv sg t u).

  (** ** Inversion *)

  (** [T] is the natural type [X] of a rule, or a well-sorted type
      convertible to it. *)
  Definition ctype (G : ctx) (X T : term) : Prop :=
    X = T \/ (X ≡ T /\ exists s, typed G T (Srt s)).

  Lemma ctype_refl : forall G X, ctype G X X.
  Proof. intros G X. left. reflexivity. Qed.

  Lemma ctype_conv : forall G X A B s, ctype G X A -> A ≡ B -> typed G B (Srt s) -> ctype G X B.
  Proof.
    intros G X A B s HX Hc HB. right. split; [ | exists s; exact HB].
    destruct HX as [-> | [HX _]]; [exact Hc | eapply conv_trans; eassumption].
  Qed.

  Lemma ctype_typed : forall G t X T, typed G t X -> ctype G X T -> typed G t T.
  Proof. intros G t X T H [<- | [Hc [s HT]]]; [exact H | exact (T_Conv _ _ _ _ _ _ _ H HT Hc)]. Qed.

  Lemma ctype_conv_of : forall G X T, ctype G X T -> X ≡ T.
  Proof. intros G X T [<- | [Hc _]]; [apply conv_refl | exact Hc]. Qed.

  Lemma inv_pi : forall G A B T, typed G (Pi A B) T ->
    exists s1 s2 s3, typed G A (Srt s1) /\ typed (A :: G) B (Srt s2) /\
      spec_rule S s1 s2 = Some s3 /\ ctype G (Srt s3) T.
  Proof.
    intros G A B T H. remember (Pi A B) as t eqn:Et. revert A B Et.
    induction H; intros A' B' Et; try discriminate Et.
    - injection Et as <- <-. exists s1, s2, s3. repeat split; try assumption. apply ctype_refl.
    - destruct (IHhas_type1 _ _ Et) as (s1 & s2 & s3 & H1' & H2' & H3' & H4').
      exists s1, s2, s3. repeat split; try assumption. eapply ctype_conv; eassumption.
  Qed.

  Lemma inv_lam : forall G b T, typed G (Lam b) T ->
    exists A B s, typed (A :: G) b B /\ typed G (Pi A B) (Srt s) /\ ctype G (Pi A B) T.
  Proof.
    intros G b T H. remember (Lam b) as t eqn:Et. revert b Et.
    induction H; intros b' Et; try discriminate Et.
    - injection Et as <-. exists A, B, s. repeat split; try assumption. apply ctype_refl.
    - destruct (IHhas_type1 _ Et) as (A' & B' & s' & H1' & H2' & H3').
      exists A', B', s'. repeat split; try assumption. eapply ctype_conv; eassumption.
  Qed.

  Lemma inv_app : forall G f u T, typed G (App f u) T ->
    exists A B, typed G f (Pi A B) /\ typed G u A /\ ctype G (subst1 B u) T.
  Proof.
    intros G f u T H. remember (App f u) as t eqn:Et. revert f u Et.
    induction H; intros f' u' Et; try discriminate Et.
    - injection Et as <- <-. exists A, B. repeat split; try assumption. apply ctype_refl.
    - destruct (IHhas_type1 _ _ Et) as (A' & B' & H1' & H2' & H3').
      exists A', B'. repeat split; try assumption. eapply ctype_conv; eassumption.
  Qed.

  Lemma inv_ann : forall G t A T, typed G (Ann t A) T ->
    exists s, typed G A (Srt s) /\ typed G t A /\ ctype G A T.
  Proof.
    intros G t A T H. remember (Ann t A) as u eqn:Et. revert t A Et.
    induction H; intros t' A' Et; try discriminate Et.
    - injection Et as <- <-. exists s. repeat split; try assumption. apply ctype_refl.
    - destruct (IHhas_type1 _ _ Et) as (s' & H1' & H2' & H3').
      exists s'. repeat split; try assumption. eapply ctype_conv; eassumption.
  Qed.

  Lemma inv_elim_void : forall G C e T, typed G (ElimVoid C e) T ->
    exists s, typed G C (Pi Void (Srt s)) /\ typed G e Void /\ ctype G (App C e) T.
  Proof.
    intros G C e T H. remember (ElimVoid C e) as u eqn:Et. revert C e Et.
    induction H; intros C' e' Et; try discriminate Et.
    - destruct (IHhas_type1 _ _ Et) as (s' & H1' & H2' & H3').
      exists s'. repeat split; try assumption. eapply ctype_conv; eassumption.
    - injection Et as <- <-. exists s. repeat split; try assumption. apply ctype_refl.
  Qed.

  Lemma inv_elim_unit : forall G C c u T, typed G (ElimUnit C c u) T ->
    exists s, typed G C (Pi Unit (Srt s)) /\ typed G c (App C Tt) /\ typed G u Unit /\
      ctype G (App C u) T.
  Proof.
    intros G C c u T H. remember (ElimUnit C c u) as v eqn:Et. revert C c u Et.
    induction H; intros C' c' u' Et; try discriminate Et.
    - destruct (IHhas_type1 _ _ _ Et) as (s' & H1' & H2' & H3' & H4').
      exists s'. repeat split; try assumption. eapply ctype_conv; eassumption.
    - injection Et as <- <- <-. exists s. repeat split; try assumption. apply ctype_refl.
  Qed.

  Lemma inv_elim_bool : forall G C t f b T, typed G (ElimBool C t f b) T ->
    exists s, typed G C (Pi Bool (Srt s)) /\ typed G t (App C BTrue) /\ typed G f (App C BFalse) /\
      typed G b Bool /\ ctype G (App C b) T.
  Proof.
    intros G C t f b T H. remember (ElimBool C t f b) as v eqn:Et. revert C t f b Et.
    induction H; intros C' t' f' b' Et; try discriminate Et.
    - destruct (IHhas_type1 _ _ _ _ Et) as (s' & H1' & H2' & H3' & H4' & H5').
      exists s'. repeat split; try assumption. eapply ctype_conv; eassumption.
    - injection Et as <- <- <- <-. exists s. repeat split; try assumption. apply ctype_refl.
  Qed.

  Lemma inv_sigma : forall G A B T, typed G (Sigma A B) T ->
    exists s1 s2 s3, typed G A (Srt s1) /\ typed (A :: G) B (Srt s2) /\
      spec_sigma S s1 s2 = Some s3 /\ ctype G (Srt s3) T.
  Proof.
    intros G A B T H. remember (Sigma A B) as t eqn:Et. revert A B Et.
    induction H; intros A' B' Et; try discriminate Et.
    - destruct (IHhas_type1 _ _ Et) as (s1' & s2' & s3' & H1' & H2' & H3' & H4').
      exists s1', s2', s3'. repeat split; try assumption. eapply ctype_conv; eassumption.
    - injection Et as <- <-. exists s1, s2, s3. repeat split; try assumption. apply ctype_refl.
  Qed.

  Lemma inv_pair : forall G a b T, typed G (Pair a b) T ->
    exists A B s, typed G (Sigma A B) (Srt s) /\ typed G a A /\ typed G b (subst1 B a) /\
      ctype G (Sigma A B) T.
  Proof.
    intros G a b T H. remember (Pair a b) as t eqn:Et. revert a b Et.
    induction H; intros a' b' Et; try discriminate Et.
    - destruct (IHhas_type1 _ _ Et) as (A' & B' & s' & H1' & H2' & H3' & H4').
      exists A', B', s'. repeat split; try assumption. eapply ctype_conv; eassumption.
    - injection Et as <- <-. exists A, B, s. repeat split; try assumption. apply ctype_refl.
  Qed.

  Lemma inv_fst : forall G p T, typed G (Fst p) T ->
    exists A B, typed G p (Sigma A B) /\ ctype G A T.
  Proof.
    intros G p T H. remember (Fst p) as t eqn:Et. revert p Et.
    induction H; intros p' Et; try discriminate Et.
    - destruct (IHhas_type1 _ Et) as (A' & B' & H1' & H2').
      exists A', B'. split; [assumption | eapply ctype_conv; eassumption].
    - injection Et as <-. exists A, B. split; [assumption | apply ctype_refl].
  Qed.

  Lemma inv_snd : forall G p T, typed G (Snd p) T ->
    exists A B, typed G p (Sigma A B) /\ ctype G (subst1 B (Fst p)) T.
  Proof.
    intros G p T H. remember (Snd p) as t eqn:Et. revert p Et.
    induction H; intros p' Et; try discriminate Et.
    - destruct (IHhas_type1 _ Et) as (A' & B' & H1' & H2').
      exists A', B'. split; [assumption | eapply ctype_conv; eassumption].
    - injection Et as <-. exists A, B. split; [assumption | apply ctype_refl].
  Qed.

  Lemma inv_const : forall G g T, typed G (Const g) T ->
    exists A, wf G /\ spec_decls S = true /\ sig_type sg g = Some A /\ ctype G A T.
  Proof.
    intros G g T H. remember (Const g) as t eqn:Et. revert g Et.
    induction H; intros g' Et; try discriminate Et.
    - destruct (IHhas_type1 _ Et) as (A' & H1' & H2' & H3' & H4').
      exists A'. repeat split; try assumption. eapply ctype_conv; eassumption.
    - injection Et as <-. exists A. repeat split; try assumption. apply ctype_refl.
  Qed.

  Lemma inv_case : forall G D s P x bs T, typed G (Case D s P x bs) T ->
    exists d ps us, spec_decls S = true /\ sig_ind sg D = Some d /\
      allows_elimination S (ind_elim d) s = true /\
      length ps = length (ind_params d) /\ length us = length (ind_indices d) /\
      typed G x (apps (Const (Ind D)) (ps ++ us)) /\ typed G P (case_motive_type d ps s) /\
      has_branches S sg G d ps P (ind_ctors d) bs /\ ctype G (apps P (us ++ [x])) T.
  Proof.
    intros G D s P x bs T H. remember (Case D s P x bs) as t eqn:Et. revert D s P x bs Et.
    induction H; intros Dq sq Pq xq bsq Et; try discriminate Et.
    - destruct (IHhas_type1 _ _ _ _ _ Et) as (d' & ps' & us' & H1' & H2' & H3' & H4' & H5' & H6' & H7' & H8' & H9').
      exists d', ps', us'. repeat split; try assumption. eapply ctype_conv; eassumption.
    - injection Et as <- <- <- <- <-. exists d, ps, us. repeat split; try assumption. apply ctype_refl.
  Qed.

  Lemma inv_fix : forall G A k b T, typed G (Fix A k b) T ->
    exists s D, typed G A (Srt s) /\ struct_arg sg A k D /\ sig_ind sg D <> None /\
      typed (A :: G) b (lift 1 A) /\ fix_guarded sg k b /\ ctype G A T.
  Proof.
    intros G A k b T H. remember (Fix A k b) as t eqn:Et. revert A k b Et.
    induction H; intros A' k' b' Et; try discriminate Et.
    - destruct (IHhas_type1 _ _ _ Et) as (s' & D' & H1' & H2' & H3' & H4' & H5' & H6').
      exists s', D'. repeat split; try assumption. eapply ctype_conv; eassumption.
    - injection Et as <- <- <-. exists s, D. repeat split; try assumption. apply ctype_refl.
  Qed.

  Lemma inv_var : forall G n T, typed G (Var n) T -> exists A, lookup G n = Some A /\ ctype G A T.
  Proof.
    intros G n T H. remember (Var n) as t eqn:Et. revert n Et.
    induction H; intros n' Et; try discriminate Et.
    - injection Et as <-. eexists. split; [eassumption | apply ctype_refl].
    - destruct (IHhas_type1 _ Et) as (A' & Hl & Hc). exists A'. split; [exact Hl | eapply ctype_conv; eassumption].
  Qed.

  Lemma inv_sort : forall G s T, typed G (Srt s) T -> exists s', spec_axiom S s = Some s' /\ ctype G (Srt s') T.
  Proof.
    intros G s T H. remember (Srt s) as t eqn:Et. revert s Et.
    induction H; intros sx Et; try discriminate Et.
    - injection Et as <-. eexists. split; [eassumption | apply ctype_refl].
    - destruct (IHhas_type1 _ Et) as (s1 & Ha & Hc). exists s1. split; [exact Ha | eapply ctype_conv; eassumption].
  Qed.

  (** The primitive types live in the sort of the primitives. *)
  Lemma inv_prim : forall G t T, typed G t T -> t = Void \/ t = Unit \/ t = Bool ->
    exists s0, spec_prim S = Some s0 /\ ctype G (Srt s0) T.
  Proof.
    intros G t T H. induction H; intros Ht; try (destruct Ht as [E | [E | E]]; discriminate E).
    all: try (eexists; split; [eassumption | apply ctype_refl]).
    destruct (IHhas_type1 Ht) as (s1 & Hp & Hc). exists s1. split; [exact Hp | eapply ctype_conv; eassumption].
  Qed.

  Lemma inv_tt : forall G T, typed G Tt T -> ctype G Unit T.
  Proof.
    intros G T H. remember Tt as t eqn:Et. induction H; try discriminate Et.
    - eapply ctype_conv; [exact (IHhas_type1 Et) | eassumption | eassumption].
    - apply ctype_refl.
  Qed.

  Lemma inv_bool_value : forall G b T, typed G b T -> b = BTrue \/ b = BFalse -> ctype G Bool T.
  Proof.
    intros G b T H Hb. induction H; try (destruct Hb as [Hb | Hb]; discriminate Hb).
    - eapply ctype_conv; [exact (IHhas_type1 Hb) | eassumption | eassumption].
    - apply ctype_refl.
    - apply ctype_refl.
  Qed.

  (** The branch of a constructor has the type the motive gives it. *)
  Lemma branches_nth : forall G d ps P cs bs, has_branches S sg G d ps P cs bs ->
    forall i c b, nth_error cs i = Some c -> nth_error bs i = Some b ->
    typed G b (case_branch_type d ps P c).
  Proof.
    intros G d ps P cs bs H. induction H as [|G d ps P c cs b bs Hb _ IH]; intros i c' b' Hc Hb'.
    - destruct i; discriminate Hc.
    - destruct i as [|i]; cbn [nth_error] in Hc, Hb'.
      + injection Hc as <-. injection Hb' as <-. exact Hb.
      + exact (IH i c' b' Hc Hb').
  Qed.

  Lemma branches_length : forall G d ps P cs bs, has_branches S sg G d ps P cs bs -> length bs = length cs.
  Proof. intros G d ps P cs bs H. induction H; cbn [length]; congruence. Qed.

  (** ** Contexts *)

  Lemma wf_cons_inv : forall G A, wf (A :: G) -> exists s, typed G A (Srt s).
  Proof. intros G A H. inversion H; subst. eexists; eassumption. Qed.

  Lemma wf_lookup : forall G n A, wf G -> lookup G n = Some A -> exists s, typed G A (Srt s).
  Proof.
    induction G as [|B G IH]; intros n A HG Hl; [destruct n; discriminate Hl | ].
    destruct (wf_cons_inv _ _ HG) as [s HB].
    destruct n as [|n].
    - rewrite lookup_cons_0 in Hl. injection Hl as <-. exists s.
      exact (typing_weaken1 S sg _ _ _ _ _ HB HB).
    - rewrite lookup_cons_S in Hl. destruct (lookup G n) as [A'|] eqn:E; [ | discriminate Hl].
      injection Hl as <-. destruct (IH n A' (typed_wf S sg _ _ _ HB) E) as [s' HA'].
      exists s'. exact (typing_weaken1 S sg _ _ _ _ _ HA' HB).
  Qed.

  (** A closed judgment holds in every context. *)
  Lemma typed_closed_weaken : forall G t A, typed [] t A -> closed t = true -> closed A = true ->
    wf G -> typed G t A.
  Proof.
    intros G t A H Ht HA HG.
    pose proof (proj1 (proj2 (typing_rename S sg)) [] t A H G (fun n => n) HG) as H'.
    rewrite (rename_closed _ t Ht), (rename_closed _ A HA) in H'. apply H'.
    intros n B HB. destruct n; discriminate HB.
  Qed.

  (** A judgment in a context [Gm] holds in [Gm ++ G]: the variables of
      [Gm] keep their positions. *)
  Theorem typed_weaken_below : forall Gm G, wf Gm -> wf G ->
    wf (Gm ++ G) /\ (forall t T, typed Gm t T -> typed (Gm ++ G) t T).
  Proof.
    induction Gm as [|A Gm IH]; intros G HGm HG.
    - split; [exact HG | ]. intros t T Ht.
      pose proof (proj1 (proj2 (typing_rename S sg)) [] t T Ht G (fun n => n) HG) as H.
      rewrite !rename_id in H. apply H. intros n B HB. destruct n; discriminate HB.
    - destruct (wf_cons_inv _ _ HGm) as [s HA].
      destruct (IH G (typed_wf S sg _ _ _ HA) HG) as [HG' Hw].
      pose proof (W_Cons _ _ _ _ _ (Hw _ _ HA)) as HG''.
      split; [exact HG'' | ]. intros t T Ht.
      pose proof (proj1 (proj2 (typing_rename S sg)) _ t T Ht _ (fun n => n) HG'') as H.
      rewrite !rename_id in H. apply H. intros n B HB. rewrite rename_id.
      exact (lookup_app_some (A :: Gm) G n B HB).
  Qed.

  (** Context conversion, at the last variable. *)
  Theorem ctx_conv1 : forall G A A' t T s, typed (A :: G) t T -> typed G A' (Srt s) -> A ≡ A' ->
    typed (A' :: G) t T.
  Proof.
    intros G A A' t T s Ht HA' Hc.
    destruct (wf_cons_inv _ _ (typed_wf S sg _ _ _ Ht)) as [s0 HA].
    pose proof (typing_weaken1 S sg _ _ _ _ _ HA HA') as HA1.
    change (lift 1 (Srt s0)) with (Srt s0) in HA1.
    assert (Hr : ren_ok (A :: G) (lift 1 A :: A' :: G) (up_ren (Nat.add 1))).
    { apply ren_ok_up. intros n B HB. change (Nat.add 1 n) with (Datatypes.S n).
      rewrite lookup_cons_S, HB. reflexivity. }
    pose proof (proj1 (proj2 (typing_rename S sg)) _ _ _ Ht _ _ (W_Cons _ _ _ _ _ HA1) Hr) as Ht1.
    assert (H0 : typed (A' :: G) (Var 0) (lift 1 A)).
    { eapply T_Conv; [ | exact HA1 | ].
      - apply T_Var; [exact (W_Cons _ _ _ _ _ HA') | apply lookup_cons_0].
      - unfold lift. apply conv_rename. apply conv_sym. exact Hc. }
    pose proof (typing_subst1 S sg _ _ _ _ _ H0 Ht1) as Ht2.
    rewrite !subst_shift_back in Ht2. exact Ht2.
  Qed.

  (** ** Arguments typed against a telescope *)

  Inductive args_typed (G : ctx) : list term -> list term -> Prop :=
  | AT_Nil : args_typed G [] []
  | AT_Cons : forall T Ts a args, typed G a T ->
      args_typed G (subst_tele (scons a Var) Ts) args -> args_typed G (T :: Ts) (a :: args).

  Lemma args_typed_length : forall G Ts args, args_typed G Ts args -> length Ts = length args.
  Proof.
    intros G Ts args H. induction H as [|T Ts a args _ _ IH]; [reflexivity | ].
    cbn [length]. rewrite subst_tele_length in IH. rewrite IH. reflexivity.
  Qed.

  Lemma args_typed_cons_inv : forall G T Ts a args, args_typed G (T :: Ts) (a :: args) ->
    typed G a T /\ args_typed G (subst_tele (scons a Var) Ts) args.
  Proof. intros G T Ts a args H. inversion H; subst. split; assumption. Qed.

  Lemma args_typed_app : forall args1 G Ts1 Ts2 args2, length Ts1 = length args1 ->
    args_typed G (Ts1 ++ Ts2) (args1 ++ args2) <->
    args_typed G Ts1 args1 /\ args_typed G (subst_tele (tsub args1) Ts2) args2.
  Proof.
    induction args1 as [|a args1 IH]; intros G Ts1 Ts2 args2 Hl.
    - destruct Ts1; [ | discriminate Hl]. cbn [app]. rewrite subst_tele_var by exact tsub_nil.
      split; [intros H; split; [constructor | exact H] | intros [_ H]; exact H].
    - destruct Ts1 as [|T Ts1]; [discriminate Hl | ]. cbn [app length] in *. injection Hl as Hl.
      assert (Ec : subst_tele (fun n => subst (tsub args1) (upn (length Ts1) (scons a Var) n)) Ts2 =
                   subst_tele (tsub (a :: args1)) Ts2).
      { apply subst_tele_ext. intros n. rewrite Hl. apply tsub_cons. }
      split.
      + intros H. apply args_typed_cons_inv in H as [Ha H]. rewrite subst_tele_app in H.
        apply IH in H as [H1 H2]; [ | rewrite subst_tele_length; exact Hl].
        split; [constructor; assumption | ].
        rewrite subst_tele_subst_tele, Ec in H2. exact H2.
      + intros [H1 H2]. apply args_typed_cons_inv in H1 as [Ha H1]. constructor; [exact Ha | ].
        rewrite subst_tele_app. apply IH; [rewrite subst_tele_length; exact Hl | ].
        split; [exact H1 | ]. rewrite subst_tele_subst_tele, Ec. exact H2.
  Qed.

  (** A function of type [Π Ts. R] applied to arguments typed against [Ts]. *)
  Lemma typed_apps : forall G Ts args h R, args_typed G Ts args -> typed G h (pis Ts R) ->
    typed G (apps h args) (subst (tsub args) R).
  Proof.
    intros G Ts args h R H. revert h R.
    induction H as [|T Ts a args Ha Hargs IH]; intros h R Hh.
    - rewrite subst_tsub_nil. exact Hh.
    - cbn [pis] in Hh. pose proof (T_App _ _ _ _ _ _ _ Hh Ha) as H1.
      unfold subst1 in H1. rewrite subst_pis in H1.
      pose proof (IH _ _ H1) as H2. change (apps h (a :: args)) with (apps (App h a) args).
      rewrite (subst_tsub_cons a args (length Ts)) in H2; [exact H2 | ].
      rewrite <- (args_typed_length _ _ _ Hargs), subst_tele_length. reflexivity.
  Qed.

  (** The type reached is a type. *)
  Lemma typed_pis_inst : forall G Ts args R s, args_typed G Ts args -> typed G (pis Ts R) (Srt s) ->
    exists s', typed G (subst (tsub args) R) (Srt s').
  Proof.
    intros G Ts args R s H. revert R s.
    induction H as [|T Ts a args Ha Hargs IH]; intros R s HR.
    - exists s. rewrite subst_tsub_nil. exact HR.
    - cbn [pis] in HR. destruct (inv_pi _ _ _ _ HR) as (s1 & s2 & s3 & _ & HB & _ & _).
      pose proof (typing_subst1 S sg _ _ _ _ _ Ha HB) as H1.
      change (subst1 (Srt s2) a) with (Srt s2) in H1. unfold subst1 in H1. rewrite subst_pis in H1.
      destruct (IH _ _ H1) as [s' H2]. exists s'.
      rewrite (subst_tsub_cons a args (length Ts)) in H2; [exact H2 | ].
      rewrite <- (args_typed_length _ _ _ Hargs), subst_tele_length. reflexivity.
  Qed.

  (** A spine of a head whose every type is convertible to [Π Ts. R0]. *)
  Theorem apps_inv : forall args G h T Ts R0 s0, length Ts = length args ->
    typed G (apps h args) T -> (forall H, typed G h H -> H ≡ pis Ts R0) ->
    typed G (pis Ts R0) (Srt s0) ->
    args_typed G Ts args /\ subst (tsub args) R0 ≡ T.
  Proof.
    induction args as [|a args IH] using rev_ind; intros G h T Ts R0 s0 Hl Ht Hh HP.
    - destruct Ts; [ | discriminate Hl]. split; [constructor | ].
      rewrite subst_tsub_nil. apply conv_sym. exact (Hh T Ht).
    - assert (HTs : Ts <> []) by (intros ->; rewrite length_app in Hl; cbn in Hl; lia).
      destruct (exists_last HTs) as (Ts' & Tl & ->).
      rewrite !length_app in Hl. cbn [length] in Hl.
      rewrite apps_snoc in Ht. destruct (inv_app _ _ _ _ Ht) as (A & B & Hf & Ha & HT).
      rewrite pis_app in Hh, HP. cbn [pis] in Hh, HP.
      destruct (IH G h (Pi A B) Ts' (Pi Tl R0) s0 ltac:(lia) Hf Hh HP) as [Hargs Hc].
      cbn [subst] in Hc. apply pi_inj in Hc as [HcA HcB].
      destruct (typed_pis_inst _ _ _ _ _ Hargs HP) as [s' HPi]. cbn [subst] in HPi.
      destruct (inv_pi _ _ _ _ HPi) as (s1 & _ & _ & HTl & _ & _ & _).
      assert (Ha' : typed G a (subst (tsub args) Tl)) by exact (T_Conv _ _ _ _ _ _ _ Ha HTl (conv_sym _ _ HcA)).
      split.
      + apply (proj2 (args_typed_app args G Ts' [Tl] [a] ltac:(lia))). split; [exact Hargs | ].
        cbn [subst_tele]. constructor; [exact Ha' | constructor].
      + rewrite subst_tsub_snoc. eapply conv_trans; [ | exact (ctype_conv_of _ _ _ HT)].
        apply conv_subst. exact HcB.
  Qed.

  (** Arguments typed against a telescope substitute for its variables:
      the variable of the outermost entry, under the others, first. *)
  Lemma tele_subst_ok : forall Ts G A a, typed G a A -> wf (rev Ts ++ A :: G) ->
    wf (rev (subst_tele (scons a Var) Ts) ++ G) /\
    sub_ok S sg (rev Ts ++ A :: G) (rev (subst_tele (scons a Var) Ts) ++ G) (upn (length Ts) (scons a Var)).
  Proof.
    induction Ts as [|T Ts IH] using rev_ind; intros G A a Ha HG.
    - cbn [rev app subst_tele length upn]. pose proof (typed_wf S sg _ _ _ Ha) as HG0. split; [exact HG0 | ].
      intros [|n] B HB.
      + rewrite lookup_cons_0 in HB. injection HB as <-.
        change (typed G a (subst1 (lift 1 A) a)). rewrite subst1_lift. exact Ha.
      + rewrite lookup_cons_S in HB. destruct (lookup G n) as [B'|] eqn:E; [ | discriminate HB].
        injection HB as <-. change (typed G (Var n) (subst1 (lift 1 B') a)). rewrite subst1_lift.
        apply T_Var; [exact HG0 | exact E].
    - rewrite rev_app_distr in HG |- *. cbn [rev app] in HG |- *.
      destruct (wf_cons_inv _ _ HG) as [s HT].
      destruct (IH G A a Ha (typed_wf S sg _ _ _ HT)) as [HG' Hsub].
      pose proof (proj1 (proj2 (typing_subst S sg)) _ _ _ HT _ _ HG' Hsub) as HT'.
      cbn [subst] in HT'.
      rewrite subst_tele_app, rev_app_distr. cbn [subst_tele rev app].
      rewrite length_app. cbn [length]. rewrite Nat.add_1_r. cbn [upn].
      split; [exact (W_Cons _ _ _ _ _ HT') | exact (sub_ok_up S sg _ _ _ _ _ Hsub HT')].
  Qed.

  Theorem typing_tsub : forall G Ts args, args_typed G Ts args -> forall t T, typed (rev Ts ++ G) t T ->
    typed G (subst (tsub args) t) (subst (tsub args) T).
  Proof.
    intros G Ts args H. induction H as [|T0 Ts a args Ha Hargs IH]; intros t T Ht.
    - rewrite !subst_tsub_nil. exact Ht.
    - cbn [rev] in Ht. rewrite <- app_assoc in Ht. cbn [app] in Ht.
      destruct (tele_subst_ok Ts G T0 a Ha (typed_wf S sg _ _ _ Ht)) as [HG' Hsub].
      pose proof (proj1 (proj2 (typing_subst S sg)) _ _ _ Ht _ _ HG' Hsub) as H1.
      pose proof (IH _ _ H1) as H2.
      assert (Hl : length Ts = length args).
      { rewrite <- (args_typed_length _ _ _ Hargs), subst_tele_length. reflexivity. }
      rewrite !(subst_tsub_cons a args (length Ts)) in H2 by exact Hl. exact H2.
  Qed.

  (** ** Validity *)

  (** Validity needs of a type-correct signature only that the types of
      its constants are types ([sig_types_typed]): the lemmas below take
      that premise ([..._t]), and their forms for [signature_typed]
      follow. *)
  Lemma const_type_typed_t : sig_types_typed S sg -> forall G g A, wf G -> sig_type sg g = Some A ->
    exists s, typed G A (Srt s).
  Proof.
    intros Hty G g A HG Hg. destruct (Hty g A Hg) as [s Hs]. exists s.
    apply typed_closed_weaken; [exact Hs | exact (sig_type_closed _ _ _ Hg) | reflexivity | exact HG].
  Qed.

  Lemma const_type_typed : signature_typed S sg -> forall G g A, wf G -> sig_type sg g = Some A ->
    exists s, typed G A (Srt s).
  Proof. intros Hsig. exact (const_type_typed_t (proj1 Hsig)). Qed.

  (** Every type of a constant is convertible to its declared type. *)
  Lemma const_head : forall G g A, sig_type sg g = Some A -> forall H, typed G (Const g) H -> H ≡ A.
  Proof.
    intros G g A Hg H Ht. destruct (inv_const _ _ _ Ht) as (A' & _ & _ & Hg' & HA').
    rewrite Hg in Hg'. injection Hg' as <-. apply conv_sym. exact (ctype_conv_of _ _ _ HA').
  Qed.

  (** The type of a match is a type: the indices are typed against the
      telescope of the family, the motive applied to them and to the
      scrutinee is a type of its sort. *)
  Lemma case_type_typed_t : sig_types_typed S sg -> forall G D s P x d ps us s',
    sig_ind sg D = Some d -> length ps = length (ind_params d) -> length us = length (ind_indices d) ->
    typed G x (apps (Const (Ind D)) (ps ++ us)) -> typed G P (case_motive_type d ps s) ->
    typed G (apps (Const (Ind D)) (ps ++ us)) (Srt s') ->
    typed G (apps P (us ++ [x])) (Srt s).
  Proof.
    intros Hsig G D s P x d ps us s' Hd Hlp Hlu Hx HP HX.
    pose proof (typed_wf S sg _ _ _ Hx) as HG.
    pose proof (sig_type_ind sg D d Hd) as Hty.
    destruct (const_type_typed_t Hsig G _ _ HG Hty) as [s0 Hs0]. unfold ind_type in Hs0.
    assert (Hl : length (ind_params d ++ ind_indices d) = length (ps ++ us)) by (rewrite !length_app; lia).
    destruct (apps_inv (ps ++ us) G (Const (Ind D)) _ _ _ _ Hl HX (const_head _ _ _ Hty) Hs0) as [Hargs _].
    destruct (proj1 (args_typed_app ps G _ _ us (eq_sym Hlp)) Hargs) as [_ Hus].
    assert (Hmt : case_motive_type d ps s =
                  pis (subst_tele (tsub ps) (ind_indices d))
                      (Pi (apps (Const (Ind D)) (map (lift (length us)) ps ++ vars 0 (length us))) (Srt s))).
    { unfold case_motive_type, inst_tele. cbv zeta. rewrite (sig_ind_name _ _ _ Hd), <- Hlu. f_equal.
      apply (inst_tele_tsub _ ps 0). rewrite Hlp. exact (proj1 (sig_ind_closed _ _ _ Hd)). }
    rewrite Hmt in HP. pose proof (typed_apps _ _ _ _ _ Hus HP) as H1.
    cbn [subst] in H1. rewrite subst_apps, map_app, map_tsub_lift, map_tsub_vars0 in H1. cbn [subst] in H1.
    rewrite apps_snoc. exact (T_App _ _ _ _ _ _ _ H1 Hx).
  Qed.

  Lemma case_type_typed : signature_typed S sg -> forall G D s P x d ps us s',
    sig_ind sg D = Some d -> length ps = length (ind_params d) -> length us = length (ind_indices d) ->
    typed G x (apps (Const (Ind D)) (ps ++ us)) -> typed G P (case_motive_type d ps s) ->
    typed G (apps (Const (Ind D)) (ps ++ us)) (Srt s') ->
    typed G (apps P (us ++ [x])) (Srt s).
  Proof. intros Hsig. exact (case_type_typed_t (proj1 Hsig)). Qed.

  Theorem validity_t : sig_types_typed S sg -> forall G t T, typed G t T ->
    (exists s, T = Srt s) \/ (exists s, typed G T (Srt s)).
  Proof.
    intros Hsig G t T H.
    induction H as
      [ G s s' HG Hax
      | G n A HG Hl
      | G A B s1 s2 s3 HA IHA HB IHB Hr
      | G A B b s Hb IHb HP IHP
      | G f u A B Hf IHf Hu IHu
      | G t A s HA IHA Ht IHt
      | G t A B s Ht IHt HB IHB Hc
      | G s0 HG Hp
      | G C e s HC IHC He IHe
      | G s0 HG Hp
      | G s0 HG Hp
      | G C c u s HC IHC Hc IHc Hu IHu
      | G s0 HG Hp
      | G s0 HG Hp
      | G s0 HG Hp
      | G C t f b s HC IHC Ht IHt Hf IHf Hb IHb
      | G A B s1 s2 s3 HA IHA HB IHB Hr
      | G A B a b s HS IHS Ha IHa Hb IHb
      | G p A B Hp IHp
      | G p A B Hp IHp
      | G g A HG Hd Hg
      | G D s P x bs d ps us Hd Hind Hel Hlp Hlu Hx IHx HP IHP Hbs
      | G A k b s D HA IHA Hsa Hne Hb IHb Hg ].
    - left. eexists. reflexivity.
    - right. exact (wf_lookup _ _ _ HG Hl).
    - left. eexists. reflexivity.
    - right. exists s. exact HP.
    - right. destruct IHf as [[s E] | [s HPi]]; [discriminate E | ].
      destruct (inv_pi _ _ _ _ HPi) as (s1 & s2 & s3 & _ & HB & _ & _).
      exists s2. exact (typing_subst1 S sg _ _ _ _ _ Hu HB).
    - right. exists s. exact HA.
    - right. exists s. exact HB.
    - left. eexists. reflexivity.
    - right. exists s. exact (T_App _ _ _ _ _ _ _ HC He).
    - left. eexists. reflexivity.
    - right. exists s0. apply T_Unit; assumption.
    - right. exists s. exact (T_App _ _ _ _ _ _ _ HC Hu).
    - left. eexists. reflexivity.
    - right. exists s0. apply T_Bool; assumption.
    - right. exists s0. apply T_Bool; assumption.
    - right. exists s. exact (T_App _ _ _ _ _ _ _ HC Hb).
    - left. eexists. reflexivity.
    - right. exists s. exact HS.
    - right. destruct IHp as [[s E] | [s HS]]; [discriminate E | ].
      destruct (inv_sigma _ _ _ _ HS) as (s1 & s2 & s3 & HA & _ & _ & _). exists s1. exact HA.
    - right. destruct IHp as [[s E] | [s HS]]; [discriminate E | ].
      destruct (inv_sigma _ _ _ _ HS) as (s1 & s2 & s3 & _ & HB & _ & _).
      exists s2. exact (typing_subst1 S sg _ _ _ _ _ (T_Fst _ _ _ _ _ _ Hp) HB).
    - right. exact (const_type_typed_t Hsig _ _ _ HG Hg).
    - right. destruct IHx as [[s' E] | [s' HX]]; [exfalso; exact (apps_const_not_srt _ _ _ E) | ].
      exists s. exact (case_type_typed_t Hsig _ _ _ _ _ _ _ _ _ Hind Hlp Hlu Hx HP HX).
    - right. exists s. exact HA.
  Qed.

  Theorem validity : signature_typed S sg -> forall G t T, typed G t T ->
    (exists s, T = Srt s) \/ (exists s, typed G T (Srt s)).
  Proof. intros Hsig. exact (validity_t (proj1 Hsig)). Qed.

  (** A type that is not a sort. *)
  Corollary validity_type_t : sig_types_typed S sg -> forall G t T, typed G t T ->
    (forall s, T <> Srt s) -> exists s, typed G T (Srt s).
  Proof.
    intros Hsig G t T H HT. destruct (validity_t Hsig _ _ _ H) as [[s E] | H']; [ | exact H'].
    exfalso. exact (HT s E).
  Qed.

  Corollary validity_type : signature_typed S sg -> forall G t T, typed G t T ->
    (forall s, T <> Srt s) -> exists s, typed G T (Srt s).
  Proof. intros Hsig. exact (validity_type_t (proj1 Hsig)). Qed.

  (** A sort that types a term is a sort of the system. *)
  Lemma typed_srt_spec : sig_types_typed S sg -> forall G t s, typed G t (Srt s) -> spec_sort S s = true.
  Proof.
    intros Hsig G t s H. remember (Srt s) as T eqn:ET. revert s ET.
    induction H; intros sx ET; subst; try discriminate ET.
    all: try (injection ET as <-).
    all: try solve [ exact (proj2 (spec_axiom_sorts S _ _ ltac:(eassumption)))
                   | exact (proj2 (proj2 (spec_rule_sorts S _ _ _ ltac:(eassumption))))
                   | exact (proj2 (proj2 (spec_sigma_sorts S _ _ _ ltac:(eassumption))))
                   | exact (spec_prim_sort S _ ltac:(eassumption))
                   | exact (typed_sort_in_spec _ _ _ _ _ ltac:(eassumption)) ].
    - (* a variable *)
      destruct (wf_lookup _ _ _ H H0) as [s1 Hs1]. exact (typed_sort_in_spec _ _ _ _ _ Hs1).
    - (* an application *)
      destruct (subst1_srt_inv _ _ _ ET) as [-> | [-> ->]].
      + destruct (validity_type_t Hsig _ _ _ H (fun s E => ltac:(discriminate E))) as [s1 HPi].
        destruct (inv_pi _ _ _ _ HPi) as (s2 & s3 & s4 & _ & HB & _ & _).
        exact (typed_sort_in_spec _ _ _ _ _ HB).
      + exact (typed_sort_in_spec _ _ _ _ _ H0).
    - (* the first projection *)
      destruct (validity_type_t Hsig _ _ _ H (fun s E => ltac:(discriminate E))) as [s1 HS].
      destruct (inv_sigma _ _ _ _ HS) as (s2 & s3 & s4 & HA & _ & _ & _).
      exact (typed_sort_in_spec _ _ _ _ _ HA).
    - (* the second projection *)
      destruct (subst1_srt_inv _ _ _ ET) as [-> | [_ E]]; [ | discriminate E].
      destruct (validity_type_t Hsig _ _ _ H (fun s E => ltac:(discriminate E))) as [s1 HS].
      destruct (inv_sigma _ _ _ _ HS) as (s2 & s3 & s4 & _ & HB & _ & _).
      exact (typed_sort_in_spec _ _ _ _ _ HB).
    - (* a constant *)
      destruct (Hsig _ _ H1) as [s1 Hs1]. exact (typed_sort_in_spec _ _ _ _ _ Hs1).
    - (* a match *)
      exfalso. rewrite apps_snoc in ET. discriminate ET.
  Qed.
End Inversion.
