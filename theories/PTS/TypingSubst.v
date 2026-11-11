(** * Weakening and substitution for the declarative rules

    The typing half of the correctness of substitution, whose syntactic
    half is PTS.SubstLaws: a judgment of PTS.Typing survives a renaming
    of its context that keeps the types of the variables
    ([typing_rename]), and a substitution of terms of the right types for
    its variables ([typing_subst]).  Weakening by a well-sorted type and
    the substitution lemma for one variable are the instances stated in
    PTS.Contracts.

    Besides the substitution laws, the rules need three invariants of a
    signature and of the guard, proved below the typing rules:
    - the type of a constant is closed ([sig_type_closed] of
      PTS.Signature), so that [T_Const] gives it in every context;
    - the types of the motive and of the branches of a [match] are built
      from a closed description and the parameters, so that substituting
      in them substitutes in the parameters and the motive
      ([subst_case_motive_type], [subst_case_branch_type] of
      PTS.SubstLaws);
    - the guard of a [fix] marks the variables of the body, and every
      variable of the enclosing context gets [Large]: a substitution for
      them gives terms that cannot mention the function, so the body
      stays guarded ([fix_guarded_subst] of PTS.GuardSubst).  The
      structural argument, an unfolding to a Π whose domain unfolds to a
      family, survives too ([struct_arg_subst] of PTS.SubstLaws).

    The renaming lemma comes first: substituting under a binder lifts the
    substituted terms, which is weakening. *)

From Stdlib Require Import List Arith Lia Bool.
From Stdlib Require String.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Telescope Spec Signature Reduction SubstLaws Guard GuardSubst Typing.
(* TODO(erasure-cic): remove this export once theories/Erasure/
   RelationSubst.v of erasure-cic imports PTS.GuardSubst.  The guard under
   substitution ([fix_guarded_subst], [fix_guarded_rename], [below]) was
   proved here; it is re-exported for the files that use it from this
   module. *)
From DepTypes.PTS Require Export GuardSubst.

Section TypingSubst.
  Variable S : spec.
  Variable sg : signature.
  Local Notation typed := (has_type S sg).
  Local Notation wf := (wf_ctx S sg).
  Local Notation branches := (has_branches S sg).

  (** Every judgment has a well-formed context. *)
  Lemma typed_wf_all :
    (forall G, wf G -> True) /\
    (forall G t A, typed G t A -> wf G) /\
    (forall G d ps P cs bs, branches G d ps P cs bs -> True).
  Proof. apply typing_mutind; intros; try exact I; assumption. Qed.

  Lemma typed_wf : forall G t A, typed G t A -> wf G.
  Proof. exact (proj1 (proj2 typed_wf_all)). Qed.

  (** The domain of a typed Π is a type. *)
  Lemma pi_dom_typed : forall G A B T, typed G (Pi A B) T -> exists s, typed G A (Srt s).
  Proof.
    intros G A B T H. remember (Pi A B) as t eqn:Et.
    induction H; try discriminate Et; [injection Et as -> -> | ]; eauto.
  Qed.

  (** *** Renaming *)

  (** [r] sends the context [G] into [G']: every variable to one of the
      renamed type. *)
  Definition ren_ok (G G' : ctx) (r : nat -> nat) : Prop :=
    forall n A, lookup G n = Some A -> lookup G' (r n) = Some (rename r A).

  Lemma ren_ok_up : forall G G' r A, ren_ok G G' r -> ren_ok (A :: G) (rename r A :: G') (up_ren r).
  Proof.
    intros G G' r A H [|n] B HB.
    - rewrite lookup_cons_0 in HB. injection HB as <-. cbn [up_ren].
      rewrite lookup_cons_0, rename_up_lift1. reflexivity.
    - rewrite lookup_cons_S in HB. destruct (lookup G n) as [B'|] eqn:E; [ | discriminate HB].
      injection HB as <-. cbn [up_ren]. rewrite lookup_cons_S, (H n B' E). cbn [option_map].
      rewrite rename_up_lift1. reflexivity.
  Qed.

  Theorem typing_rename :
    (forall G, wf G -> True) /\
    (forall G t A, typed G t A -> forall G' r, wf G' -> ren_ok G G' r ->
       typed G' (rename r t) (rename r A)) /\
    (forall G d ps P cs bs, branches G d ps P cs bs -> forall G' r, wf G' -> ren_ok G G' r ->
       length ps = length (ind_params d) -> forallb (ctor_closed (length (ind_params d))) cs = true ->
       branches G' d (map (rename r) ps) (rename r P) cs (map (rename r) bs)).
  Proof.
    apply typing_mutind.
    (* contexts *)
    - exact I.
    - intros; exact I.
    (* sorts, variables *)
    - intros G s s' _ _ Hax G' r HG Hr. cbn [rename]. apply T_Sort; assumption.
    - intros G n A _ _ Hl G' r HG Hr. cbn [rename]. apply T_Var; [exact HG | exact (Hr n A Hl)].
    (* Π, λ, application, annotation, conversion *)
    - intros G A B s1 s2 s3 _ IHA _ IHB Hrule G' r HG Hr. cbn [rename].
      pose proof (IHA G' r HG Hr) as HA. cbn [rename] in HA.
      eapply T_Pi; [exact HA | | exact Hrule].
      exact (IHB _ _ (W_Cons _ _ _ _ _ HA) (ren_ok_up _ _ _ _ Hr)).
    - intros G A B b s _ IHb _ IHP G' r HG Hr. cbn [rename].
      pose proof (IHP G' r HG Hr) as HP. cbn [rename] in HP.
      destruct (pi_dom_typed _ _ _ _ HP) as [s1 HA].
      eapply T_Lam; [ | exact HP]. exact (IHb _ _ (W_Cons _ _ _ _ _ HA) (ren_ok_up _ _ _ _ Hr)).
    - intros G f u A B _ IHf _ IHu G' r HG Hr. rewrite rename_subst1. cbn [rename].
      pose proof (IHf G' r HG Hr) as Hf. cbn [rename] in Hf.
      exact (T_App _ _ _ _ _ _ _ Hf (IHu G' r HG Hr)).
    - intros G t A s _ IHA _ IHt G' r HG Hr. cbn [rename].
      eapply T_Ann; [exact (IHA G' r HG Hr) | exact (IHt G' r HG Hr)].
    - intros G t A B s _ IHt _ IHB Hc G' r HG Hr.
      eapply T_Conv; [exact (IHt G' r HG Hr) | exact (IHB G' r HG Hr) | exact (conv_rename r _ _ Hc)].
    (* the primitives *)
    - intros G s0 _ _ Hp G' r HG Hr. eapply T_Void; eassumption.
    - intros G C e s _ IHC _ IHe G' r HG Hr. cbn [rename].
      eapply T_ElimVoid; [exact (IHC G' r HG Hr) | exact (IHe G' r HG Hr)].
    - intros G s0 _ _ Hp G' r HG Hr. eapply T_Unit; eassumption.
    - intros G s0 _ _ Hp G' r HG Hr. eapply T_Tt; eassumption.
    - intros G C c u s _ IHC _ IHc _ IHu G' r HG Hr. cbn [rename].
      eapply T_ElimUnit; [exact (IHC G' r HG Hr) | exact (IHc G' r HG Hr) | exact (IHu G' r HG Hr)].
    - intros G s0 _ _ Hp G' r HG Hr. eapply T_Bool; eassumption.
    - intros G s0 _ _ Hp G' r HG Hr. eapply T_True; eassumption.
    - intros G s0 _ _ Hp G' r HG Hr. eapply T_False; eassumption.
    - intros G C t f b s _ IHC _ IHt _ IHf _ IHb G' r HG Hr. cbn [rename].
      eapply T_ElimBool;
        [exact (IHC G' r HG Hr) | exact (IHt G' r HG Hr) | exact (IHf G' r HG Hr) | exact (IHb G' r HG Hr)].
    (* Σ *)
    - intros G A B s1 s2 s3 _ IHA _ IHB Hrule G' r HG Hr. cbn [rename].
      pose proof (IHA G' r HG Hr) as HA. cbn [rename] in HA.
      eapply T_Sigma; [exact HA | | exact Hrule].
      exact (IHB _ _ (W_Cons _ _ _ _ _ HA) (ren_ok_up _ _ _ _ Hr)).
    - intros G A B a b s _ IHS _ IHa _ IHb G' r HG Hr. cbn [rename].
      pose proof (IHb G' r HG Hr) as Hb. rewrite rename_subst1 in Hb.
      eapply T_Pair; [exact (IHS G' r HG Hr) | exact (IHa G' r HG Hr) | exact Hb].
    - intros G p A B _ IHp G' r HG Hr. cbn [rename]. eapply T_Fst. exact (IHp G' r HG Hr).
    - intros G p A B _ IHp G' r HG Hr. rewrite rename_subst1. cbn [rename].
      eapply T_Snd. exact (IHp G' r HG Hr).
    (* constants: their types are closed *)
    - intros G g A _ _ Hd Hty G' r HG Hr. cbn [rename].
      rewrite (rename_closed r A (sig_type_closed _ _ _ Hty)). apply T_Const; assumption.
    (* match *)
    - intros G D s P x bs d ps us Hdecls Hind Hel Hlp Hlu _ IHx _ IHP _ IHbs G' r HG Hr.
      destruct (sig_ind_closed _ _ _ Hind) as [Hi Hcs].
      rewrite rename_apps, map_app. cbn [map rename].
      pose proof (IHx G' r HG Hr) as Hx. rewrite rename_apps, map_app in Hx. cbn [rename] in Hx.
      pose proof (IHP G' r HG Hr) as HP. rewrite rename_case_motive_type in HP by (rewrite Hlp; exact Hi).
      apply (T_Case _ _ G' D s (rename r P) (rename r x) (map (rename r) bs) d (map (rename r) ps)
               (map (rename r) us));
        [exact Hdecls | exact Hind | exact Hel | rewrite length_map; exact Hlp | rewrite length_map; exact Hlu
        | exact Hx | exact HP | exact (IHbs G' r HG Hr Hlp Hcs)].
    (* fix *)
    - intros G A k b s D _ IHA Hsa Hne _ IHb Hg G' r HG Hr. cbn [rename].
      pose proof (IHA G' r HG Hr) as HA. cbn [rename] in HA.
      pose proof (IHb _ _ (W_Cons _ _ _ _ _ HA) (ren_ok_up _ _ _ _ Hr)) as Hb. rewrite rename_up_lift1 in Hb.
      eapply T_Fix; [exact HA | exact (struct_arg_rename _ _ _ _ r Hsa) | exact Hne | exact Hb
                    | exact (fix_guarded_rename _ _ _ r Hg)].
    (* the branches *)
    - intros G d ps P G' r HG Hr Hl Hc. constructor.
    - intros G d ps P c cs b bs _ IHb _ IHbs G' r HG Hr Hl Hc.
      cbn [forallb] in Hc. apply andb_prop in Hc as [Hc1 Hc2]. cbn [map].
      constructor; [ | exact (IHbs G' r HG Hr Hl Hc2)].
      pose proof (IHb G' r HG Hr) as Hb. rewrite rename_case_branch_type in Hb by assumption. exact Hb.
  Qed.

  (** Weakening by one well-sorted type. *)
  Corollary typing_weaken1 : forall G t A B s, typed G t A -> typed G B (Srt s) ->
    typed (B :: G) (lift 1 t) (lift 1 A).
  Proof.
    intros G t A B s Ht HB. apply (proj1 (proj2 typing_rename) G t A Ht (B :: G) (Nat.add 1)).
    - exact (W_Cons _ _ _ _ _ HB).
    - intros n A' HA'. change (Nat.add 1 n) with (Datatypes.S n). rewrite lookup_cons_S, HA'. reflexivity.
  Qed.

  (** *** Substitution *)

  (** [sb] sends the context [G] into [G']: every variable to a term of
      the substituted type. *)
  Definition sub_ok (G G' : ctx) (sb : nat -> term) : Prop :=
    forall n A, lookup G n = Some A -> typed G' (sb n) (subst sb A).

  Lemma sub_ok_up : forall G G' sb A s, sub_ok G G' sb -> typed G' (subst sb A) (Srt s) ->
    sub_ok (A :: G) (subst sb A :: G') (up_sub sb).
  Proof.
    intros G G' sb A s H HA [|n] B HB.
    - rewrite lookup_cons_0 in HB. injection HB as <-. rewrite subst_up_lift1. cbn [up_sub].
      apply T_Var; [exact (W_Cons _ _ _ _ _ HA) | apply lookup_cons_0].
    - rewrite lookup_cons_S in HB. destruct (lookup G n) as [B'|] eqn:E; [ | discriminate HB].
      injection HB as <-. rewrite subst_up_lift1. cbn [up_sub].
      exact (typing_weaken1 _ _ _ _ _ (H n B' E) HA).
  Qed.

  Theorem typing_subst :
    (forall G, wf G -> True) /\
    (forall G t A, typed G t A -> forall G' sb, wf G' -> sub_ok G G' sb ->
       typed G' (subst sb t) (subst sb A)) /\
    (forall G d ps P cs bs, branches G d ps P cs bs -> forall G' sb, wf G' -> sub_ok G G' sb ->
       length ps = length (ind_params d) -> forallb (ctor_closed (length (ind_params d))) cs = true ->
       branches G' d (map (subst sb) ps) (subst sb P) cs (map (subst sb) bs)).
  Proof.
    apply typing_mutind.
    (* contexts *)
    - exact I.
    - intros; exact I.
    (* sorts, variables *)
    - intros G s s' _ _ Hax G' sb HG Hs. cbn [subst]. apply T_Sort; assumption.
    - intros G n A _ _ Hl G' sb HG Hs. cbn [subst]. exact (Hs n A Hl).
    (* Π, λ, application, annotation, conversion *)
    - intros G A B s1 s2 s3 _ IHA _ IHB Hrule G' sb HG Hs. cbn [subst].
      pose proof (IHA G' sb HG Hs) as HA. cbn [subst] in HA.
      eapply T_Pi; [exact HA | | exact Hrule].
      exact (IHB _ _ (W_Cons _ _ _ _ _ HA) (sub_ok_up _ _ _ _ _ Hs HA)).
    - intros G A B b s _ IHb _ IHP G' sb HG Hs. cbn [subst].
      pose proof (IHP G' sb HG Hs) as HP. cbn [subst] in HP.
      destruct (pi_dom_typed _ _ _ _ HP) as [s1 HA].
      eapply T_Lam; [ | exact HP]. exact (IHb _ _ (W_Cons _ _ _ _ _ HA) (sub_ok_up _ _ _ _ _ Hs HA)).
    - intros G f u A B _ IHf _ IHu G' sb HG Hs. rewrite subst_subst1. cbn [subst].
      pose proof (IHf G' sb HG Hs) as Hf. cbn [subst] in Hf.
      exact (T_App _ _ _ _ _ _ _ Hf (IHu G' sb HG Hs)).
    - intros G t A s _ IHA _ IHt G' sb HG Hs. cbn [subst].
      eapply T_Ann; [exact (IHA G' sb HG Hs) | exact (IHt G' sb HG Hs)].
    - intros G t A B s _ IHt _ IHB Hc G' sb HG Hs.
      eapply T_Conv; [exact (IHt G' sb HG Hs) | exact (IHB G' sb HG Hs) | exact (conv_subst sb _ _ Hc)].
    (* the primitives *)
    - intros G s0 _ _ Hp G' sb HG Hs. eapply T_Void; eassumption.
    - intros G C e s _ IHC _ IHe G' sb HG Hs. cbn [subst].
      eapply T_ElimVoid; [exact (IHC G' sb HG Hs) | exact (IHe G' sb HG Hs)].
    - intros G s0 _ _ Hp G' sb HG Hs. eapply T_Unit; eassumption.
    - intros G s0 _ _ Hp G' sb HG Hs. eapply T_Tt; eassumption.
    - intros G C c u s _ IHC _ IHc _ IHu G' sb HG Hs. cbn [subst].
      eapply T_ElimUnit; [exact (IHC G' sb HG Hs) | exact (IHc G' sb HG Hs) | exact (IHu G' sb HG Hs)].
    - intros G s0 _ _ Hp G' sb HG Hs. eapply T_Bool; eassumption.
    - intros G s0 _ _ Hp G' sb HG Hs. eapply T_True; eassumption.
    - intros G s0 _ _ Hp G' sb HG Hs. eapply T_False; eassumption.
    - intros G C t f b s _ IHC _ IHt _ IHf _ IHb G' sb HG Hs. cbn [subst].
      eapply T_ElimBool;
        [exact (IHC G' sb HG Hs) | exact (IHt G' sb HG Hs) | exact (IHf G' sb HG Hs) | exact (IHb G' sb HG Hs)].
    (* Σ *)
    - intros G A B s1 s2 s3 _ IHA _ IHB Hrule G' sb HG Hs. cbn [subst].
      pose proof (IHA G' sb HG Hs) as HA. cbn [subst] in HA.
      eapply T_Sigma; [exact HA | | exact Hrule].
      exact (IHB _ _ (W_Cons _ _ _ _ _ HA) (sub_ok_up _ _ _ _ _ Hs HA)).
    - intros G A B a b s _ IHS _ IHa _ IHb G' sb HG Hs. cbn [subst].
      pose proof (IHb G' sb HG Hs) as Hb. rewrite subst_subst1 in Hb.
      eapply T_Pair; [exact (IHS G' sb HG Hs) | exact (IHa G' sb HG Hs) | exact Hb].
    - intros G p A B _ IHp G' sb HG Hs. cbn [subst]. eapply T_Fst. exact (IHp G' sb HG Hs).
    - intros G p A B _ IHp G' sb HG Hs. rewrite subst_subst1. cbn [subst].
      eapply T_Snd. exact (IHp G' sb HG Hs).
    (* constants: their types are closed *)
    - intros G g A _ _ Hd Hty G' sb HG Hs. cbn [subst].
      rewrite (subst_closed sb A (sig_type_closed _ _ _ Hty)). apply T_Const; assumption.
    (* match *)
    - intros G D s P x bs d ps us Hdecls Hind Hel Hlp Hlu _ IHx _ IHP _ IHbs G' sb HG Hs.
      destruct (sig_ind_closed _ _ _ Hind) as [Hi Hcs].
      rewrite subst_apps, map_app. cbn [map subst].
      pose proof (IHx G' sb HG Hs) as Hx. rewrite subst_apps, map_app in Hx. cbn [subst] in Hx.
      pose proof (IHP G' sb HG Hs) as HP. rewrite subst_case_motive_type in HP by (rewrite Hlp; exact Hi).
      apply (T_Case _ _ G' D s (subst sb P) (subst sb x) (map (subst sb) bs) d (map (subst sb) ps)
               (map (subst sb) us));
        [exact Hdecls | exact Hind | exact Hel | rewrite length_map; exact Hlp | rewrite length_map; exact Hlu
        | exact Hx | exact HP | exact (IHbs G' sb HG Hs Hlp Hcs)].
    (* fix *)
    - intros G A k b s D _ IHA Hsa Hne _ IHb Hg G' sb HG Hs. cbn [subst].
      pose proof (IHA G' sb HG Hs) as HA. cbn [subst] in HA.
      pose proof (IHb _ _ (W_Cons _ _ _ _ _ HA) (sub_ok_up _ _ _ _ _ Hs HA)) as Hb.
      rewrite subst_up_lift1 in Hb.
      eapply T_Fix; [exact HA | exact (struct_arg_subst _ _ _ _ sb Hsa) | exact Hne | exact Hb
                    | exact (fix_guarded_subst _ _ _ sb Hg)].
    (* the branches *)
    - intros G d ps P G' sb HG Hs Hl Hc. constructor.
    - intros G d ps P c cs b bs _ IHb _ IHbs G' sb HG Hs Hl Hc.
      cbn [forallb] in Hc. apply andb_prop in Hc as [Hc1 Hc2]. cbn [map].
      constructor; [ | exact (IHbs G' sb HG Hs Hl Hc2)].
      pose proof (IHb G' sb HG Hs) as Hb. rewrite subst_case_branch_type in Hb by assumption. exact Hb.
  Qed.

  (** The substitution lemma for one variable. *)
  Corollary typing_subst1 : forall G u A t B, typed G u A -> typed (A :: G) t B ->
    typed G (subst1 t u) (subst1 B u).
  Proof.
    intros G u A t B Hu Ht. pose proof (typed_wf _ _ _ Hu) as HG.
    apply (proj1 (proj2 typing_subst) _ _ _ Ht G (scons u Var) HG).
    intros [|n] B' HB'.
    - rewrite lookup_cons_0 in HB'. injection HB' as <-.
      change (typed G u (subst1 (lift 1 A) u)). rewrite subst1_lift. exact Hu.
    - rewrite lookup_cons_S in HB'. destruct (lookup G n) as [B''|] eqn:E; [ | discriminate HB'].
      injection HB' as <-. change (typed G (Var n) (subst1 (lift 1 B'') u)). rewrite subst1_lift.
      apply T_Var; [exact HG | exact E].
  Qed.
End TypingSubst.
