(** * Renaming constants

    [cren r t] renames by [r] the constants of [t] and keeps the rest, the
    names of matches included.  The judgments of a signature [sg] carry
    over to a signature [sg'] where [r] sends the constants of [sg] to
    constants of the renamed types, bodies and rules:
    - reduction and conversion ([red_cren], [conv_cren]), for terms whose
      matches are on families [sg'] declares alike ([cases_in]); the
      ι of an instance needs the indices of its recursive fields fixed
      by [r] ([fields_ok]); the conditions on [r], [sg] and [sg'] are
      [cren_ok], and reduction keeps the constants and matches a term
      may have when the bodies and rules of [sg] have them only
      ([an_closed], [red_an]);
    - the structural arguments of [fix] and the guard
      ([struct_arg_cren], [guarded_cren]);
    - the declarative judgments ([typing_cren]), for every term;
    - the bidirectional judgments ([synth_cren]), for terms whose
      constants [r] may rename ([allnodes]) and whose [fix] are on
      families it keeps ([fixok]).
    [r] need not be injective, nor the identity on the constants it
    leaves out: a judgment is carried, not reflected.

    The use made of it (Checked/SigTyped.v of elim-inductive-types): the
    types of a declaration of D are checked in a signature that already
    has D, where the soundness of the checker needs these very types to
    be types.  Renamed, [Ind D] becomes an inactive instance of the same
    type in a signature without D, where the soundness applies, and the
    declarative judgment is renamed back. *)

From Stdlib Require Import List Arith Lia Bool Relations.
From Stdlib Require String.
Import ListNotations.
From DepTypes.Common Require Import Lists.
From DepTypes.PTS Require Import Syntax Telescope Spec Signature Reduction SubstLaws Typing
  Confluence Guard Inversion Bidir BidirSound Monotone.

Local Open Scope list_scope.

(** ** Renaming constants *)

Section Cren.
  Variable r : gref -> gref.

  Fixpoint cren (t : term) : term :=
    match t with
    | Srt s => Srt s
    | Var n => Var n
    | Pi A B => Pi (cren A) (cren B)
    | Lam b => Lam (cren b)
    | App f a => App (cren f) (cren a)
    | Ann u A => Ann (cren u) (cren A)
    | Void => Void
    | ElimVoid C e => ElimVoid (cren C) (cren e)
    | Unit => Unit
    | Tt => Tt
    | ElimUnit C c u => ElimUnit (cren C) (cren c) (cren u)
    | Bool => Bool
    | BTrue => BTrue
    | BFalse => BFalse
    | ElimBool C t f b => ElimBool (cren C) (cren t) (cren f) (cren b)
    | Sigma A B => Sigma (cren A) (cren B)
    | Pair a b => Pair (cren a) (cren b)
    | Fst p => Fst (cren p)
    | Snd p => Snd (cren p)
    | Const g => Const (r g)
    | Case D s P x bs => Case D s (cren P) (cren x) (map cren bs)
    | Fix A k b => Fix (cren A) k (cren b)
    end.

  Lemma cren_rename : forall t f, cren (rename f t) = rename f (cren t).
  Proof.
    intros t. induction t using term_ind'; intros fr; cbn [cren rename]; f_equal; auto.
    rewrite !map_map. induction IHl as [|b bs Hb _ IH]; [reflexivity | cbn [map]; f_equal; auto].
  Qed.

  Lemma cren_lift : forall n t, cren (lift n t) = lift n (cren t).
  Proof. intros n t. unfold lift. apply cren_rename. Qed.

  Lemma cren_subst : forall t sb, cren (subst sb t) = subst (fun n => cren (sb n)) (cren t).
  Proof.
    assert (Hup : forall sb n, cren (up_sub sb n) = up_sub (fun i => cren (sb i)) n).
    { intros sb [|n]; [reflexivity | cbn [up_sub]; apply cren_lift]. }
    intros t. induction t using term_ind'; intros sb; cbn [cren subst]; f_equal; auto;
      try (rewrite IHt2; apply subst_ext; exact (Hup sb));
      try (rewrite IHt; apply subst_ext; exact (Hup sb)).
    rewrite !map_map. induction IHl as [|b bs Hb _ IH]; [reflexivity | cbn [map]; f_equal; auto].
  Qed.

  Lemma cren_subst1 : forall b u, cren (subst1 b u) = subst1 (cren b) (cren u).
  Proof.
    intros b u. unfold subst1. rewrite cren_subst. apply subst_ext. intros [|n]; reflexivity.
  Qed.

  Lemma cren_apps : forall l h, cren (apps h l) = apps (cren h) (map cren l).
  Proof.
    induction l as [|a l IH]; intros h; [reflexivity | ].
    change (apps h (a :: l)) with (apps (App h a) l). rewrite IH. reflexivity.
  Qed.

  Lemma cren_lams : forall n b, cren (lams n b) = lams n (cren b).
  Proof. induction n as [|n IH]; intros b; [reflexivity | cbn [lams cren]; f_equal; apply IH]. Qed.

  Lemma cren_vars : forall base n, map cren (vars base n) = vars base n.
  Proof. intros base n. induction n as [|n IH]; [reflexivity | cbn [vars map cren]; f_equal; exact IH]. Qed.

  Lemma cren_pis : forall Ts R, cren (pis Ts R) = pis (map cren Ts) (cren R).
  Proof. induction Ts as [|T Ts IH]; intros R; [reflexivity | cbn [pis map cren]; f_equal; apply IH]. Qed.

  Lemma spine_head_cren : forall t, spine_head (cren t) = cren (spine_head t).
  Proof. induction t; try reflexivity. exact IHt1. Qed.

  Lemma spine_args_cren : forall t, spine_args (cren t) = map cren (spine_args t).
  Proof.
    induction t; try reflexivity. cbn [cren]. rewrite !spine_args_App, map_app, IHt1. reflexivity.
  Qed.

  Lemma cren_subst_tele : forall Ts sb, map cren (subst_tele sb Ts) = subst_tele (fun n => cren (sb n)) (map cren Ts).
  Proof.
    induction Ts as [|T Ts IH]; intros sb; [reflexivity | ]. cbn [subst_tele map].
    rewrite cren_subst, IH. f_equal. apply subst_tele_ext. intros [|n]; [reflexivity | cbn [up_sub]; apply cren_lift].
  Qed.

  (** Terms whose constants the renaming keeps. *)
  Definition fixed (t : term) : Prop := cren t = t.

  Lemma hyp_cren : forall D s pre env Bs vs a, r (Elim D s) = Elim D s -> Forall fixed vs ->
    cren (hyp D s pre env Bs vs a) = hyp D s (map cren pre) (map cren env) Bs vs (cren a).
  Proof.
    intros D s pre env Bs vs a Hr Hvs. unfold hyp. rewrite cren_lams, cren_apps. cbn [cren]. rewrite Hr.
    f_equal. f_equal. rewrite !map_app. f_equal; [ | f_equal].
    - rewrite !map_map. apply map_ext. intros t. apply cren_lift.
    - rewrite map_map. induction Hvs as [|v vs Hv _ IH]; [reflexivity | ]. cbn [map]. f_equal; [ | exact IH].
      rewrite cren_subst, Hv. apply subst_ext. intros n. unfold inst.
      destruct (Nat.ltb n (length Bs)); [reflexivity | ]. rewrite cren_lift. f_equal.
      symmetry. exact (map_nth cren env (Var 0) _).
    - cbn [map]. f_equal. rewrite cren_apps, cren_lift, cren_vars. reflexivity.
  Qed.
End Cren.

(** ** Renaming commutes with reduction *)

Definition fields_ok (r : gref -> gref) (cok : String.string -> bool) (d : ind_desc) : Prop :=
  forall c, In c (ind_ctors d) -> forall Bs vs, In (FRec Bs vs) (ctor_fields c) ->
    Forall (fun v => fixed r v /\ cases_in cok v = true) vs.

(** The conditions under which [cren r] carries the reduction of [sg] to
    [sg'] for terms whose matches are on families [cok] accepts: [r]
    keeps constructors, sends a δ-constant to one with the renamed body,
    keeps every active instance with its family and the indices of its
    recursive fields ([fields_ok]), and [sg'] declares alike the families
    [cok] accepts. *)
Record cren_ok (r : gref -> gref) (sg sg' : signature) (cok : String.string -> bool) : Prop := {
  ok_ctor : forall D c, r (Ctor D c) = Ctor D c;
  ok_delta : forall g b, sig_delta sg g = Some b ->
    sig_delta sg' (r g) = Some (cren r b) /\ cases_in cok b = true;
  ok_elim : forall D s A d, sig_elim sg D s = Some (A, true) -> sig_ind sg D = Some d ->
    r (Elim D s) = Elim D s /\ sig_elim sg' D s = Some (A, true) /\ sig_ind sg' D = Some d /\ fields_ok r cok d;
  ok_case : forall D d, sig_ind sg D = Some d -> cok D = true -> sig_ind sg' D = Some d
}.
Arguments ok_ctor {r sg sg' cok}.
Arguments ok_delta {r sg sg' cok}.
Arguments ok_elim {r sg sg' cok}.
Arguments ok_case {r sg sg' cok}.

Section Red.
  Variable r : gref -> gref.
  Variables sg sg' : signature.
  Variable cok : String.string -> bool.
  Hypothesis HR : cren_ok r sg sg' cok.

  Local Notation cr := (cren r).

  Lemma ctor_view_cren : forall D d x i cd xs, ctor_view D d x = Some (i, cd, xs) ->
    ctor_view D d (cr x) = Some (i, cd, map cr xs).
  Proof.
    intros D d x i cd xs H. unfold ctor_view in *. cbv zeta in *.
    rewrite spine_head_cren, spine_args_cren, length_map.
    destruct (spine_head x) eqn:Eh; try discriminate H. destruct g as [ | D' c | | ]; try discriminate H.
    cbn [cren]. rewrite (ok_ctor HR).
    destruct (String.eqb D' D); [ | discriminate H].
    destruct (find_ctor (ind_ctors d) c) as [[i' cd']|]; [ | discriminate H].
    destruct (Nat.eqb _ _); [ | discriminate H].
    injection H as <- <- <-. rewrite skipn_map. reflexivity.
  Qed.

  Lemma iota_args_cren : forall D s fs pre env xs, r (Elim D s) = Elim D s ->
    Forall (fun fd => match fd with FRec _ vs => Forall (fixed r) vs | FArg _ => True end) fs ->
    map cr (iota_args D s pre env fs xs) = iota_args D s (map cr pre) (map cr env) fs (map cr xs).
  Proof.
    intros D s fs. induction fs as [|fd fs IH]; intros pre env xs Hr Hfs; [reflexivity | ].
    destruct xs as [|a xs]; [destruct fd; reflexivity | ].
    inversion Hfs as [|? ? Hfd Hfs']; subst.
    destruct fd as [A | Bs vs]; cbn [iota_args map].
    - f_equal. exact (IH _ (a :: env) _ Hr Hfs').
    - f_equal. f_equal; [exact (hyp_cren r D s pre env Bs vs a Hr Hfd) | exact (IH _ (a :: env) _ Hr Hfs')].
  Qed.

  Lemma iota_cren : forall t u, iota sg t = Some u -> iota sg' (cr t) = Some (cr u).
  Proof.
    intros t u H. unfold iota, iota_at in *.
    destruct (elim_view sg t) as [[[D s] d]|] eqn:Ev; [ | discriminate H].
    pose proof Ev as Ev'. unfold elim_view, elim_head in Ev'.
    destruct (spine_head t) eqn:Eh; try discriminate Ev'. destruct g as [ | | D' s' | ]; try discriminate Ev'.
    destruct (sig_elim sg D' s') as [[A [|]]|] eqn:Ee; try discriminate Ev'.
    destruct (sig_ind sg D') as [d'|] eqn:Ed; try discriminate Ev'.
    destruct (Nat.eqb (length (spine_args t)) (elim_arity d')) eqn:El; [ | discriminate Ev'].
    injection Ev' as -> -> ->.
    destruct (ok_elim HR _ _ _ _ Ee Ed) as (Hr & Ee' & Ed' & Hf).
    assert (Ev2 : elim_view sg' (cr t) = Some (D, s, d)).
    { unfold elim_view, elim_head. rewrite spine_head_cren, Eh. cbn [cren]. rewrite Hr, Ee', Ed'.
      rewrite spine_args_cren, length_map, El. reflexivity. }
    rewrite Ev2, spine_args_cren.
    apply Nat.eqb_eq in El.
    assert (Hne : spine_args t <> []) by (intros E; rewrite E in El; unfold elim_arity in El; cbn in El; lia).
    rewrite (last_map_nonempty _ _ (Var 0) _ Hne).
    destruct (ctor_view D d (last (spine_args t) (Var 0))) as [[[i cd] xs]|] eqn:Ecv; [ | discriminate H].
    rewrite (ctor_view_cren _ _ _ _ _ _ Ecv).
    rewrite skipn_map, firstn_map, nth_error_map.
    destruct (nth_error _ i) as [m|]; [ | discriminate H].
    injection H as <-. cbn [option_map]. f_equal.
    rewrite cren_apps, firstn_map, firstn_map, !rev'_rev, <- map_rev. f_equal.
    symmetry. apply iota_args_cren; [exact Hr | ].
    destruct (ctor_view_spec _ _ _ _ _ _ Ecv) as (c & ps & _ & Ec & _ & _).
    pose proof (find_ctor_nth_error _ _ _ _ Ec) as Ecd.
    apply Forall_forall. intros [A0 | Bs vs] Hin; [exact I | ].
    pose proof (Hf cd (nth_error_In _ _ Ecd) Bs vs Hin) as Hvs.
    rewrite Forall_forall in Hvs |- *. intros v Hv. exact (proj1 (Hvs v Hv)).
  Qed.

  Lemma fix_unfold_cren : forall t u, fix_unfold t = Some u -> fix_unfold (cr t) = Some (cr u).
  Proof.
    intros t u H. unfold fix_unfold, fix_at in *.
    destruct (fix_view t) as [[[A k] b]|] eqn:Ev; [ | discriminate H].
    destruct (fix_view_spec _ _ _ _ Ev) as [Eh Hl].
    assert (Ev' : fix_view (cr t) = Some (cr A, k, cr b)).
    { unfold fix_view. rewrite spine_head_cren, Eh. cbn [cren]. rewrite spine_args_cren, length_map, Hl, Nat.eqb_refl.
      reflexivity. }
    rewrite Ev', spine_args_cren.
    assert (Hne : spine_args t <> []) by (intros E; rewrite E in Hl; discriminate Hl).
    rewrite (last_map_nonempty _ _ (Var 0) _ Hne), spine_head_cren.
    destruct (spine_head (last (spine_args t) (Var 0))) eqn:Ex; try discriminate H.
    destruct g as [ | D c | | ]; try discriminate H.
    cbn [cren]. rewrite (ok_ctor HR). injection H as <-.
    rewrite cren_apps, cren_subst1. reflexivity.
  Qed.

  Lemma spine_iota_cren : forall t u, spine_iota sg t = Some u -> spine_iota sg' (cr t) = Some (cr u).
  Proof.
    intros t u H. unfold spine_iota in *.
    destruct (iota sg t) as [v|] eqn:E.
    - injection H as <-. rewrite (iota_cren _ _ E). reflexivity.
    - pose proof (fix_unfold_cren _ _ H) as H'. rewrite (fix_unfold_iota sg' _ _ H'). exact H'.
  Qed.

  Lemma case_iota_cren : forall t u, case_iota sg t = Some u -> cases_in cok t = true ->
    case_iota sg' (cr t) = Some (cr u).
  Proof.
    intros t u H Hc. destruct (case_iota_case _ _ _ H) as (D & s & P & x & bs & ->).
    unfold case_iota in *. cbn [cases_in] in Hc. apply andb_prop in Hc as [Hc _].
    apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _].
    destruct (sig_ind sg D) as [d|] eqn:Ed; [ | discriminate H]. cbn [cren].
    rewrite (ok_case HR _ _ Ed Hc).
    destruct (ctor_view D d x) as [[[i cd] xs]|] eqn:Ecv; [ | discriminate H].
    rewrite (ctor_view_cren _ _ _ _ _ _ Ecv), nth_error_map.
    destruct (nth_error bs i) as [b|]; [ | discriminate H].
    injection H as <-. cbn [option_map]. rewrite cren_apps. reflexivity.
  Qed.
End Red.

(** ** Reduction keeps the allowed constants and matches *)

Lemma last_in : forall (l : list term) d, l <> [] -> In (last l d) l.
Proof.
  intros l d H. destruct (exists_last H) as (l' & a & ->). rewrite last_last.
  apply in_or_app. right. left. reflexivity.
Qed.

(** The δ-bodies of [sg] and the indices of the recursive fields of its
    active instances satisfy [allnodes pc pk], and its active instances
    [pc]: reduction then keeps [allnodes pc pk] ([red_an]). *)
Record an_closed (pc : gref -> bool) (pk : String.string -> bool) (sg : signature) : Prop := {
  cl_delta : forall g b, sig_delta sg g = Some b -> allnodes pc pk b = true;
  cl_elim : forall D s A d, sig_elim sg D s = Some (A, true) -> sig_ind sg D = Some d ->
    pc (Elim D s) = true /\
    (forall c, In c (ind_ctors d) -> forall Bs vs, In (FRec Bs vs) (ctor_fields c) -> forallb (allnodes pc pk) vs = true)
}.
Arguments cl_delta {pc pk sg}.
Arguments cl_elim {pc pk sg}.

Section Closure.
  Variable pc : gref -> bool.
  Variable pk : String.string -> bool.
  Variable sg : signature.
  Local Notation an := (allnodes pc pk).
  Hypothesis Hcl : an_closed pc pk sg.

  Lemma an_iota_args : forall D s fs pre env xs, pc (Elim D s) = true ->
    forallb an pre = true -> forallb an env = true -> forallb an xs = true ->
    (forall Bs vs, In (FRec Bs vs) fs -> forallb an vs = true) ->
    forallb an (iota_args D s pre env fs xs) = true.
  Proof.
    intros D s fs. induction fs as [|fd fs IH]; intros pre env xs Hpc Hpre Henv Hxs Hfs; [reflexivity | ].
    destruct xs as [|a xs]; [destruct fd; reflexivity | ]. cbn [forallb] in Hxs. apply andb_prop in Hxs as [Ha Hxs].
    destruct fd as [A | Bs vs]; cbn [iota_args forallb].
    - rewrite Ha. cbn [andb]. apply IH; [exact Hpc | exact Hpre | cbn [forallb]; rewrite Ha; exact Henv | exact Hxs | ].
      intros Bs vs H. apply (Hfs Bs vs). right. exact H.
    - rewrite Ha. cbn [andb]. apply andb_true_intro. split.
      + unfold hyp. rewrite an_lams, an_apps. cbn [allnodes]. rewrite Hpc. cbn [andb].
        rewrite !forallb_app. apply andb_true_intro; split; [ | apply andb_true_intro; split].
        * rewrite forallb_forall in *. intros t Ht. apply in_map_iff in Ht as (t0 & <- & Ht0). rewrite an_lift. auto.
        * pose proof (Hfs Bs vs (or_introl eq_refl)) as Hvs. rewrite forallb_forall in *.
          intros t Ht. apply in_map_iff in Ht as (v & <- & Hv). apply an_subst; [auto | ].
          intros n. unfold inst. destruct (Nat.ltb n (length Bs)); [reflexivity | ]. rewrite an_lift.
          destruct (nth_error env (n - length Bs)) as [e|] eqn:Ee.
          -- rewrite (nth_error_nth _ _ _ Ee). apply Henv. exact (nth_error_In _ _ Ee).
          -- rewrite nth_overflow by (apply nth_error_None; exact Ee). reflexivity.
        * cbn [forallb]. rewrite an_apps, an_lift, Ha, an_vars. reflexivity.
      + apply IH; [exact Hpc | exact Hpre | cbn [forallb]; rewrite Ha; exact Henv | exact Hxs | ].
        intros Bs' vs' H. apply (Hfs Bs' vs'). right. exact H.
  Qed.

  Lemma an_spine_iota : forall t u, spine_iota sg t = Some u -> an t = true -> an u = true.
  Proof.
    intros t u H Ht. destruct (an_spine _ _ _ Ht) as [Hh Ha].
    unfold spine_iota in H. destruct (iota sg t) as [v|] eqn:Ei.
    - injection H as <-. unfold iota, iota_at in Ei.
      destruct (elim_view sg t) as [[[D s] d]|] eqn:Ev; [ | discriminate Ei].
      pose proof Ev as Ev'. unfold elim_view, elim_head in Ev'.
      destruct (spine_head t) eqn:Eh; try discriminate Ev'. destruct g as [ | | D' s' | ]; try discriminate Ev'.
      destruct (sig_elim sg D' s') as [[A [|]]|] eqn:Ee; try discriminate Ev'.
      destruct (sig_ind sg D') as [d'|] eqn:Ed; try discriminate Ev'.
      destruct (Nat.eqb _ _); [ | discriminate Ev']. injection Ev' as -> -> ->.
      destruct (cl_elim Hcl _ _ _ _ Ee Ed) as [Hpc Hf].
      destruct (ctor_view D d (last (spine_args t) (Var 0))) as [[[i cd] xs]|] eqn:Ecv; [ | discriminate Ei].
      destruct (nth_error _ i) as [m|] eqn:Em; [ | discriminate Ei]. injection Ei as <-.
      destruct (ctor_view_spec _ _ _ _ _ _ Ecv) as (c & ps & Ex & Ec & _ & _).
      assert (Hlast : an (last (spine_args t) (Var 0)) = true).
      { destruct (spine_args t) as [|a l] eqn:El; [reflexivity | ]. try rewrite El in Ha.
        rewrite forallb_forall in Ha. apply Ha. apply last_in. discriminate. }
      rewrite Ex, an_apps, forallb_app in Hlast. apply andb_prop in Hlast as [_ Hlast].
      apply andb_prop in Hlast as [_ Hxs].
      rewrite an_apps. apply andb_true_intro. split.
      + apply nth_error_In in Em.
        assert (Hs : forallb an (skipn (S (length (ind_params d))) (spine_args t)) = true).
        { rewrite <- (firstn_skipn (S (length (ind_params d))) (spine_args t)), forallb_app in Ha.
          apply andb_prop in Ha. exact (proj2 Ha). }
        pose proof (forallb_firstn _ (length (ind_ctors d)) _ Hs) as Hm. rewrite forallb_forall in Hm.
        exact (Hm m Em).
      + apply an_iota_args.
        * exact Hpc.
        * exact (forallb_firstn _ (S (length (ind_params d)) + length (ind_ctors d)) _ Ha).
        * rewrite rev'_rev, forallb_forall. intros x Hx. apply in_rev in Hx.
          rewrite <- (firstn_skipn (length (ind_params d)) (spine_args t)), forallb_app in Ha.
          apply andb_prop in Ha as [Ha _]. rewrite forallb_forall in Ha. exact (Ha x Hx).
        * exact Hxs.
        * intros Bs vs Hin. exact (Hf cd (nth_error_In _ _ (find_ctor_nth_error _ _ _ _ Ec)) Bs vs Hin).
    - unfold fix_unfold, fix_at in H.
      destruct (fix_view t) as [[[A k] b]|] eqn:Ev; [ | discriminate H].
      destruct (fix_view_spec _ _ _ _ Ev) as [Eh _].
      destruct (spine_head (last (spine_args t) (Var 0))); try discriminate H.
      destruct g; try discriminate H. injection H as <-.
      rewrite Eh in Hh. cbn [allnodes] in Hh. apply andb_prop in Hh as [HA Hb].
      rewrite an_apps, Ha, andb_true_r. apply an_subst1; [exact Hb | cbn [allnodes]; rewrite HA, Hb; reflexivity].
  Qed.
End Closure.

Section Step.
  Variable pc : gref -> bool.
  Variable pk : String.string -> bool.
  Variable sg : signature.
  Local Notation an := (allnodes pc pk).
  Hypothesis Hcl : an_closed pc pk sg.

  Lemma an_case_iota : forall t u, case_iota sg t = Some u -> an t = true -> an u = true.
  Proof.
    intros t u H Ht. destruct (case_iota_case _ _ _ H) as (D & s & P & x & bs & ->).
    unfold case_iota in H. cbn [allnodes] in Ht.
    apply andb_prop in Ht as [Ht Hbs]. apply andb_prop in Ht as [Ht Hx].
    destruct (sig_ind sg D) as [d|]; [ | discriminate H].
    destruct (ctor_view D d x) as [[[i cd] xs]|] eqn:Ecv; [ | discriminate H].
    destruct (nth_error bs i) as [b|] eqn:Eb; [ | discriminate H]. injection H as <-.
    destruct (ctor_view_spec _ _ _ _ _ _ Ecv) as (c & ps & -> & _ & _ & _).
    rewrite an_apps, forallb_app in Hx. apply andb_prop in Hx as [_ Hx]. apply andb_prop in Hx as [_ Hxs].
    rewrite an_apps, Hxs, andb_true_r. rewrite forallb_forall in Hbs. exact (Hbs b (nth_error_In _ _ Eb)).
  Qed.

  Lemma red1_an : forall t u, red1 sg t u -> an t = true -> an u = true.
  Proof.
    intros t u H. induction H; intros Ht; cbn [allnodes] in *;
      repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [? ?] end;
      repeat (apply andb_true_intro; split); auto.
    - apply an_subst1; assumption.
    - rewrite forallb_app in *. cbn [forallb] in *.
      repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [? ?] end.
      repeat (apply andb_true_intro; split); auto.
    - exact (cl_delta Hcl _ _ H).
    - exact (an_spine_iota pc pk sg Hcl _ _ H Ht).
    - exact (an_case_iota _ _ H Ht).
  Qed.

  Lemma red_an : forall t u, red sg t u -> an t = true -> an u = true.
  Proof. intros t u H. induction H; eauto using red1_an. Qed.
End Step.

Section RedStep.
  Variable r : gref -> gref.
  Variables sg sg' : signature.
  Variable cok : String.string -> bool.
  Hypothesis HR : cren_ok r sg sg' cok.

  Local Notation cr := (cren r).

  (** Reduction keeps the matches [cok] accepts. *)
  Lemma cases_closed : an_closed (fun _ => true) cok sg.
  Proof.
    split; [intros g b H; exact (proj2 (ok_delta HR _ _ H)) | ].
    intros D s A d He Hd. split; [reflexivity | ]. intros c Hc Bs vs Hin.
    destruct (ok_elim HR _ _ _ _ He Hd) as (_ & _ & _ & Hf). pose proof (Hf c Hc Bs vs Hin) as H.
    rewrite forallb_forall. rewrite Forall_forall in H. intros v Hv. exact (proj2 (H v Hv)).
  Qed.

  Lemma red1_cren : forall t u, red1 sg t u -> cases_in cok t = true -> red1 sg' (cr t) (cr u).
  Proof.
    intros t u H. induction H; intros Ht; cbn [cren allnodes] in *;
      repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [? ?] end.
    all: try (constructor; auto; fail).
    - rewrite cren_subst1. apply R_Beta.
    - rewrite !map_app. cbn [map]. apply R_CaseBr. apply IHred1.
      rewrite forallb_app in *. cbn [forallb] in *.
      repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [? ?] end. assumption.
    - apply R_Delta. exact (proj1 (ok_delta HR _ _ H)).
    - apply R_Spine. eapply spine_iota_cren; eassumption.
    - apply R_Case. eapply case_iota_cren; eassumption.
  Qed.

  Lemma red_cren : forall t u, red sg t u -> cases_in cok t = true -> red sg' (cr t) (cr u).
  Proof.
    intros t u H. induction H as [t u H | t | t u v H1 IH1 H2 IH2]; intros Ht.
    - apply rt_step. exact (red1_cren _ _ H Ht).
    - apply rt_refl.
    - eapply rt_trans; [exact (IH1 Ht) | apply IH2].
      exact (red_an _ _ sg cases_closed _ _ H1 Ht).
  Qed.

  (** Conversion between terms with allowed matches. *)
  Lemma conv_cren : forall t u, conv sg t u -> cases_in cok t = true -> cases_in cok u = true ->
    conv sg' (cr t) (cr u).
  Proof.
    intros t u H Ht Hu. destruct (church_rosser sg t u H) as (w & H1 & H2).
    apply (conv_common sg' _ _ (cr w)); [exact (red_cren _ _ H1 Ht) | exact (red_cren _ _ H2 Hu)].
  Qed.

  Lemma struct_arg_cren : forall A k D, struct_arg sg A k D -> cases_in cok A = true -> r (Ind D) = Ind D ->
    struct_arg sg' (cr A) k D.
  Proof.
    intros A k D H. induction H as [A T B D us H1 H2 | A T B k D H1 _ IH]; intros HA Hr.
    - pose proof (red_an _ _ sg cases_closed _ _ H1 HA) as HP. cbn [allnodes] in HP.
      apply andb_prop in HP as [HT _].
      apply (SA_Here _ _ (cr T) (cr B) _ (map cr us)).
      + exact (red_cren _ _ H1 HA).
      + pose proof (red_cren _ _ H2 HT) as H2'. rewrite cren_apps in H2'. cbn [cren] in H2'. rewrite Hr in H2'.
        exact H2'.
    - pose proof (red_an _ _ sg cases_closed _ _ H1 HA) as HP. cbn [allnodes] in HP.
      apply andb_prop in HP as [_ HB].
      exact (SA_Next _ _ (cr T) (cr B) _ _ (red_cren _ _ H1 HA) (IH HB Hr)).
  Qed.
End RedStep.

(** ** The guard of [fix] under the renaming *)

Section GuardCren.
  Variable r : gref -> gref.
  Variables sg sg' : signature.
  Variable cok : String.string -> bool.
  Hypothesis Hcase : forall D d, sig_ind sg D = Some d -> cok D = true -> sig_ind sg' D = Some d.
  Variable k : nat.
  Local Notation cr := (cren r).

  Lemma sub_arg_cren : forall ms a, sub_arg ms (cr a) = sub_arg ms a.
  Proof.
    intros ms a. unfold sub_arg. rewrite spine_head_cren, spine_args_cren, length_map.
    destruct (spine_head a); reflexivity.
  Qed.

  Lemma is_arg_cren : forall ms x, is_arg ms (cr x) = is_arg ms x.
  Proof. intros ms x. destruct x; reflexivity. Qed.

  Lemma origin_cren : forall ms x, origin ms (cr x) = origin ms x.
  Proof. intros ms x. unfold origin. rewrite is_arg_cren, sub_arg_cren. reflexivity. Qed.

  Lemma self_headed_cren : forall ms t, self_headed ms (cr t) = self_headed ms t.
  Proof. intros ms t. unfold self_headed. rewrite spine_head_cren. destruct (spine_head t); reflexivity. Qed.

  Lemma atomic_cren : forall t, atomic (cr t) = atomic t.
  Proof. intros t. destruct t; reflexivity. Qed.

  Lemma peel_cren : forall fds ms b, peel ms fds (cr b) = (fst (peel ms fds b), cr (snd (peel ms fds b))).
  Proof.
    induction fds as [|fd fds IH]; intros ms b; [reflexivity | ].
    destruct b; try reflexivity. cbn [cren peel]. apply IH.
  Qed.

  Theorem guarded_cren : forall ms t, Guarded sg k ms t -> decl_cases sg t = true -> cases_in cok t = true ->
    Guarded sg' k ms (cr t).
  Proof.
    induction 1 as
      [ms i args Hself Hk Hsub _ IH | ms i Hi | ms f a Hs _ IHf _ IHa | ms b _ IHb
      | ms A B _ IHA _ IHB | ms A B _ IHA _ IHB | ms A k' b _ IHA _ IHb
      | ms u A _ IHu _ IHA | ms C e _ IHC _ IHe | ms a b _ IHa _ IHb
      | ms C c u _ IHC _ IHc _ IHu | ms C t f b _ IHC _ IHt _ IHf _ IHb
      | ms p _ IHp | ms p _ IHp
      | ms D s P x bs _ IHP _ IHx _ IHbs | ms t Ht ]; intros Hd Hc; cbn [allnodes cren] in Hd, Hc |- *;
      repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [? ?] end.
    - rewrite an_apps in Hd. rewrite an_apps in Hc.
      apply andb_prop in Hd as [_ Hd]. apply andb_prop in Hc as [_ Hc]. rewrite forallb_forall in Hd, Hc.
      rewrite cren_apps. cbn [cren]. apply G_Call; [exact Hself | rewrite length_map; exact Hk | | ].
      + replace (nth k (map cr args) (Var 0)) with (cr (nth k args (Var 0))) by (exact (eq_sym (map_nth cr args (Var 0) k))).
        rewrite sub_arg_cren. exact Hsub.
      + intros a' Ha'. apply in_map_iff in Ha' as (a & <- & Ha). exact (IH a Ha (Hd a Ha) (Hc a Ha)).
    - apply G_Var, Hi.
    - apply G_App; [rewrite <- Hs; change (App (cr f) (cr a)) with (cr (App f a)); apply self_headed_cren | auto | auto].
    - apply G_Lam; auto.
    - apply G_Pi; auto.
    - apply G_Sigma; auto.
    - apply G_Fix; auto.
    - apply G_Ann; auto.
    - apply G_ElimVoid; auto.
    - apply G_Pair; auto.
    - apply G_ElimUnit; auto.
    - apply G_ElimBool; auto.
    - apply G_Fst; auto.
    - apply G_Snd; auto.
    - assert (HD : sig_ind sg D <> None) by (unfold declared in *; intros E; rewrite E in *; discriminate).
      assert (Hbf : branch_fields sg' ms D (cr x) = branch_fields sg ms D x).
      { unfold branch_fields. rewrite origin_cren. destruct (origin ms x); [ | reflexivity].
        destruct (sig_ind sg D) as [d|] eqn:Ed; [ | contradiction].
        match goal with H : cok D = true |- _ => rewrite (Hcase _ _ Ed H) end. reflexivity. }
      apply G_Case; [auto | auto | ]. intros j b' Hj. rewrite Hbf.
      rewrite nth_error_map in Hj. destruct (nth_error bs j) as [b|] eqn:Eb; [ | discriminate Hj].
      injection Hj as <-. cbv zeta. rewrite peel_cren. cbn [fst snd].
      apply (IHbs j b Eb).
      + apply an_peel.
        match goal with H : forallb (decl_cases sg) bs = true |- _ => rewrite forallb_forall in H; apply H end.
        exact (nth_error_In _ _ Eb).
      + apply (an_peel _ _ (nth j (branch_fields sg ms D x) []) ms b).
        match goal with H : forallb (allnodes _ cok) bs = true |- _ => rewrite forallb_forall in H; apply H end.
        exact (nth_error_In _ _ Eb).
    - apply G_Atom. rewrite atomic_cren. exact Ht.
  Qed.
End GuardCren.

(** ** The types of a match under the renaming *)

(** The renaming keeps a description: its telescopes, fields and
    indices, and the constant of its family. *)
Definition desc_fixed (r : gref -> gref) (d : ind_desc) : Prop :=
  r (Ind (ind_name d)) = Ind (ind_name d) /\
  Forall (fixed r) (ind_indices d) /\
  (forall c, In c (ind_ctors d) ->
     Forall (fixed r) (field_types (ind_name d) (length (ind_params d)) 0 (ctor_fields c)) /\
     Forall (fixed r) (ctor_indices c)).

Section CaseTypes.
  Variable r : gref -> gref.
  Hypothesis Hctor : forall D c, r (Ctor D c) = Ctor D c.
  Local Notation cr := (cren r).

  Lemma cren_inst : forall m env n, cr (inst m env n) = inst m (map cr env) n.
  Proof.
    intros m env n. unfold inst. destruct (Nat.ltb n m); [reflexivity | ].
    rewrite cren_lift. f_equal. exact (eq_sym (map_nth cr env (Var 0) _)).
  Qed.

  Lemma cren_inst_env : forall env m T, fixed r T -> cr (inst_env env m T) = inst_env (map cr env) m T.
  Proof.
    intros env m T HT. unfold inst_env. rewrite cren_subst, HT. apply subst_ext. intros n. apply cren_inst.
  Qed.

  Lemma cren_inst_tele_env : forall Ts env m, Forall (fixed r) Ts ->
    map cr (inst_tele_env env m Ts) = inst_tele_env (map cr env) m Ts.
  Proof.
    induction Ts as [|T Ts IH]; intros env m H; [reflexivity | ]. inversion H as [|? ? HT HTs]; subst.
    cbn [inst_tele_env map]. rewrite cren_inst_env by exact HT. f_equal. apply IH, HTs.
  Qed.

  Lemma cren_case_motive_type : forall d ps s, desc_fixed r d ->
    cr (case_motive_type d ps s) = case_motive_type d (map cr ps) s.
  Proof.
    intros d ps s (Hi & HIs & _). unfold case_motive_type, inst_tele. cbv zeta.
    rewrite cren_pis. f_equal.
    - rewrite params_env_map. apply cren_inst_tele_env, HIs.
    - cbn [cren]. rewrite cren_apps. cbn [cren]. rewrite Hi, map_app, cren_vars, !map_map. do 3 f_equal.
      apply map_ext. intros t. apply cren_lift.
  Qed.

  Lemma cren_case_branch_type : forall d ps P c, desc_fixed r d -> In c (ind_ctors d) ->
    cr (case_branch_type d ps P c) = case_branch_type d (map cr ps) (cr P) c.
  Proof.
    intros d ps P c (Hi & _ & Hcs) Hc. destruct (Hcs c Hc) as [HF HU].
    unfold case_branch_type. cbv zeta. rewrite cren_pis. f_equal.
    - rewrite params_env_map. apply cren_inst_tele_env, HF.
    - rewrite cren_apps, cren_lift, map_app. f_equal. f_equal.
      + rewrite map_map, params_env_map. induction HU as [|v vs Hv _ IH]; [reflexivity | ].
        cbn [map]. f_equal; [apply cren_inst_env, Hv | exact IH].
      + cbn [map]. f_equal. rewrite cren_apps. cbn [cren]. rewrite Hctor, map_app, cren_vars, !map_map.
        do 2 f_equal. apply map_ext. intros t. apply cren_lift.
  Qed.
End CaseTypes.

Lemma lookup_cren : forall r G n, lookup (map (cren r) G) n = option_map (cren r) (lookup G n).
Proof.
  intros r G n. unfold lookup. rewrite nth_error_map.
  destruct (nth_error G n); [cbn [option_map]; rewrite cren_lift; reflexivity | reflexivity].
Qed.

(** ** Renaming back: the declarative judgments *)

Section TypingCren.
  Variable S : spec.
  Variable r : gref -> gref.
  Variables sg sg' : signature.
  Hypothesis HR : cren_ok r sg sg' (fun _ => true).
  Hypothesis Hfixed : forall D d, sig_ind sg D = Some d -> desc_fixed r d.
  Hypothesis Htype : forall g A, sig_type sg g = Some A -> sig_type sg' (r g) = Some (cren r A).
  Local Notation cr := (cren r).

  Lemma conv_cren_all : forall t u, conv sg t u -> conv sg' (cr t) (cr u).
  Proof. intros t u H. apply (conv_cren r sg sg' (fun _ => true) HR); [exact H | | ]; apply an_true. Qed.

  Theorem typing_cren :
    (forall G, wf_ctx S sg G -> wf_ctx S sg' (map cr G)) /\
    (forall G t A, has_type S sg G t A -> has_type S sg' (map cr G) (cr t) (cr A)) /\
    (forall G d ps P cs bs, has_branches S sg G d ps P cs bs -> desc_fixed r d ->
       (forall c, In c cs -> In c (ind_ctors d)) ->
       has_branches S sg' (map cr G) d (map cr ps) (cr P) cs (map cr bs)).
  Proof.
    apply typing_mutind; intros; cbn [cren map] in *; try rewrite !cren_subst1 in *; cbn [cren] in *.
    - (* W_Nil *) constructor.
    - (* W_Cons *) econstructor; eassumption.
    - (* T_Sort *) constructor; assumption.
    - (* T_Var *) constructor; [assumption | ].
      rewrite lookup_cren. match goal with H : lookup _ _ = _ |- _ => rewrite H end. reflexivity.
    - (* T_Pi *) econstructor; eassumption.
    - (* T_Lam *) econstructor; eassumption.
    - (* T_App *) econstructor; eassumption.
    - (* T_Ann *) econstructor; eassumption.
    - (* T_Conv *) econstructor; [eassumption | eassumption | apply conv_cren_all; assumption].
    - (* T_Void *) econstructor; eassumption.
    - (* T_ElimVoid *) econstructor; eassumption.
    - (* T_Unit *) econstructor; eassumption.
    - (* T_Tt *) econstructor; eassumption.
    - (* T_ElimUnit *) econstructor; eassumption.
    - (* T_Bool *) econstructor; eassumption.
    - (* T_True *) econstructor; eassumption.
    - (* T_False *) econstructor; eassumption.
    - (* T_ElimBool *) econstructor; eassumption.
    - (* T_Sigma *) econstructor; eassumption.
    - (* T_Pair *) econstructor; eassumption.
    - (* T_Fst *) econstructor; eassumption.
    - (* T_Snd *) econstructor; eassumption.
    - (* a constant *) apply T_Const; [assumption | assumption | apply Htype; assumption].
    - (* a match *)
      match goal with H : sig_ind sg D = Some d |- _ =>
        pose proof (ok_case HR _ _ H eq_refl) as Hd'; pose proof (Hfixed _ _ H) as Hfx end.
      rewrite cren_apps, map_app. cbn [map].
      pose proof (proj1 Hfx) as Hr. rewrite (sig_ind_name _ _ _ e0) in Hr.
      apply (T_Case S sg' (map cr G) D s (cr P) (cr x) (map cr bs) d (map cr ps) (map cr us));
        [assumption | exact Hd' | assumption | rewrite length_map; assumption
        | rewrite length_map; assumption | | | ].
      + match goal with H : has_type S sg' _ (cren r x) _ |- _ => rewrite cren_apps, map_app in H; cbn [cren] in H;
          rewrite Hr in H; exact H end.
      + rewrite <- cren_case_motive_type by assumption. assumption.
      + apply H1; [exact Hfx | intros c Hc; exact Hc].
    - (* a fixpoint *)
      apply (T_Fix S sg' (map cr G) (cr A) k (cr b) s D); [assumption | | | | ].
      + apply (struct_arg_cren r sg sg' (fun _ => true) HR); [assumption | apply an_true | ].
        destruct (sig_ind sg D) as [d|] eqn:Ed; [ | contradiction].
        pose proof (proj1 (Hfixed _ _ Ed)) as Hr. rewrite (sig_ind_name _ _ _ Ed) in Hr. exact Hr.
      + intros E. destruct (sig_ind sg D) as [d|] eqn:Ed; [ | contradiction].
        rewrite (ok_case HR _ _ Ed eq_refl) in E. discriminate E.
      + rewrite <- cren_lift. assumption.
      + destruct f as (body & -> & Hg). exists (cr body). rewrite cren_lams. split; [reflexivity | ].
        apply (guarded_cren r sg sg' (fun _ => true) (ok_case HR)); [exact Hg | | apply an_true].
        rewrite <- (an_lams _ (declared sg) (Datatypes.S k)). exact (proj1 (proj2 (typed_decl_cases S sg)) _ _ _ h0).
    - constructor.
    - constructor.
      + rewrite <- cren_case_branch_type; [assumption | exact (ok_ctor HR) | assumption | apply H2; left; reflexivity].
      + apply H0; [assumption | intros c' Hc'; apply H2; right; exact Hc'].
  Qed.
End TypingCren.

(** ** Renaming forward: the annotated judgments *)

(** The matches of a description are on allowed names. *)
Definition desc_cases (cok : String.string -> bool) (d : ind_desc) : Prop :=
  Forall (fun T => cases_in cok T = true) (ind_indices d) /\
  (forall c, In c (ind_ctors d) ->
     Forall (fun T => cases_in cok T = true) (field_types (ind_name d) (length (ind_params d)) 0 (ctor_fields c)) /\
     Forall (fun T => cases_in cok T = true) (ctor_indices c)).

Lemma cases_case_motive_type : forall cok d ps s, desc_cases cok d -> forallb (cases_in cok) ps = true ->
  cases_in cok (case_motive_type d ps s) = true.
Proof.
  intros cok d ps s [HI _] Hps. unfold case_motive_type, inst_tele. cbv zeta.
  rewrite an_pis. apply andb_true_intro. split.
  - apply an_inst_tele_env; [exact HI | apply an_params_env, Hps].
  - cbn [allnodes]. rewrite an_apps, forallb_app, an_vars.
    assert (H : forallb (cases_in cok) (map (lift (length (ind_indices d))) ps) = true).
    { rewrite forallb_forall in *. intros t Ht. apply in_map_iff in Ht as (t0 & <- & Ht0). rewrite an_lift. auto. }
    rewrite H. reflexivity.
Qed.

Lemma cases_case_branch_type : forall cok d ps P c, desc_cases cok d -> In c (ind_ctors d) ->
  forallb (cases_in cok) ps = true -> cases_in cok P = true -> cases_in cok (case_branch_type d ps P c) = true.
Proof.
  intros cok d ps P c [_ Hcs] Hc Hps HP. destruct (Hcs c Hc) as [HF HU].
  unfold case_branch_type. cbv zeta. rewrite an_pis. apply andb_true_intro. split.
  - apply an_inst_tele_env; [exact HF | apply an_params_env, Hps].
  - rewrite an_apps, an_lift, HP, forallb_app. cbn [forallb andb]. apply andb_true_intro. split.
    + rewrite forallb_forall. intros t Ht. apply in_map_iff in Ht as (v & <- & Hv).
      unfold inst_env. apply an_subst.
      * rewrite Forall_forall in HU. exact (HU v Hv).
      * intros n. unfold inst. destruct (Nat.ltb n _); [reflexivity | ]. rewrite an_lift.
        destruct (nth_error (params_env ps) (n - length (ctor_fields c))) as [e|] eqn:Ee.
        -- rewrite (nth_error_nth _ _ _ Ee). pose proof (an_params_env _ _ _ Hps) as H.
           rewrite forallb_forall in H. exact (H e (nth_error_In _ _ Ee)).
        -- rewrite nth_overflow by (apply nth_error_None; exact Ee). reflexivity.
    + rewrite an_apps, forallb_app, an_vars.
      assert (H : forallb (cases_in cok) (map (lift (length (ctor_fields c))) ps) = true).
      { rewrite forallb_forall in *. intros t Ht. apply in_map_iff in Ht as (t0 & <- & Ht0). rewrite an_lift. auto. }
      rewrite H. reflexivity.
Qed.

(** Every match of a checked term is on a declared type. *)
Lemma bidir_decl_cases : forall S sg,
  (forall G t A, synth S sg G t A -> decl_cases sg t = true) /\
  (forall G t A, chk S sg G t A -> decl_cases sg t = true) /\
  (forall G d ps P cs bs, chk_branches S sg G d ps P cs bs -> forallb (decl_cases sg) bs = true).
Proof.
  intros S sg. apply synth_chk_mut; intros; cbn [allnodes forallb]; auto;
    repeat match goal with H : ?x = true |- context [?x] => rewrite H end; auto.
  unfold declared. match goal with H : sig_ind sg _ = Some _ |- _ => rewrite H end.
  repeat match goal with H : ?x = true |- context [?x] => rewrite H end. reflexivity.
Qed.

(** The constants allowed in checked terms, and fixpoints whose types
    reach only families kept by the renaming. *)
Fixpoint fixok (pcf : gref -> bool) (pkf : String.string -> bool) (t : term) : bool :=
  match t with
  | Srt _ | Var _ | Void | Unit | Tt | Bool | BTrue | BFalse | Const _ => true
  | Pi A B | Sigma A B | App A B | Ann A B | ElimVoid A B | Pair A B => fixok pcf pkf A && fixok pcf pkf B
  | Lam b | Fst b | Snd b => fixok pcf pkf b
  | ElimUnit C c u => fixok pcf pkf C && fixok pcf pkf c && fixok pcf pkf u
  | ElimBool C t f b => fixok pcf pkf C && fixok pcf pkf t && fixok pcf pkf f && fixok pcf pkf b
  | Case _ _ P x bs => fixok pcf pkf P && fixok pcf pkf x && forallb (fixok pcf pkf) bs
  | Fix A _ b => allnodes pcf pkf A && fixok pcf pkf A && fixok pcf pkf b
  end.

Section StructFamily.
  Variable pc : gref -> bool.
  Variable pk : String.string -> bool.
  Variable sg : signature.
  Hypothesis Hcl : an_closed pc pk sg.

  Lemma struct_arg_family : forall A k D, struct_arg sg A k D -> allnodes pc pk A = true -> pc (Ind D) = true.
  Proof.
    intros A k D H. induction H as [A T B D us H1 H2 | A T B k D H1 _ IH]; intros HA.
    - pose proof (red_an _ _ sg Hcl _ _ H1 HA) as HP. cbn [allnodes] in HP. apply andb_prop in HP as [HT _].
      pose proof (red_an _ _ sg Hcl _ _ H2 HT) as Hs. rewrite an_apps in Hs. apply andb_prop in Hs as [Hs _].
      exact Hs.
    - pose proof (red_an _ _ sg Hcl _ _ H1 HA) as HP. cbn [allnodes] in HP. apply andb_prop in HP as [_ HB].
      exact (IH HB).
  Qed.
End StructFamily.

Section SynthCren.
  Variable S : spec.
  Variable r : gref -> gref.
  Variables sg sg' : signature.
  Variable cok : String.string -> bool.
  Variable pc_ok : gref -> bool.
  Variables (pcf : gref -> bool) (pkf : String.string -> bool).
  Hypothesis HR : cren_ok r sg sg' cok.
  Hypothesis Hcl_f : an_closed pcf pkf sg.
  Hypothesis Hpcf : forall D, pcf (Ind D) = true -> r (Ind D) = Ind D /\ (forall d, sig_ind sg D = Some d -> sig_ind sg' D = Some d).
  Hypothesis Htype_f : forall g A, sig_type sg g = Some A -> pc_ok g = true ->
    sig_type sg' (r g) = Some (cren r A) /\ cases_in cok A = true.
  Hypothesis Hdesc_f : forall D d, sig_ind sg D = Some d -> cok D = true -> desc_fixed r d /\ desc_cases cok d.
  Local Notation cr := (cren r).
  Local Notation an := (allnodes pc_ok cok).
  Local Notation cs := (cases_in cok).
  Local Notation fx := (fixok pcf pkf).

  Local Lemma rc : forall t u, red sg t u -> cs t = true -> red sg' (cr t) (cr u).
  Proof. exact (red_cren r sg sg' cok HR). Qed.

  Local Lemma ra : forall t u, red sg t u -> cs t = true -> cs u = true.
  Proof. exact (red_an _ _ sg (cases_closed r sg sg' cok HR)). Qed.

  Local Lemma cc : forall t u, conv sg t u -> cs t = true -> cs u = true -> conv sg' (cr t) (cr u).
  Proof. exact (conv_cren r sg sg' cok HR). Qed.

  Local Lemma an_cs : forall t, an t = true -> cs t = true.
  Proof. intros t. apply an_weaken; auto. Qed.

  Local Lemma cs_ctx : forall A G, cs A = true -> forallb cs G = true -> forallb cs (A :: G) = true.
  Proof. intros A G HA HG. cbn [forallb]. rewrite HA, HG. reflexivity. Qed.

  Local Ltac crush :=
    cbn [allnodes fixok forallb cren map] in *;
    repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [? ?] end.

  Theorem synth_cren :
    (forall G t A, synth S sg G t A -> an t = true -> fx t = true -> forallb cs G = true ->
       synth S sg' (map cr G) (cr t) (cr A) /\ cs A = true) /\
    (forall G t B, chk S sg G t B -> an t = true -> fx t = true -> forallb cs G = true -> cs B = true ->
       chk S sg' (map cr G) (cr t) (cr B)) /\
    (forall G d ps P cs0 bs, chk_branches S sg G d ps P cs0 bs -> forallb an bs = true -> forallb fx bs = true ->
       forallb cs G = true -> forallb cs ps = true -> cs P = true -> desc_fixed r d -> desc_cases cok d ->
       (forall c, In c cs0 -> In c (ind_ctors d)) ->
       chk_branches S sg' (map cr G) d (map cr ps) (cr P) cs0 (map cr bs)).
  Proof.
    apply synth_chk_mut.
    - (* S_Sort *) intros G s s' Hax _ _ _. split; [constructor; exact Hax | reflexivity].
    - (* S_Var *) intros G n A Hl _ _ HG. split.
      + constructor. rewrite lookup_cren, Hl. reflexivity.
      + exact (an_lookup _ _ _ _ _ HG Hl).
    - (* S_Pi *) intros G A B TA TB s1 s2 s3 _ IHA HA _ IHB HB Hr Han Hfx HG. crush.
      destruct (IHA ltac:(assumption) ltac:(assumption) HG) as [HA' HcA].
      destruct (IHB ltac:(assumption) ltac:(assumption) ltac:(rewrite (an_cs A) by assumption; exact HG)) as [HB' HcB].
      split; [ | reflexivity]. econstructor; [exact HA' | exact (rc _ _ HA HcA) | exact HB' | exact (rc _ _ HB HcB) | exact Hr].
    - (* S_App *) intros G f u F A B _ IHf HF _ IHu Han Hfx HG. crush.
      destruct (IHf ltac:(assumption) ltac:(assumption) HG) as [Hf' HcF].
      pose proof (ra _ _ HF HcF) as HcP. cbn [allnodes] in HcP. apply andb_prop in HcP as [HcA HcB].
      pose proof (IHu ltac:(assumption) ltac:(assumption) HG HcA) as Hu'.
      split.
      + rewrite cren_subst1. econstructor; [exact Hf' | exact (rc _ _ HF HcF) | exact Hu'].
      + apply an_subst1; [exact HcB | apply an_cs; assumption].
    - (* S_Ann *) intros G t A T s _ IHA HT _ IHt Han Hfx HG. crush.
      destruct (IHA ltac:(assumption) ltac:(assumption) HG) as [HA' HcT].
      split; [ | apply an_cs; assumption].
      econstructor; [exact HA' | exact (rc _ _ HT HcT) | apply IHt; try assumption; apply an_cs; assumption].
    - intros G s0 Hp _ _ _. split; [econstructor; exact Hp | reflexivity].
    - intros G s0 Hp _ _ _. split; [econstructor; exact Hp | reflexivity].
    - intros G s0 Hp _ _ _. split; [econstructor; exact Hp | reflexivity].
    - intros G s0 Hp _ _ _. split; [econstructor; exact Hp | reflexivity].
    - intros G s0 Hp _ _ _. split; [econstructor; exact Hp | reflexivity].
    - intros G s0 Hp _ _ _. split; [econstructor; exact Hp | reflexivity].
    - (* S_ElimVoid *) intros G C e TC D K s s0 Hp _ IHC HTC HD HK _ IHe Han Hfx HG. crush.
      destruct (IHC ltac:(assumption) ltac:(assumption) HG) as [HC' HcTC].
      pose proof (ra _ _ HTC HcTC) as HcP. cbn [allnodes] in HcP. apply andb_prop in HcP as [HcD HcK].
      split; [ | cbn [allnodes]; rewrite (an_cs C), (an_cs e) by assumption; reflexivity].
      econstructor; [exact Hp | exact HC' | exact (rc _ _ HTC HcTC) | exact (cc _ _ HD HcD eq_refl)
                    | exact (rc _ _ HK HcK) | apply IHe; auto].
    - (* S_ElimUnit *) intros G C c u TC D K s s0 Hp _ IHC HTC HD HK _ IHc _ IHu Han Hfx HG. crush.
      destruct (IHC ltac:(assumption) ltac:(assumption) HG) as [HC' HcTC].
      pose proof (ra _ _ HTC HcTC) as HcP. cbn [allnodes] in HcP. apply andb_prop in HcP as [HcD HcK].
      split; [ | cbn [allnodes]; rewrite (an_cs C), (an_cs u) by assumption; reflexivity].
      econstructor; [exact Hp | exact HC' | exact (rc _ _ HTC HcTC) | exact (cc _ _ HD HcD eq_refl)
                    | exact (rc _ _ HK HcK) | | ].
      + apply IHc; auto. cbn [allnodes]. rewrite (an_cs C) by assumption. reflexivity.
      + apply IHu; auto.
    - (* S_ElimBool *) intros G C t f b TC D K s s0 Hp _ IHC HTC HD HK _ IHt _ IHf _ IHb Han Hfx HG. crush.
      destruct (IHC ltac:(assumption) ltac:(assumption) HG) as [HC' HcTC].
      pose proof (ra _ _ HTC HcTC) as HcP. cbn [allnodes] in HcP. apply andb_prop in HcP as [HcD HcK].
      split; [ | cbn [allnodes]; rewrite (an_cs C), (an_cs b) by assumption; reflexivity].
      econstructor; [exact Hp | exact HC' | exact (rc _ _ HTC HcTC) | exact (cc _ _ HD HcD eq_refl)
                    | exact (rc _ _ HK HcK) | | | ].
      + apply IHt; auto. cbn [allnodes]. rewrite (an_cs C) by assumption. reflexivity.
      + apply IHf; auto. cbn [allnodes]. rewrite (an_cs C) by assumption. reflexivity.
      + apply IHb; auto.
    - (* S_Sigma *) intros G A B TA TB s1 s2 s3 _ IHA HA _ IHB HB Hr Han Hfx HG. crush.
      destruct (IHA ltac:(assumption) ltac:(assumption) HG) as [HA' HcA].
      destruct (IHB ltac:(assumption) ltac:(assumption) ltac:(rewrite (an_cs A) by assumption; exact HG)) as [HB' HcB].
      split; [ | reflexivity]. econstructor; [exact HA' | exact (rc _ _ HA HcA) | exact HB' | exact (rc _ _ HB HcB) | exact Hr].
    - (* S_Fst *) intros G p P A B _ IHp HP Han Hfx HG. crush.
      destruct (IHp ltac:(assumption) ltac:(assumption) HG) as [Hp' HcP].
      pose proof (ra _ _ HP HcP) as HcS. cbn [allnodes] in HcS. apply andb_prop in HcS as [HcA HcB].
      split; [econstructor; [exact Hp' | exact (rc _ _ HP HcP)] | exact HcA].
    - (* S_Snd *) intros G p P A B _ IHp HP Han Hfx HG. crush.
      destruct (IHp ltac:(assumption) ltac:(assumption) HG) as [Hp' HcP].
      pose proof (ra _ _ HP HcP) as HcS. cbn [allnodes] in HcS. apply andb_prop in HcS as [HcA HcB].
      split.
      + rewrite cren_subst1. cbn [cren]. econstructor; [exact Hp' | exact (rc _ _ HP HcP)].
      + apply an_subst1; [exact HcB | cbn [allnodes]; apply an_cs; assumption].
    - (* S_Const *) intros G g A Hdecl Hg Han _ _. cbn [allnodes] in Han.
      destruct (Htype_f _ _ Hg Han) as [Hg' HcA]. split; [ | exact HcA].
      cbn [cren]. apply S_Const; [exact Hdecl | exact Hg'].
    - (* S_Case *) intros G D s P x bs X d ps us Hdecl Hd Hel _ IHx HX Hlp Hlu _ IHP _ IHbs Han Hfx HG. crush.
      destruct (Hdesc_f _ _ Hd ltac:(assumption)) as [Hfx' Hcd].
      pose proof (proj1 Hfx') as Hri. rewrite (sig_ind_name _ _ _ Hd) in Hri.
      destruct (IHx ltac:(assumption) ltac:(assumption) HG) as [Hx' HcX].
      pose proof (ra _ _ HX HcX) as HcI. rewrite an_apps, forallb_app in HcI. cbn [allnodes andb] in HcI.
      apply andb_prop in HcI as [Hcps Hcus].
      pose proof (rc _ _ HX HcX) as HX'. rewrite cren_apps, map_app in HX'. cbn [cren] in HX'. rewrite Hri in HX'.
      split.
      + rewrite cren_apps, map_app. cbn [map cren].
        apply (S_Case S sg' (map cr G) D s (cr P) (cr x) (map cr bs) (cr X) d (map cr ps) (map cr us));
          [exact Hdecl | exact (ok_case HR _ _ Hd ltac:(assumption)) | exact Hel | exact Hx' | exact HX'
          | rewrite length_map; exact Hlp | rewrite length_map; exact Hlu | | ].
        * rewrite <- cren_case_motive_type by assumption.
          apply IHP; try assumption. exact (cases_case_motive_type _ _ _ _ Hcd Hcps).
        * apply IHbs; try assumption; try (apply an_cs; assumption). intros c Hc. exact Hc.
      + rewrite an_apps, forallb_app. cbn [forallb allnodes]. rewrite Hcus, (an_cs P), (an_cs x) by assumption.
        reflexivity.
    - (* S_Fix *) intros G A k b T s D _ IHA HT Hsa Hne Hbc IHb Hgd Han Hfx HG. crush.
      destruct (IHA ltac:(assumption) ltac:(assumption) HG) as [HA' HcT].
      assert (HpD : pcf (Ind D) = true).
      { eapply struct_arg_family; [exact Hcl_f | exact Hsa | assumption]. }
      destruct (Hpcf D HpD) as [HrD HiD].
      split; [ | apply an_cs; assumption].
      apply S_Fix with (T := cr T) (s := s) (D := D).
      + exact HA'.
      + exact (rc _ _ HT HcT).
      + eapply struct_arg_cren; try eassumption. apply an_cs; assumption.
      + intros E. destruct (sig_ind sg D) as [d|] eqn:Ed; [ | contradiction]. rewrite (HiD d eq_refl) in E. discriminate E.
      + rewrite <- cren_lift. apply IHb; try assumption.
        * apply cs_ctx; [apply an_cs; assumption | exact HG].
        * rewrite an_lift. apply an_cs. assumption.
      + destruct Hgd as (body & -> & Hg). exists (cr body). rewrite cren_lams. split; [reflexivity | ].
        apply (guarded_cren r sg sg' cok (ok_case HR)); [exact Hg | | ].
        * rewrite <- (an_lams _ (declared sg) (Datatypes.S k)).
          exact (proj1 (proj2 (bidir_decl_cases S sg)) _ _ _ Hbc).
        * rewrite <- (an_lams _ _ (Datatypes.S k)). apply an_cs. assumption.
    - (* C_Lam *) intros G b T A B HT _ IHb Han Hfx HG HcT. crush.
      pose proof (ra _ _ HT HcT) as HcP. cbn [allnodes] in HcP. apply andb_prop in HcP as [HcA HcB].
      econstructor; [exact (rc _ _ HT HcT) | apply IHb; try assumption; exact (cs_ctx _ _ HcA HG)].
    - (* C_Pair *) intros G a b T A B HT _ IHa _ IHb Han Hfx HG HcT. crush.
      pose proof (ra _ _ HT HcT) as HcP. cbn [allnodes] in HcP. apply andb_prop in HcP as [HcA HcB].
      apply (C_Pair S sg' (map cr G) (cr a) (cr b) (cr T) (cr A) (cr B));
        [exact (rc _ _ HT HcT) | apply IHa; assumption | ].
      rewrite <- cren_subst1. apply IHb; try assumption. apply an_subst1; [exact HcB | apply an_cs; assumption].
    - (* C_Synth *) intros G t A B _ IHt Hc Han Hfx HG HcB.
      destruct (IHt Han Hfx HG) as [Ht' HcA]. econstructor; [exact Ht' | exact (cc _ _ Hc HcA HcB)].
    - (* CB_Nil *) intros. constructor.
    - (* CB_Cons *) intros G d ps P c cs0 b bs _ IHb _ IHbs Han Hfx HG Hps HP Hfd Hcd Hin. crush.
      constructor.
      + rewrite <- cren_case_branch_type; [ | exact (ok_ctor HR) | exact Hfd | apply Hin; left; reflexivity].
        apply IHb; try assumption. apply cases_case_branch_type; [exact Hcd | apply Hin; left; reflexivity | exact Hps | exact HP].
      + apply IHbs; try assumption. intros c' Hc'. apply Hin. right. exact Hc'.
  Qed.
End SynthCren.

(** ** Fixed terms *)

Lemma cren_fixed_an : forall r pc pk t, (forall g, pc g = true -> r g = g) -> allnodes pc pk t = true -> cren r t = t.
Proof.
  intros r pc pk t Hr. induction t using term_ind'; intros H; cbn [allnodes cren] in *;
    repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [? ?] end;
    try (f_equal; auto; fail).
  f_equal; auto. rewrite forallb_forall in *. rewrite Forall_forall in IHl.
    rewrite <- (map_id l) at 2. apply map_ext_in. intros b Hb. auto.
Qed.

Lemma cren_id : forall t, cren (fun g => g) t = t.
Proof. intros t. apply (cren_fixed_an _ (fun _ => true) (fun _ => true)); [reflexivity | apply an_true]. Qed.

Lemma cren_compose : forall r1 r2 t, cren r2 (cren r1 t) = cren (fun g => r2 (r1 g)) t.
Proof.
  intros r1 r2 t. induction t using term_ind'; cbn [cren]; f_equal; auto.
  rewrite map_map. induction IHl as [|b bs Hb _ IH]; [reflexivity | cbn [map]; f_equal; auto].
Qed.

Lemma fixok_of_an : forall pcf pkf t, allnodes pcf pkf t = true -> fixok pcf pkf t = true.
Proof.
  intros pcf pkf t. induction t using term_ind'; intros H; cbn [allnodes fixok] in *;
    repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [? ?] end;
    repeat (apply andb_true_intro; split); auto.
  rewrite forallb_forall in *. rewrite Forall_forall in IHl. auto.
Qed.

(** Typed terms mention only constants and families the signature has. *)
Lemma typed_an : forall S sg pc pk, (forall g, pc g = false -> sig_type sg g = None) ->
  (forall D, pk D = false -> sig_ind sg D = None) ->
  (forall G t A, has_type S sg G t A -> allnodes pc pk t = true).
Proof.
  intros S sg pc pk Hc Hk.
  assert (H : (forall G, wf_ctx S sg G -> True) /\ (forall G t A, has_type S sg G t A -> allnodes pc pk t = true) /\
              (forall G d ps P cs bs, has_branches S sg G d ps P cs bs -> forallb (allnodes pc pk) bs = true)).
  { apply typing_mutind; intros; cbn [allnodes forallb]; auto;
      repeat match goal with H : ?x = true |- context [?x] => rewrite H end; auto.
    - destruct (pc g) eqn:E; [reflexivity | ]. rewrite (Hc _ E) in e0. discriminate e0.
    - destruct (pk D) eqn:E; [ | rewrite (Hk _ E) in e0; discriminate e0]. cbn [andb].
      repeat match goal with H : ?x = true |- context [?x] => rewrite H end. reflexivity. }
  exact (proj1 (proj2 H)).
Qed.
