(** * Call-by-value evaluation of source programs

    [eval_src] runs a program the way its erasure will run: weakly, by
    value.  It is the source side of the contract of erasure (stage 6
    of erasure-cic) and is separate from the normalizer of conversion
    (PTS.Eval), which reduces under binders and in normal order.

    The strategy:
    - no reduction under λ and inside types: a λ, a [fix], a sort, Π, Σ
      and the primitive types are values as they are;
    - in an application, the function, then the argument, from left to
      right, both to values; then β, or the ι-rule of a full spine of an
      eliminator instance with active rules, or the unfolding of a [fix]
      applied up to its structural argument when that argument is a
      constructor, the same root rules as [whnf];
    - a constructor or a family applied to values is a value, and so are
      an eliminator instance with active rules and a [fix] applied to
      fewer arguments than the arity at which they compute ([head_arity],
      the same arity as their contraction); an instance without active
      rules is an ordinary constant whose spines are neutral, and applied
      it is stuck, as a variable is;
    - a pair evaluates its components from left to right; a projection
      its pair;
    - a [match] and the eliminators of the primitives evaluate the
      scrutinee to a value and continue in the chosen branch; the motive
      and the other branches are not evaluated;
    - δ unfolds a constant, an annotation is dropped.

    There are three answers ([cbv_result] of Common.Outcome, exported
    here): a value, a stuck term (a variable, a
    projection of a non-pair, an eliminator or a [fix] on a value that is
    not a constructor, an application of a non-function or of an
    eliminator instance without active rules), and running
    out of the budget.  The budget counts nested calls, so it bounds the
    depth of the evaluation, not the number of steps: one unit for every
    node, every application of a spine included.

    ** Spines

    [eval_nested] states the strategy one application at a time.  On a
    spine [h a₁ … aₙ] it takes the spine apart at each of its [n]
    applications, and each time it asks whether the head contracts and
    whether the spine is a value, which walks the spine again: the work
    is quadratic in [n].  [eval_src] computes the same function
    ([eval_src_nested]) with one walk of each spine: it takes the spine
    of an application apart once ([spine_rev]), and keeps the value of
    the function part as its head, its arguments (the last one first)
    and the number of arguments its head still takes before its arity
    ([remaining], from [head_arity]).  Each argument takes one off; the
    one that brings it to zero contracts the spine, and only then are
    the arguments put back in order.  No count is compared with an
    arity at each argument, so the work is linear in [n] in the
    extracted code and under [vm_compute], with unary numbers, alike.

    [eval_src_reduces]: a value found by [eval_src] is a reduct of the
    program.  That a well-typed closed program of a type-correct
    signature never gets stuck is a separate obligation, as for normal
    order. *)

From Stdlib Require Import List Relations Bool Arith Lia.
Import ListNotations.
From DepTypes.Common Require Export Outcome.
From DepTypes.PTS Require Import Syntax Signature Reduction SubstLaws.

Section EvalSrc.
Variable sg : signature.
Local Notation "t ⇝ u" := (red1 sg t u).
Local Notation "t ⇝* u" := (red sg t u).

(** A spine that is a value, from its head and the number of its
    arguments: a constructor or a family applied to values, or a head
    applied to fewer arguments than the arity at which it computes.  The
    arity is that of the contraction ([head_arity]), so an instance
    without active rules, which never computes, is never a partial
    application either. *)
Definition is_inert (h : term) : bool :=
  match h with Const (Ctor _ _) | Const (Ind _) => true | _ => false end.

Definition head_value (h : term) (n : nat) : bool :=
  is_inert h || match head_arity sg h with Some m => Nat.ltb n m | None => false end.

Lemma head_arity_inert : forall h m, head_arity sg h = Some m -> is_inert h = false.
Proof. intros h m H. destruct h; try reflexivity. destruct g; try reflexivity; discriminate H. Qed.

(** The arguments a head still takes before its arity: [Some (m - n)]
    for a head of arity [m] applied to [n] arguments, [None] for a head
    without arity. *)
Definition remaining (m : option nat) (n : nat) : option nat :=
  match m with Some m' => Some (m' - n) | None => None end.

Definition spine_value (t : term) : bool := head_value (spine_head t) (length (spine_args t)).

(** ** One node

    Every former but the application, which [app] evaluates; [ev]
    evaluates the subterms with the budget that is left. *)

Definition eval_node (ev : term -> cbv_result term) (app : term -> term -> cbv_result term)
  (t : term) : cbv_result term :=
  match t with
  | Var _ => CbvStuck t
  | Srt _ | Pi _ _ | Sigma _ _ | Lam _ | Void | Unit | Bool | Tt | BTrue | BFalse
  | Fix _ _ _ => CbvValue t
  | Const g =>
      match sig_delta sg g with
      | Some b => ev b
      | None => CbvValue t
      end
  | Ann u _ => ev u
  | App f a => app f a
  | Pair a b =>
      match ev a with
      | CbvValue va =>
          match ev b with
          | CbvValue vb => CbvValue (Pair va vb)
          | r => r
          end
      | r => r
      end
  | Fst p =>
      match ev p with
      | CbvValue (Pair a _) => CbvValue a
      | CbvValue v => CbvStuck (Fst v)
      | r => r
      end
  | Snd p =>
      match ev p with
      | CbvValue (Pair _ b) => CbvValue b
      | CbvValue v => CbvStuck (Snd v)
      | r => r
      end
  | ElimVoid C e =>
      match ev e with
      | CbvValue v => CbvStuck (ElimVoid C v)
      | r => r
      end
  | ElimUnit C c u =>
      match ev u with
      | CbvValue Tt => ev c
      | CbvValue v => CbvStuck (ElimUnit C c v)
      | r => r
      end
  | ElimBool C bt bf b =>
      match ev b with
      | CbvValue BTrue => ev bt
      | CbvValue BFalse => ev bf
      | CbvValue v => CbvStuck (ElimBool C bt bf v)
      | r => r
      end
  | Case D s P x bs =>
      match ev x with
      | CbvValue v =>
          match case_iota sg (Case D s P v bs) with
          | Some r => ev r
          | None => CbvStuck (Case D s P v bs)
          end
      | r => r
      end
  end.

(** ** One application at a time: the specification *)

(** The application of the value [vf] to the value [va]: β, the
    contraction of a spine, or a value or a stuck spine. *)
Definition nested_apply (ev : term -> cbv_result term) (vf va : term) : cbv_result term :=
  match vf with
  | Lam b => ev (subst1 b va)
  | _ =>
      match spine_iota sg (App vf va) with
      | Some r => ev r
      | None => if spine_value (App vf va) then CbvValue (App vf va) else CbvStuck (App vf va)
      end
  end.

(** [App f a]: the function, then the argument, then their application. *)
Definition nested_app (ev : term -> cbv_result term) (f a : term) : cbv_result term :=
  match ev f with
  | CbvValue vf =>
      match ev a with
      | CbvValue va => nested_apply ev vf va
      | r => r
      end
  | r => r
  end.

Fixpoint eval_nested (fuel : nat) (t : term) {struct fuel} : cbv_result term :=
  match fuel with
  | O => CbvOutOfFuel
  | S fuel' => eval_node (eval_nested fuel') (nested_app (eval_nested fuel')) t
  end.

(** ** Whole spines

    The arguments of a spine are kept the last one first and put in
    order by [rev'], which is linear, rather than [rev], which appends
    at every element; [rev'_rev] of PTS.Syntax gives the same list, so the proofs
    reason with [rev]. *)


(** The value of the function part of a spine, or a final answer:
    [SpValue h vs n] is the value [apps h (rev vs)], with [h] not an
    application and [n] the length of [vs]; [SpDone] is a stuck term or a
    timeout. *)
Inductive spine_result : Type :=
| SpValue : term -> list term -> option nat -> spine_result
| SpDone : cbv_result term -> spine_result.

Definition of_cbv (r : cbv_result term) : spine_result :=
  match r with
  | CbvValue v => let (h, vs) := spine_rev v in SpValue h vs (remaining (head_arity sg h) (length vs))
  | CbvStuck u => SpDone (CbvStuck u)
  | CbvOutOfFuel => SpDone CbvOutOfFuel
  end.

Definition to_cbv (r : spine_result) : cbv_result term :=
  match r with
  | SpValue h vs _ => CbvValue (apps h (rev' vs))
  | SpDone r => r
  end.

Definition stuck_spine (h : term) (vs : list term) (va : term) : spine_result :=
  SpDone (CbvStuck (apps h (rev' (va :: vs)))).

(** [vf va], with [vf] the spine [h vs] that takes [r] more arguments
    before the arity of its head.  The argument that completes it
    contracts the spine, and only then are its arguments put in order;
    one short of it leaves a value; past it, or under a head without
    arity that is not a constructor or a family, the spine is stuck. *)
Definition contract_or_stop (ev : term -> cbv_result term) (h : term) (vs : list term) (r : option nat)
  (va : term) : spine_result :=
  match r with
  | Some 1 =>
      match head_iota sg h (rev' (va :: vs)) with
      | Some u => of_cbv (ev u)
      | None => stuck_spine h vs va
      end
  | Some (S (S k)) => SpValue h (va :: vs) (Some (S k))
  | Some 0 => stuck_spine h vs va
  | None => if is_inert h then SpValue h (va :: vs) None else stuck_spine h vs va
  end.

Definition apply_value (ev : term -> cbv_result term) (h : term) (vs : list term) (r : option nat)
  (va : term) : spine_result :=
  match vs, h with
  | [], Lam b => of_cbv (ev (subst1 b va))
  | _, _ => contract_or_stop ev h vs r va
  end.

(** The function part [apps h (rev vs)] of an application: the head
    itself by [ev], a shorter spine by [evs]. *)
Definition eval_fun (ev : term -> cbv_result term) (evs : term -> term -> list term -> spine_result)
  (h : term) (vs : list term) : spine_result :=
  match vs with
  | [] => of_cbv (ev h)
  | a' :: vs' => evs h a' vs'
  end.

(** [App f a] with [f = apps h (rev vs)]: the function, the argument,
    then their application. *)
Definition eval_app (ev : term -> cbv_result term) (evs : term -> term -> list term -> spine_result)
  (h : term) (vs : list term) (a : term) : spine_result :=
  match eval_fun ev evs h vs with
  | SpValue hf vsf nf =>
      match ev a with
      | CbvValue va => apply_value ev hf vsf nf va
      | CbvStuck u => SpDone (CbvStuck u)
      | CbvOutOfFuel => SpDone CbvOutOfFuel
      end
  | SpDone r => SpDone r
  end.

(** [eval_args fuel h a vs] is [eval_src fuel] on the spine
    [apps h (rev (a :: vs))], with a value kept as a spine.  Each of its
    applications takes one unit of the budget, as in [eval_nested]. *)
Fixpoint eval_src (fuel : nat) (t : term) {struct fuel} : cbv_result term :=
  match fuel with
  | O => CbvOutOfFuel
  | S fuel' =>
      eval_node (eval_src fuel')
        (fun f a => let (h, vs) := spine_rev f in
                    to_cbv (eval_app (eval_src fuel') (eval_args fuel') h vs a)) t
  end

with eval_args (fuel : nat) (h a : term) (vs : list term) {struct fuel} : spine_result :=
  match fuel with
  | O => SpDone CbvOutOfFuel
  | S fuel' => eval_app (eval_src fuel') (eval_args fuel') h vs a
  end.

(** ** [eval_src] is [eval_nested] *)

(** A value spine has a head that is not an application, and the
    arguments it still takes; a final answer is not a value. *)
Definition sp_ok (r : spine_result) : Prop :=
  match r with
  | SpValue h vs r => spine_head h = h /\ r = remaining (head_arity sg h) (length vs)
  | SpDone (CbvValue _) => False
  | SpDone _ => True
  end.

Lemma of_cbv_spec : forall r, sp_ok (of_cbv r) /\ to_cbv (of_cbv r) = r.
Proof.
  intros [v | u | ]; [ | split; [exact I | reflexivity] ..].
  unfold of_cbv. rewrite spine_rev_spec. cbn [sp_ok to_cbv].
  split; [split; [apply spine_head_idem | reflexivity] | ].
  rewrite rev'_rev, rev_involutive, apps_spine. reflexivity.
Qed.

Lemma apps_rev_cons : forall h vs a, apps h (rev (a :: vs)) = App (apps h (rev vs)) a.
Proof. intros h vs a. cbn [rev]. apply apps_snoc. Qed.

Lemma contract_or_stop_spec : forall ev h vs r va,
  spine_head h = h -> r = remaining (head_arity sg h) (length vs) ->
  sp_ok (contract_or_stop ev h vs r va) /\
  to_cbv (contract_or_stop ev h vs r va) =
  match spine_iota sg (apps h (rev (va :: vs))) with
  | Some u => ev u
  | None =>
      if spine_value (apps h (rev (va :: vs))) then CbvValue (apps h (rev (va :: vs)))
      else CbvStuck (apps h (rev (va :: vs)))
  end.
Proof.
  intros ev h vs r va Hh Hr.
  assert (Hhd : spine_head (apps h (rev (va :: vs))) = h) by (rewrite spine_head_apps; exact Hh).
  assert (Har : spine_args (apps h (rev (va :: vs))) = rev (va :: vs))
    by (rewrite spine_args_apps, (spine_head_args h Hh); reflexivity).
  assert (Hlen : length (rev (va :: vs)) = S (length vs)) by (rewrite length_rev; reflexivity).
  rewrite spine_iota_head. unfold spine_value, head_value. rewrite Hhd, Har, Hlen.
  assert (Hst : sp_ok (stuck_spine h vs va) /\ to_cbv (stuck_spine h vs va) = CbvStuck (apps h (rev (va :: vs))))
    by (unfold stuck_spine; cbn [sp_ok to_cbv]; rewrite rev'_rev; split; [exact I | reflexivity]).
  unfold contract_or_stop. subst r.
  destruct (head_arity sg h) as [m|] eqn:Ha; cbn [remaining].
  - rewrite (head_arity_inert _ _ Ha). cbn [orb].
    destruct (m - length vs) as [|[|k]] eqn:E.
    + replace (Nat.eqb (S (length vs)) m) with false by (symmetry; apply Nat.eqb_neq; lia).
      replace (Nat.ltb (S (length vs)) m) with false by (symmetry; apply Nat.ltb_ge; lia). exact Hst.
    + replace (Nat.eqb (S (length vs)) m) with true by (symmetry; apply Nat.eqb_eq; lia).
      rewrite rev'_rev. destruct (head_iota sg h (rev (va :: vs))) as [u|]; [exact (of_cbv_spec (ev u)) | ].
      replace (Nat.ltb (S (length vs)) m) with false by (symmetry; apply Nat.ltb_ge; lia). exact Hst.
    + replace (Nat.eqb (S (length vs)) m) with false by (symmetry; apply Nat.eqb_neq; lia).
      replace (Nat.ltb (S (length vs)) m) with true by (symmetry; apply Nat.ltb_lt; lia).
      cbn [sp_ok to_cbv]. rewrite rev'_rev.
      split; [split; [exact Hh | rewrite Ha; cbn [remaining length]; f_equal; lia] | reflexivity].
  - rewrite orb_false_r. destruct (is_inert h); [ | exact Hst].
    cbn [sp_ok to_cbv]. rewrite rev'_rev. split; [split; [exact Hh | rewrite Ha; reflexivity] | reflexivity].
Qed.

Lemma apply_value_spec : forall ev h vs r va,
  spine_head h = h -> r = remaining (head_arity sg h) (length vs) ->
  sp_ok (apply_value ev h vs r va) /\
  to_cbv (apply_value ev h vs r va) = nested_apply ev (apps h (rev vs)) va.
Proof.
  intros ev h vs r va Hh Hr.
  pose proof (contract_or_stop_spec ev h vs r va Hh Hr) as Hc. rewrite apps_rev_cons in Hc.
  destruct vs as [|a' vs'].
  - destruct h; try exact Hc. exact (of_cbv_spec _).
  - unfold nested_apply. rewrite apps_rev_cons in Hc |- *. exact Hc.
Qed.

Lemma eval_app_spec : forall ev evs h vs a,
  (forall h a vs, sp_ok (evs h a vs) /\ to_cbv (evs h a vs) = ev (apps h (rev (a :: vs)))) ->
  sp_ok (eval_app ev evs h vs a) /\ to_cbv (eval_app ev evs h vs a) = nested_app ev (apps h (rev vs)) a.
Proof.
  intros ev evs h vs a Hevs.
  assert (Hf : sp_ok (eval_fun ev evs h vs) /\ to_cbv (eval_fun ev evs h vs) = ev (apps h (rev vs))).
  { destruct vs as [|a' vs']; [exact (of_cbv_spec (ev h)) | exact (Hevs h a' vs')]. }
  unfold eval_app, nested_app. destruct Hf as [Hok Hf].
  destruct (eval_fun ev evs h vs) as [hf vsf nf | r]; cbn [to_cbv] in Hf; rewrite ?rev'_rev in Hf; rewrite <- Hf.
  - destruct Hok as [Hh Hn].
    destruct (ev a) as [va | u | ]; [ | split; [exact I | reflexivity] ..].
    exact (apply_value_spec ev hf vsf nf va Hh Hn).
  - destruct r as [v | u | ]; [destruct Hok | split; [exact I | reflexivity] ..].
Qed.

(** Two evaluations that agree on the subterms agree on the node: the
    results bound by the branches are taken apart first. *)
Ltac agree H :=
  cbv beta iota; rewrite ?H;
  first [ reflexivity
        | lazymatch goal with |- context [match ?x with _ => _ end] => destruct x end; agree H ].

Lemma nested_app_ext : forall ev ev' f a, (forall u, ev u = ev' u) ->
  nested_app ev f a = nested_app ev' f a.
Proof. intros ev ev' f a H. unfold nested_app, nested_apply. agree H. Qed.

Lemma eval_node_ext : forall ev ev' app app' t,
  (forall u, ev u = ev' u) -> (forall f a, app f a = app' f a) ->
  eval_node ev app t = eval_node ev' app' t.
Proof. intros ev ev' app app' t H Happ. unfold eval_node. destruct t; rewrite ?Happ; agree H. Qed.

Theorem eval_src_nested : forall fuel,
  (forall t, eval_src fuel t = eval_nested fuel t) /\
  (forall h a vs, sp_ok (eval_args fuel h a vs) /\
                  to_cbv (eval_args fuel h a vs) = eval_nested fuel (apps h (rev (a :: vs)))).
Proof.
  induction fuel as [|fuel [IHt IHa]].
  - split; [reflexivity | intros h a vs; split; [exact I | reflexivity]].
  - assert (Happ : forall h vs a,
               sp_ok (eval_app (eval_src fuel) (eval_args fuel) h vs a) /\
               to_cbv (eval_app (eval_src fuel) (eval_args fuel) h vs a) =
               nested_app (eval_nested fuel) (apps h (rev vs)) a).
    { intros h vs a. rewrite <- (nested_app_ext (eval_src fuel) (eval_nested fuel)) by exact IHt.
      apply eval_app_spec. intros h' a' vs'. rewrite IHt. apply IHa. }
    split.
    + intros t. cbn [eval_src eval_nested]. apply eval_node_ext; [exact IHt | ].
      intros f a. rewrite spine_rev_spec. cbv beta iota.
      rewrite (proj2 (Happ _ _ _)), rev_involutive, apps_spine. reflexivity.
    + intros h a vs. cbn [eval_args]. destruct (Happ h vs a) as [Hok Ht].
      split; [exact Hok | ]. rewrite Ht, apps_rev_cons. reflexivity.
Qed.

(** ** A value is a reduct *)

Theorem eval_nested_reduces : forall fuel t v, eval_nested fuel t = CbvValue v -> t ⇝* v.
Proof.
  induction fuel as [|fuel IH]; intros t v H; [discriminate H | ].
  destruct t; cbn [eval_nested] in H; cbv beta iota delta [eval_node nested_app nested_apply] in H;
    try (injection H as <-; apply rt_refl); try discriminate H.
  (* App *)
  - destruct (eval_nested fuel t1) as [vf| |] eqn:Ef; try discriminate H.
    destruct (eval_nested fuel t2) as [va| |] eqn:Ea; try discriminate H.
    apply IH in Ef. apply IH in Ea.
    apply rt_trans with (App vf va); [apply red_app; assumption | ].
    destruct vf.
    all: lazymatch type of H with
         | match spine_iota sg ?u with _ => _ end = _ =>
             destruct (spine_iota sg u) as [r|] eqn:Ei;
             [ apply IH in H; exact (red_step_trans _ _ _ (spine_iota_red _ _ Ei) H)
             | destruct (spine_value u); [injection H as <-; apply rt_refl | discriminate H] ]
         | _ => apply IH in H; exact (red_step_trans _ _ _ (R_Beta _ _ _) H)
         end.
  (* Ann *)
  - apply IH in H. exact (red_step_trans _ _ _ (R_Ann _ _ _) H).
  (* ElimVoid *)
  - destruct (eval_nested fuel t2); discriminate H.
  (* ElimUnit *)
  - destruct (eval_nested fuel t3) as [vu| |] eqn:Eu; try discriminate H.
    apply IH in Eu. destruct vu; try discriminate H. apply IH in H.
    apply rt_trans with (ElimUnit t1 t2 Tt); [apply red_elim_unit; [apply rt_refl | apply rt_refl | exact Eu] | ].
    exact (red_step_trans _ _ _ (R_UnitTt _ _ _) H).
  (* ElimBool *)
  - destruct (eval_nested fuel t4) as [vb| |] eqn:Eb; try discriminate H.
    apply IH in Eb. destruct vb; try discriminate H; apply IH in H.
    + apply rt_trans with (ElimBool t1 t2 t3 BTrue); [apply red_elim_bool; first [exact Eb | apply rt_refl] | ].
      exact (red_step_trans _ _ _ (R_BoolTrue _ _ _ _) H).
    + apply rt_trans with (ElimBool t1 t2 t3 BFalse); [apply red_elim_bool; first [exact Eb | apply rt_refl] | ].
      exact (red_step_trans _ _ _ (R_BoolFalse _ _ _ _) H).
  (* Pair *)
  - destruct (eval_nested fuel t1) as [va| |] eqn:Ea; try discriminate H.
    destruct (eval_nested fuel t2) as [vb| |] eqn:Eb; try discriminate H.
    injection H as <-. apply red_pair; apply IH; assumption.
  (* Fst *)
  - destruct (eval_nested fuel t) as [vp| |] eqn:Ep; try discriminate H.
    destruct vp; try discriminate H. injection H as <-. apply IH in Ep.
    apply rt_trans with (Fst (Pair vp1 vp2)); [apply red_fst, Ep | apply rt_step, R_FstPair].
  (* Snd *)
  - destruct (eval_nested fuel t) as [vp| |] eqn:Ep; try discriminate H.
    destruct vp; try discriminate H. injection H as <-. apply IH in Ep.
    apply rt_trans with (Snd (Pair vp1 vp2)); [apply red_snd, Ep | apply rt_step, R_SndPair].
  (* Const *)
  - destruct (sig_delta sg g) as [b|] eqn:Ed; [ | injection H as <-; apply rt_refl].
    apply IH in H. exact (red_step_trans _ _ _ (R_Delta _ _ _ Ed) H).
  (* Case *)
  - destruct (eval_nested fuel t2) as [vx| |] eqn:Ex; try discriminate H.
    destruct (case_iota sg (Case s s0 t1 vx l)) as [r|] eqn:Ei; [ | discriminate H].
    apply IH in Ex. apply IH in H.
    apply rt_trans with (Case s s0 t1 vx l).
    + apply red_case; [apply rt_refl | exact Ex | apply red_list_refl].
    + exact (red_step_trans _ _ _ (R_Case _ _ _ Ei) H).
Qed.

Theorem eval_src_reduces : forall fuel t v, eval_src fuel t = CbvValue v -> t ⇝* v.
Proof.
  intros fuel t v H. rewrite (proj1 (eval_src_nested fuel)) in H.
  exact (eval_nested_reduces fuel t v H).
Qed.
End EvalSrc.

Arguments eval_src_nested {sg}.
Arguments eval_nested_reduces {sg}.
Arguments eval_src_reduces {sg}.
