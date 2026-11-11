(** * Substitution under the binders of a telescope

    A telescope is a list of types, outermost first, each in the context
    of the ones before it, as [pis] of PTS.Syntax takes it.  The
    descriptions of a signature (PTS.Signature) lie under such
    telescopes: the parameters, the fields of a constructor, the domains
    of a recursive field.

    [upn m sb] is the substitution [sb] under [m] binders, and
    [subst_tele sb Ts] substitutes in a telescope, each entry under the
    ones before it.  They are the specification.  The kernel computes
    with an environment instead ([inst]): the values of the free
    variables as a list, innermost first, put under [m] binders by a
    single [lift m], where [upn m] lifts [m] times.  [inst_upn] and
    [inst_tele_subst] of PTS.SubstLaws prove the two forms equal.

    [params_env] reverses the parameters of a type once, so that a
    telescope under them ([inst_tele]) or the type of a branch of a match
    does not reverse them again for each entry.

    [tsub args] substitutes the arguments of a telescope for all its
    variables at once; its laws with substitution are in PTS.SubstLaws. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From DepTypes.PTS Require Import Syntax.

(** ** The specification *)

(** [upn m sb]: [sb] under [m] binders. *)
Fixpoint upn (m : nat) (sb : nat -> term) : nat -> term :=
  match m with
  | 0 => sb
  | S m' => up_sub (upn m' sb)
  end.

Lemma upn_lt : forall m sb n, n < m -> upn m sb n = Var n.
Proof.
  induction m as [|m IH]; intros sb n H; [lia | ].
  destruct n as [|n]; cbn; [reflexivity | ]. rewrite IH by lia. reflexivity.
Qed.

(** Substitutes in a telescope: each entry under the entries before it. *)
Fixpoint subst_tele (sb : nat -> term) (Ts : list term) : list term :=
  match Ts with
  | [] => []
  | T :: Ts' => subst sb T :: subst_tele (up_sub sb) Ts'
  end.

(** ** Environments *)

(** The values of the free variables, innermost first, under [m] binders. *)
Definition inst (m : nat) (env : list term) : nat -> term :=
  fun n => if Nat.ltb n m then Var n else lift m (nth (n - m) env (Var 0)).

(** The parameters [ps], outermost first, as an environment, innermost
    first. *)
Definition params_env (ps : list term) : list term := rev_append ps [].

Lemma params_env_rev : forall ps, params_env ps = rev ps.
Proof. intros ps. symmetry. apply rev_alt. Qed.

(** A term under the parameters and [m] more binders, with the
    parameters substituted: [env] is [params_env ps]. *)
Definition inst_env (env : list term) (m : nat) (t : term) : term := subst (inst m env) t.

Definition inst_params (ps : list term) (m : nat) (t : term) : term := inst_env (params_env ps) m t.

(** A telescope under the parameters and [m] more binders, each entry
    under the ones before it. *)
Fixpoint inst_tele_env (env : list term) (m : nat) (Ts : list term) : list term :=
  match Ts with
  | [] => []
  | T :: Ts' => inst_env env m T :: inst_tele_env env (S m) Ts'
  end.

Definition inst_tele (ps : list term) (m : nat) (Ts : list term) : list term :=
  inst_tele_env (params_env ps) m Ts.

(** ** Lengths and maps *)

Lemma params_env_map : forall f ps, params_env (map f ps) = map f (params_env ps).
Proof. intros f ps. rewrite !params_env_rev. symmetry. apply map_rev. Qed.

Lemma params_env_length : forall ps, length (params_env ps) = length ps.
Proof. intros ps. rewrite params_env_rev. apply length_rev. Qed.

Lemma inst_tele_env_length : forall env m Ts, length (inst_tele_env env m Ts) = length Ts.
Proof. intros env m Ts. revert m. induction Ts as [|T Ts IH]; intros m; cbn; [reflexivity | now rewrite IH]. Qed.

Lemma subst_tele_length : forall Ts sb, length (subst_tele sb Ts) = length Ts.
Proof. induction Ts as [|T Ts IH]; intros sb; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

(** ** Telescopes substituted at once *)

(** [tsub args]: the arguments of a telescope for its variables, the last
    one for [Var 0]; the variables outside it go down past them. *)
Definition tsub (args : list term) : nat -> term :=
  fun i => nth i (rev args) (Var (i - length args)).

Lemma tsub_nil : forall i, tsub [] i = Var i.
Proof. intros [|i]; reflexivity. Qed.

Lemma tsub_lt : forall a args i, i < length args -> tsub (a :: args) i = tsub args i.
Proof.
  intros a args i H. unfold tsub. cbn [rev]. rewrite app_nth1 by (rewrite length_rev; exact H).
  apply nth_indep. rewrite length_rev. exact H.
Qed.

(** ** Telescopes of terms with allowed constants and matches *)

Lemma an_inst_tele_env : forall pc pk Ts env m, Forall (fun T => allnodes pc pk T = true) Ts ->
  forallb (allnodes pc pk) env = true -> forallb (allnodes pc pk) (inst_tele_env env m Ts) = true.
Proof.
  intros pc pk Ts. induction Ts as [|T Ts IH]; intros env m HT Henv; [reflexivity | ].
  inversion HT as [|? ? H1 H2]; subst. cbn [inst_tele_env forallb]. apply andb_true_intro. split; [ | apply IH; assumption].
  unfold inst_env. apply an_subst; [exact H1 | ]. intros n. unfold inst. destruct (Nat.ltb n m); [reflexivity | ].
  rewrite an_lift. destruct (nth_error env (n - m)) as [e|] eqn:Ee.
  - rewrite (nth_error_nth _ _ _ Ee). rewrite forallb_forall in Henv. exact (Henv e (nth_error_In _ _ Ee)).
  - rewrite nth_overflow by (apply nth_error_None; exact Ee). reflexivity.
Qed.

Lemma an_params_env : forall pc pk ps, forallb (allnodes pc pk) ps = true -> forallb (allnodes pc pk) (params_env ps) = true.
Proof. intros pc pk ps H. rewrite params_env_rev, forallb_forall. intros x Hx. apply in_rev in Hx. rewrite forallb_forall in H. auto. Qed.
