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
    does not reverse them again for each entry. *)

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
