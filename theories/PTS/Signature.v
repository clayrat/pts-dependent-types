(** * Signatures: the global environment of constants

    A signature lists the constants a term may mention, newest first:
    - an inductive family D with its constructors, given by a classified
      description;
    - an instance [Elim D j] of its eliminator: its closed type and the
      flag of active ι-rules;
    - a δ-constant [Def f]: its closed type and body.

    The kernel only stores and looks up entries.  Classifying a
    declaration (the check of strict positivity), generating the types of
    eliminators and checking every entry belong to the procedures that
    register them; the checker never creates an entry, and a constant
    missing from the signature it is given is rejected.

    ** Descriptions

    A declaration [data D (Δ) : Πθ̄:Θ̄. Type_i where c₁ : con … c_k : con]
    is stored classified, after Dybjer's schema: every field of a
    constructor is either non-recursive, [FArg A], or recursive,
    [FRec B̄ v̄] for the field [r : Πȳ:B̄. D Δ v̄].  D itself does not occur
    in a description; the types of D and of its constructors are rebuilt
    from it ([ind_type], [ctor_type]).

    Telescopes are lists, outermost entry first, each entry in the context
    of the ones before it: the parameters Δ; the indices Θ̄ under Δ; the
    fields of a constructor under Δ; the domains B̄ of a recursive field
    under Δ and the previous fields, and its indices v̄ under these and ȳ;
    the result indices ū of a constructor under Δ and all its fields.

    ** Computation

    A signature contributes two contractions at the root:
    - δ: [Const (Def f) ⇝ body];
    - ι: an instance with active rules, applied to its full spine
      [elim_D[j] Δ P m̄ ū x] with [x] a constructor spine [c_k Δ' ā],
      contracts to [m_k args(ā, ih̄)]: a non-recursive field contributes
      its argument, a recursive field [r : Πȳ:B̄. D Δ v̄] the argument and,
      right after it, its hypothesis [λȳ. elim_D[j] Δ P m̄ v̄ (r ȳ)].  This
      is the order of [nat_rect]; the parameters of the hypotheses and of
      v̄ are those of the eliminator.

    An instance without the flag is an ordinary constant: its spines are
    neutral, so its rules can be checked before they take part in
    evaluation and conversion.

    The invariant carried by [signature] is closedness: types and bodies
    are closed, and every term of a description mentions only its
    telescope.  It makes δ and ι commute with substitution
    (PTS.SubstLaws). *)

From Stdlib Require Import List Bool Arith.
From Stdlib Require String.
Import ListNotations.
From DepTypes.PTS Require Import Syntax.

Local Notation string := String.string.

(** ** Classified descriptions *)

Inductive field : Type :=
| FArg : term -> field                     (** a non-recursive field: its type *)
| FRec : list term -> list term -> field.  (** [Πȳ:B̄. D Δ v̄]: the domains B̄, the indices v̄ *)

Record ctor_desc : Type := mk_ctor {
  ctor_name : string;
  ctor_fields : list field;
  ctor_indices : list term;
}.

Record ind_desc : Type := mk_ind {
  ind_name : string;
  ind_params : list term;
  ind_indices : list term;
  ind_level : nat;
  ind_ctors : list ctor_desc;
}.

Inductive entry : Type :=
| EInd : ind_desc -> entry
| EElim : string -> nat -> term -> bool -> entry   (** D, j, the type, active ι-rules *)
| EDef : string -> term -> term -> entry.          (** f, the type, the body *)

(** ** The types of a declaration *)

(** The type of a field at position [l], after the [p] parameters: a
    recursive field applies D to the parameters, which lie past its
    domains and the [l] previous fields. *)
Definition field_type (D : string) (p l : nat) (fd : field) : term :=
  match fd with
  | FArg A => A
  | FRec Bs vs => pis Bs (apps (Const (Ind D)) (vars (length Bs + l) p ++ vs))
  end.

Fixpoint field_types (D : string) (p l : nat) (fs : list field) : list term :=
  match fs with
  | [] => []
  | fd :: fs' => field_type D p l fd :: field_types D p (S l) fs'
  end.

(** [D : Π(Δ). Πθ̄:Θ̄. Type_i] *)
Definition ind_type (d : ind_desc) : term :=
  pis (ind_params d ++ ind_indices d) (Srt (Univ (ind_level d))).

(** [c : Π(Δ). Π(fields). D Δ ū] *)
Definition ctor_type (d : ind_desc) (c : ctor_desc) : term :=
  let p := length (ind_params d) in
  pis (ind_params d ++ field_types (ind_name d) p 0 (ctor_fields c))
      (apps (Const (Ind (ind_name d))) (vars (length (ctor_fields c)) p ++ ctor_indices c)).

(** [elim_D[j] Δ P m̄ θ̄ x]: parameters, motive, one method per
    constructor, indices and the object. *)
Definition elim_arity (d : ind_desc) : nat :=
  length (ind_params d) + 1 + length (ind_ctors d) + length (ind_indices d) + 1.

(** ** Closedness *)

Fixpoint tele_closed (k : nat) (As : list term) : bool :=
  match As with
  | [] => true
  | A :: As' => closed_above k A && tele_closed (S k) As'
  end.

(** [k]: the parameters and the previous fields. *)
Definition field_closed (k : nat) (fd : field) : bool :=
  match fd with
  | FArg A => closed_above k A
  | FRec Bs vs => tele_closed k Bs && forallb (closed_above (k + length Bs)) vs
  end.

Fixpoint fields_closed (k : nat) (fs : list field) : bool :=
  match fs with
  | [] => true
  | fd :: fs' => field_closed k fd && fields_closed (S k) fs'
  end.

Definition ctor_closed (p : nat) (c : ctor_desc) : bool :=
  fields_closed p (ctor_fields c) &&
  forallb (closed_above (p + length (ctor_fields c))) (ctor_indices c).

Definition ind_closed (d : ind_desc) : bool :=
  let p := length (ind_params d) in
  tele_closed 0 (ind_params d) && tele_closed p (ind_indices d) &&
  forallb (ctor_closed p) (ind_ctors d).

Definition entry_closed (e : entry) : bool :=
  match e with
  | EInd d => ind_closed d
  | EElim _ _ A _ => closed A
  | EDef _ A b => closed A && closed b
  end.

Definition entries_closed (es : list entry) : bool := forallb entry_closed es.

(** ** Signatures *)

Record signature : Type := {
  sig_entries : list entry;
  sig_wf : entries_closed sig_entries = true;
}.

Definition sig_empty : signature := {| sig_entries := []; sig_wf := eq_refl |}.

Notation "∅" := sig_empty.

(** Extends a signature by a newer entry, if it is closed.  Only the new
    entry is checked: the older ones are closed by [sig_wf]. *)
Lemma entries_closed_cons : forall sg e,
  entry_closed e = true -> entries_closed (e :: sig_entries sg) = true.
Proof. intros sg e H. cbn. rewrite H. exact (sig_wf sg). Qed.

Definition sig_add (sg : signature) (e : entry) : option signature :=
  match entry_closed e as b return entry_closed e = b -> option signature with
  | true => fun H => Some {| sig_entries := e :: sig_entries sg; sig_wf := entries_closed_cons sg e H |}
  | false => fun _ => None
  end eq_refl.

(** ** Lookup

    The newest entry of a name wins: an instance registered again with
    active rules shadows its earlier copy. *)

Fixpoint find_ind (es : list entry) (D : string) : option ind_desc :=
  match es with
  | [] => None
  | EInd d :: es' => if String.eqb (ind_name d) D then Some d else find_ind es' D
  | _ :: es' => find_ind es' D
  end.

Fixpoint find_elim (es : list entry) (D : string) (j : nat) : option (term * bool) :=
  match es with
  | [] => None
  | EElim D' j' A act :: es' =>
      if String.eqb D' D && Nat.eqb j' j then Some (A, act) else find_elim es' D j
  | _ :: es' => find_elim es' D j
  end.

Fixpoint find_def (es : list entry) (f : string) : option (term * term) :=
  match es with
  | [] => None
  | EDef f' A b :: es' => if String.eqb f' f then Some (A, b) else find_def es' f
  | _ :: es' => find_def es' f
  end.

(** The position of a constructor among those of its type. *)
Fixpoint find_ctor (cs : list ctor_desc) (c : string) : option (nat * ctor_desc) :=
  match cs with
  | [] => None
  | cd :: cs' =>
      if String.eqb (ctor_name cd) c then Some (0, cd)
      else option_map (fun r => (S (fst r), snd r)) (find_ctor cs' c)
  end.

Section Lookup.
  Variable sg : signature.

  Definition sig_ind (D : string) : option ind_desc := find_ind (sig_entries sg) D.
  Definition sig_elim (D : string) (j : nat) : option (term * bool) := find_elim (sig_entries sg) D j.
  Definition sig_def (f : string) : option (term * term) := find_def (sig_entries sg) f.

  (** The closed type of a constant. *)
  Definition sig_type (g : gref) : option term :=
    match g with
    | Ind D => option_map ind_type (sig_ind D)
    | Ctor D c =>
        match sig_ind D with
        | Some d => option_map (fun r => ctor_type d (snd r)) (find_ctor (ind_ctors d) c)
        | None => None
        end
    | Elim D j => option_map fst (sig_elim D j)
    | Def f => option_map fst (sig_def f)
    end.

  (** δ: the body of a δ-constant. *)
  Definition sig_delta (g : gref) : option term :=
    match g with
    | Def f => option_map snd (sig_def f)
    | _ => None
    end.

  (** ** ι by the scheme of descriptions *)

  (** An instance with active rules applied to its full arity: the type
      it eliminates and its description. *)
  Definition elim_view (t : term) : option (string * nat * ind_desc) :=
    match spine_head t with
    | Const (Elim D j) =>
        match sig_elim D j, sig_ind D with
        | Some (_, true), Some d =>
            if Nat.eqb (length (spine_args t)) (elim_arity d) then Some (D, j, d) else None
        | _, _ => None
        end
    | _ => None
    end.

  Definition full_elim (t : term) : bool :=
    match elim_view t with Some _ => true | None => false end.
End Lookup.

(** The substitution instantiating the indices v̄ of a recursive field
    under its [m] positions ȳ: [env] holds the previous fields and the
    parameters, innermost first. *)
Definition inst (m : nat) (env : list term) : nat -> term :=
  fun n => if Nat.ltb n m then Var n else lift m (nth (n - m) env (Var 0)).

(** The hypothesis of a recursive field [a : Πȳ:B̄. D Δ v̄]:
    [λȳ. elim_D[j] Δ P m̄ v̄ (a ȳ)], where [pre] are the parameters,
    motive and methods of the eliminator. *)
Definition hyp (D : string) (j : nat) (pre env Bs vs : list term) (a : term) : term :=
  let m := length Bs in
  lams m (apps (Const (Elim D j))
    (map (lift m) pre ++ map (subst (inst m env)) vs ++ [apps (lift m a) (vars 0 m)])).

(** The arguments of a method: each field, and after a recursive one its
    hypothesis. *)
Fixpoint iota_args (D : string) (j : nat) (pre env : list term) (fs : list field) (xs : list term)
  : list term :=
  match fs, xs with
  | FArg _ :: fs', a :: xs' => a :: iota_args D j pre (a :: env) fs' xs'
  | FRec Bs vs :: fs', a :: xs' => a :: hyp D j pre env Bs vs a :: iota_args D j pre (a :: env) fs' xs'
  | _, _ => []
  end.

Section Iota.
  Variable sg : signature.

  (** The ι-contraction of a full spine on a constructor spine of its
      type, with the right number of arguments. *)
  Definition iota (t : term) : option term :=
    match elim_view sg t with
    | Some (D, j, d) =>
        let p := length (ind_params d) in
        let k := length (ind_ctors d) in
        let a := spine_args t in
        let x := last a (Var 0) in
        match spine_head x with
        | Const (Ctor D' c) =>
            if String.eqb D' D then
              match find_ctor (ind_ctors d) c with
              | Some (i, cd) =>
                  let xa := spine_args x in
                  if Nat.eqb (length xa) (p + length (ctor_fields cd)) then
                    match nth_error (firstn k (skipn (S p) a)) i with
                    | Some m =>
                        Some (apps m (iota_args D j (firstn (S p + k) a) (rev (firstn p a))
                                        (ctor_fields cd) (skipn p xa)))
                    | None => None
                    end
                  else None
              | None => None
              end
            else None
        | _ => None
        end
    | None => None
    end.
End Iota.

(** ** What the invariant gives *)

Lemma find_ind_closed : forall es D d,
  entries_closed es = true -> find_ind es D = Some d -> ind_closed d = true.
Proof.
  induction es as [|e es IH]; intros D d Hc H; [discriminate H | ].
  cbn in Hc. apply andb_prop in Hc as [He Hc].
  destruct e as [d'| | ]; cbn in H; try exact (IH _ _ Hc H).
  destruct (String.eqb (ind_name d') D); [injection H as <-; exact He | exact (IH _ _ Hc H)].
Qed.

Lemma find_def_closed : forall es f A b,
  entries_closed es = true -> find_def es f = Some (A, b) -> closed A = true /\ closed b = true.
Proof.
  induction es as [|e es IH]; intros f A b Hc H; [discriminate H | ].
  cbn in Hc. apply andb_prop in Hc as [He Hc].
  destruct e as [ | | f' A' b']; cbn in H; try exact (IH _ _ _ Hc H).
  destruct (String.eqb f' f); [ | exact (IH _ _ _ Hc H)].
  injection H as <- <-. exact (andb_prop _ _ He).
Qed.

Lemma find_ctor_closed : forall p cs c i cd,
  forallb (ctor_closed p) cs = true -> find_ctor cs c = Some (i, cd) -> ctor_closed p cd = true.
Proof.
  induction cs as [|cd' cs IH]; intros c i cd Hc H; [discriminate H | ].
  cbn in Hc. apply andb_prop in Hc as [He Hc]. cbn in H.
  destruct (String.eqb (ctor_name cd') c); [injection H as _ <-; exact He | ].
  destruct (find_ctor cs c) as [[i' cd'']|] eqn:E; [ | discriminate H].
  injection H as _ <-. exact (IH _ _ _ Hc E).
Qed.

Lemma sig_delta_closed : forall sg g b, sig_delta sg g = Some b -> closed b = true.
Proof.
  intros sg g b H. destruct g as [ | | | f]; try discriminate H. cbn in H.
  unfold sig_def in H. destruct (find_def (sig_entries sg) f) as [[A b']|] eqn:E; [ | discriminate H].
  injection H as <-. exact (proj2 (find_def_closed _ _ _ _ (sig_wf sg) E)).
Qed.

Lemma elim_view_spec : forall sg t D j d, elim_view sg t = Some (D, j, d) ->
  spine_head t = Const (Elim D j) /\ length (spine_args t) = elim_arity d /\ ind_closed d = true.
Proof.
  intros sg t D j d H. unfold elim_view in H.
  destruct (spine_head t) eqn:Eh; try discriminate H. destruct g; try discriminate H.
  destruct (sig_elim sg s n) as [[A [|]]|]; try discriminate H.
  destruct (sig_ind sg s) as [d'|] eqn:Ed; try discriminate H.
  destruct (Nat.eqb (length (spine_args t)) (elim_arity d')) eqn:El; try discriminate H.
  injection H as <- <- <-. apply Nat.eqb_eq in El.
  repeat split; [assumption | exact (find_ind_closed _ _ _ (sig_wf sg) Ed)].
Qed.

Lemma iota_full_elim : forall sg t u, iota sg t = Some u -> full_elim sg t = true.
Proof.
  intros sg t u H. unfold iota in H. unfold full_elim.
  destruct (elim_view sg t); [reflexivity | discriminate H].
Qed.

(** A β-redex is no spine of a constant. *)
Lemma elim_view_lam : forall sg b u, elim_view sg (App (Lam b) u) = None.
Proof. reflexivity. Qed.

Lemma iota_lam : forall sg b u, iota sg (App (Lam b) u) = None.
Proof. reflexivity. Qed.

(** An ι-redex is an application: its spine has the full arity. *)
Lemma iota_app : forall sg t u, iota sg t = Some u -> exists f a, t = App f a.
Proof.
  intros sg t u H. unfold iota in H.
  destruct (elim_view sg t) as [[[D j] d]|] eqn:Ev; [ | discriminate H].
  destruct (elim_view_spec _ _ _ _ _ Ev) as (_ & Hlen & _).
  destruct t; try (eexists; eexists; reflexivity).
  all: cbn in Hlen; unfold elim_arity in Hlen; rewrite Nat.add_1_r in Hlen; discriminate Hlen.
Qed.
