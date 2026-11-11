(** * Signatures: the global environment of constants

    A signature lists the constants a term may mention, newest first:
    - an inductive family D with its constructors, given by a classified
      description;
    - an instance [Elim D s] of its eliminator, for motives into the sort
      [s]: its closed type and the flag of active ι-rules;
    - a δ-constant [Def f]: its closed type and body.

    The kernel only stores and looks up entries.  Classifying a
    declaration (the check of strict positivity), generating the types of
    eliminators and checking every entry belong to the procedures that
    register them; the checker never creates an entry, and a constant
    missing from the signature it is given is rejected.

    ** Descriptions

    A declaration [data D (Δ) : Πθ̄:Θ̄. s where c₁ : con … c_k : con],
    with [s] a sort, [Type_i] or [Prop], is stored classified, after
    Dybjer's schema: every field of a constructor is either non-recursive,
    [FArg A], or recursive, [FRec B̄ v̄] for the field
    [r : Πȳ:B̄. D Δ v̄].  D itself does not occur in a description; the
    types of D and of its constructors are rebuilt from it ([ind_type],
    [ctor_type]).

    A description also stores the sorts its eliminators may target, its
    category [elim_class]: every sort of the table ([AllSorts]), or Prop
    alone ([PropOnly]).  The registration computes it from the sort of D
    and the sorts of the fields; the kernel stores it and answers
    [allows_elimination], the one check of the sort of a motive.  A
    category rather than a list: Type has infinitely many levels.

    Telescopes are lists, outermost entry first, each entry in the context
    of the ones before it: the parameters Δ; the indices Θ̄ under Δ; the
    fields of a constructor under Δ; the domains B̄ of a recursive field
    under Δ and the previous fields, and its indices v̄ under these and ȳ;
    the result indices ū of a constructor under Δ and all its fields.

    ** Computation

    A signature contributes two contractions at the root:
    - δ: [Const (Def f) ⇝ body];
    - ι: an instance with active rules, applied to its full spine
      [elim_D[s] Δ P m̄ ū x] with [x] a constructor spine [c_k Δ' ā],
      contracts to [m_k args(ā, ih̄)]: a non-recursive field contributes
      its argument, a recursive field [r : Πȳ:B̄. D Δ v̄] the argument and,
      right after it, its hypothesis [λȳ. elim_D[s] Δ P m̄ v̄ (r ȳ)].  This
      is the order of [nat_rect]; the parameters of the hypotheses and of
      v̄ are those of the eliminator.

    An instance without the flag is an ordinary constant: its spines are
    neutral, so its rules can be checked before they take part in
    evaluation and conversion.

    ** match and fix

    The primitive [match] of PTS.Syntax computes by the description too:
    [Case D s P (c_i Δ' ā) bs ⇝ b_i ā], the branch of the position of
    [c_i] applied to the fields, the parameters skipped ([case_iota]).
    [fix] does not need the signature, but it computes like an
    eliminator: [Fix A k b] applied to [k + 1] arguments, the last one a
    constructor spine, unfolds to [b[Fix A k b/0]] applied to them
    ([fix_unfold]).  The spines contracted at their last argument, a full
    spine of an instance or a [fix] up to its structural argument, are
    scanned from that argument by the evaluators ([full_spine],
    [spine_iota]).  [head_arity] and [head_iota] give the same
    contraction from the head of a spine and its arguments
    ([spine_iota_head]), for an evaluator that keeps them apart.

    The types of a match are built from the description and the
    parameters read off the type of the scrutinee: the motive
    [Πθ̄:Θ̄[Δ']. D Δ' θ̄ → s] ([case_motive_type]) and, for a constructor,
    the branch [Πȳ:fields[Δ']. P ū (c Δ' ȳ)] ([case_branch_type]), the
    method type of the eliminator without hypotheses.

    The invariant carried by [signature] is closedness: types and bodies
    are closed, and every term of a description mentions only its
    telescope.  It makes δ and ι commute with substitution
    (PTS.SubstLaws). *)

From Stdlib Require Import List Bool Arith Lia.
From Stdlib Require String.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Telescope Spec.

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

(** The sorts of the motives of D: every sort of the table, or Prop. *)
Inductive elim_class : Type :=
| PropOnly : elim_class
| AllSorts : elim_class.

Record ind_desc : Type := mk_ind {
  ind_name : string;
  ind_params : list term;
  ind_indices : list term;
  ind_sort : sort;              (** [Type_i] or [Prop] *)
  ind_elim : elim_class;
  ind_ctors : list ctor_desc;
}.

Inductive entry : Type :=
| EInd : ind_desc -> entry
| EElim : string -> sort -> term -> bool -> entry   (** D, s, the type, active ι-rules *)
| EDef : string -> term -> term -> entry.           (** f, the type, the body *)

(** ** Sorts of elimination

    A motive into [s] is allowed when [s] is a sort of the table and the
    category of D admits it.  The registration of an eliminator instance
    checks it (Elim.Declare of elim-inductive-types). *)
Definition allows_elimination (S : pts_table) (cls : elim_class) (s : sort) : bool :=
  spec_sort S s && match cls with AllSorts => true | PropOnly => sort_eqb s Prp end.

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

(** [D : Π(Δ). Πθ̄:Θ̄. s] *)
Definition ind_type (d : ind_desc) : term :=
  pis (ind_params d ++ ind_indices d) (Srt (ind_sort d)).

(** [c : Π(Δ). Π(fields). D Δ ū] *)
Definition ctor_type (d : ind_desc) (c : ctor_desc) : term :=
  let p := length (ind_params d) in
  pis (ind_params d ++ field_types (ind_name d) p 0 (ctor_fields c))
      (apps (Const (Ind (ind_name d))) (vars (length (ctor_fields c)) p ++ ctor_indices c)).

(** [elim_D[s] Δ P m̄ θ̄ x]: parameters, motive, one method per
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

(** An entry that is added extends the signature by exactly itself. *)
Lemma sig_add_entries : forall sg e sg', sig_add sg e = Some sg' -> sig_entries sg' = e :: sig_entries sg.
Proof.
  intros sg e sg' H. unfold sig_add in H.
  revert H. generalize (@eq_refl bool (entry_closed e)).
  generalize (entry_closed e) at 2 3. intros b Hb.
  destruct b; intros H; [injection H as <-; reflexivity | discriminate H].
Qed.

(** ** Lookup

    The newest entry of a name wins: an instance registered again with
    active rules shadows its earlier copy. *)

Fixpoint find_ind (es : list entry) (D : string) : option ind_desc :=
  match es with
  | [] => None
  | EInd d :: es' => if String.eqb (ind_name d) D then Some d else find_ind es' D
  | _ :: es' => find_ind es' D
  end.

Fixpoint find_elim (es : list entry) (D : string) (s : sort) : option (term * bool) :=
  match es with
  | [] => None
  | EElim D' s' A act :: es' =>
      if String.eqb D' D && sort_eqb s' s then Some (A, act) else find_elim es' D s
  | _ :: es' => find_elim es' D s
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
  Definition sig_elim (D : string) (s : sort) : option (term * bool) := find_elim (sig_entries sg) D s.
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
    | Elim D s => option_map fst (sig_elim D s)
    | Def f => option_map fst (sig_def f)
    end.

  (** δ: the body of a δ-constant. *)
  Definition sig_delta (g : gref) : option term :=
    match g with
    | Def f => option_map snd (sig_def f)
    | _ => None
    end.

  (** ** ι by the scheme of descriptions *)

  (** An instance with active rules: the type it eliminates and its
      description. *)
  Definition elim_head (h : term) : option (string * sort * ind_desc) :=
    match h with
    | Const (Elim D s) =>
        match sig_elim D s, sig_ind D with
        | Some (_, true), Some d => Some (D, s, d)
        | _, _ => None
        end
    | _ => None
    end.

  (** An instance with active rules applied to its full arity. *)
  Definition elim_view (t : term) : option (string * sort * ind_desc) :=
    match elim_head (spine_head t) with
    | Some (D, s, d) => if Nat.eqb (length (spine_args t)) (elim_arity d) then Some (D, s, d) else None
    | None => None
    end.

  Definition full_elim (t : term) : bool :=
    match elim_view t with Some _ => true | None => false end.
End Lookup.

(** ** Adding an entry

    The lookups in a signature whose entries are those of [sg] with one
    more in front: the new entry answers for its own name, [sg] for the
    others. *)

Section AddEntry.
  Variables sg sg' : signature.

  Section Def.
    Variables (f : String.string) (A b : term).
    Hypothesis E : sig_entries sg' = EDef f A b :: sig_entries sg.

    Lemma add_def_ind : forall D, sig_ind sg' D = sig_ind sg D.
    Proof. intros D. unfold sig_ind. rewrite E. reflexivity. Qed.

    Lemma add_def_elim : forall D s, sig_elim sg' D s = sig_elim sg D s.
    Proof. intros D s. unfold sig_elim. rewrite E. reflexivity. Qed.

    Lemma add_def_def : forall f', sig_def sg' f' = if String.eqb f f' then Some (A, b) else sig_def sg f'.
    Proof. intros f'. unfold sig_def. rewrite E. reflexivity. Qed.
  End Def.

  Section Elim.
    Variables (D : String.string) (s : sort) (A : term) (act : bool).
    Hypothesis E : sig_entries sg' = EElim D s A act :: sig_entries sg.

    Lemma add_elim_ind : forall D', sig_ind sg' D' = sig_ind sg D'.
    Proof. intros D'. unfold sig_ind. rewrite E. reflexivity. Qed.

    Lemma add_elim_def : forall f, sig_def sg' f = sig_def sg f.
    Proof. intros f. unfold sig_def. rewrite E. reflexivity. Qed.

    Lemma add_elim_elim : forall D' s', sig_elim sg' D' s' =
      if String.eqb D D' && sort_eqb s s' then Some (A, act) else sig_elim sg D' s'.
    Proof. intros D' s'. unfold sig_elim. rewrite E. reflexivity. Qed.
  End Elim.

  Section Ind.
    Variable d : ind_desc.
    Hypothesis E : sig_entries sg' = EInd d :: sig_entries sg.

    Lemma add_ind_ind : forall D', sig_ind sg' D' = if String.eqb (ind_name d) D' then Some d else sig_ind sg D'.
    Proof. intros D'. unfold sig_ind. rewrite E. reflexivity. Qed.

    Lemma add_ind_def : forall f, sig_def sg' f = sig_def sg f.
    Proof. intros f. unfold sig_def. rewrite E. reflexivity. Qed.

    Lemma add_ind_elim : forall D' s', sig_elim sg' D' s' = sig_elim sg D' s'.
    Proof. intros D' s'. unfold sig_elim. rewrite E. reflexivity. Qed.
  End Ind.
End AddEntry.

(** The hypothesis of a recursive field [a : Πȳ:B̄. D Δ v̄]:
    [λȳ. elim_D[s] Δ P m̄ v̄ (a ȳ)], where [pre] are the parameters,
    motive and methods of the eliminator.  The indices v̄ lie under the
    [m] positions ȳ: [inst m env] (PTS.Telescope) instantiates them, with
    [env] the previous fields and the parameters, innermost first. *)
Definition hyp (D : string) (s : sort) (pre env Bs vs : list term) (a : term) : term :=
  let m := length Bs in
  lams m (apps (Const (Elim D s))
    (map (lift m) pre ++ map (subst (inst m env)) vs ++ [apps (lift m a) (vars 0 m)])).

(** The arguments of a method: each field, and after a recursive one its
    hypothesis. *)
Fixpoint iota_args (D : string) (s : sort) (pre env : list term) (fs : list field) (xs : list term)
  : list term :=
  match fs, xs with
  | FArg _ :: fs', a :: xs' => a :: iota_args D s pre (a :: env) fs' xs'
  | FRec Bs vs :: fs', a :: xs' => a :: hyp D s pre env Bs vs a :: iota_args D s pre (a :: env) fs' xs'
  | _, _ => []
  end.

(** ** Constructor spines

    [x] is a constructor of D, described by [d], applied to the
    parameters and to all its fields: its position among the
    constructors, its description, and the fields.  ι of an eliminator,
    ι of a match and the strict subterms of the guard (PTS.GuardSound)
    read a constructor spine through this view. *)
Definition ctor_view (D : string) (d : ind_desc) (x : term) : option (nat * ctor_desc * list term) :=
  match spine_head x with
  | Const (Ctor D' c) =>
      if String.eqb D' D then
        match find_ctor (ind_ctors d) c with
        | Some (i, cd) =>
            let p := length (ind_params d) in
            let xa := spine_args x in
            if Nat.eqb (length xa) (p + length (ctor_fields cd)) then Some (i, cd, skipn p xa) else None
        | None => None
        end
      else None
  | _ => None
  end.

Lemma ctor_view_spec : forall D d x i cd xs, ctor_view D d x = Some (i, cd, xs) ->
  exists c ps, x = apps (Const (Ctor D c)) (ps ++ xs) /\ find_ctor (ind_ctors d) c = Some (i, cd) /\
    length ps = length (ind_params d) /\ length xs = length (ctor_fields cd).
Proof.
  intros D d x i cd xs H. unfold ctor_view in H. cbv zeta in H.
  destruct (spine_head x) eqn:Eh; try discriminate H. destruct g as [ | D' c | | ]; try discriminate H.
  destruct (String.eqb D' D) eqn:ED; [ | discriminate H]. apply String.eqb_eq in ED. subst D'.
  destruct (find_ctor (ind_ctors d) c) as [[i' cd']|] eqn:Ec; [ | discriminate H].
  destruct (Nat.eqb (length (spine_args x)) _) eqn:El; [ | discriminate H].
  injection H as <- <- <-. apply Nat.eqb_eq in El.
  exists c, (firstn (length (ind_params d)) (spine_args x)).
  rewrite firstn_skipn, <- Eh, apps_spine. split; [reflexivity | split; [exact Ec | ]].
  rewrite length_firstn, length_skipn. split; lia.
Qed.

Lemma ctor_view_apps : forall D d c ps xs i cd, find_ctor (ind_ctors d) c = Some (i, cd) ->
  length ps = length (ind_params d) -> length xs = length (ctor_fields cd) ->
  ctor_view D d (apps (Const (Ctor D c)) (ps ++ xs)) = Some (i, cd, xs).
Proof.
  intros D d c ps xs i cd Hc Hp Hx. unfold ctor_view. cbv zeta.
  rewrite spine_head_apps, spine_args_apps. cbn [spine_head].
  rewrite String.eqb_refl, Hc. change (spine_args (Const (Ctor D c))) with (@nil term).
  rewrite app_nil_l, length_app, Hp, Hx, Nat.eqb_refl, skipn_app, <- Hp, skipn_all, Nat.sub_diag.
  reflexivity.
Qed.

(** The ι-contraction of the arguments [a] of a full spine of an instance
    for D, when its object is a constructor spine of D. *)
Definition iota_at (D : string) (s : sort) (d : ind_desc) (a : list term) : option term :=
  let p := length (ind_params d) in
  let k := length (ind_ctors d) in
  match ctor_view D d (last a (Var 0)) with
  | Some (i, cd, xs) =>
      match nth_error (firstn k (skipn (S p) a)) i with
      | Some m => Some (apps m (iota_args D s (firstn (S p + k) a) (rev' (firstn p a)) (ctor_fields cd) xs))
      | None => None
      end
  | None => None
  end.

Section Iota.
  Variable sg : signature.

  (** The ι-contraction of a full spine on a constructor spine of its
      type, with the right number of arguments. *)
  Definition iota (t : term) : option term :=
    match elim_view sg t with
    | Some (D, s, d) => iota_at D s d (spine_args t)
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

(** The position found is the position of the constructor. *)
Lemma find_ctor_nth_error : forall cs c i cd, find_ctor cs c = Some (i, cd) -> nth_error cs i = Some cd.
Proof.
  induction cs as [|cd' cs IH]; intros c i cd H; [discriminate H | ]. cbn in H.
  destruct (String.eqb (ctor_name cd') c); [injection H as <- <-; reflexivity | ].
  destruct (find_ctor cs c) as [[i' cd'']|] eqn:E; [ | discriminate H].
  injection H as <- <-. exact (IH _ _ _ E).
Qed.

Lemma sig_delta_closed : forall sg g b, sig_delta sg g = Some b -> closed b = true.
Proof.
  intros sg g b H. destruct g as [ | | | f]; try discriminate H. cbn in H.
  unfold sig_def in H. destruct (find_def (sig_entries sg) f) as [[A b']|] eqn:E; [ | discriminate H].
  injection H as <-. exact (proj2 (find_def_closed _ _ _ _ (sig_wf sg) E)).
Qed.

Lemma elim_view_spec : forall sg t D s d, elim_view sg t = Some (D, s, d) ->
  spine_head t = Const (Elim D s) /\ length (spine_args t) = elim_arity d /\ ind_closed d = true.
Proof.
  intros sg t D s d H. unfold elim_view, elim_head in H.
  destruct (spine_head t) eqn:Eh; try discriminate H. destruct g as [ | | D' s' | ]; try discriminate H.
  destruct (sig_elim sg D' s') as [[A [|]]|]; try discriminate H.
  destruct (sig_ind sg D') as [d'|] eqn:Ed; try discriminate H. cbv beta iota in H.
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
  destruct (elim_view sg t) as [[[D s] d]|] eqn:Ev; [ | discriminate H].
  destruct (elim_view_spec _ _ _ _ _ Ev) as (_ & Hlen & _).
  destruct t; try (eexists; eexists; reflexivity).
  all: cbn in Hlen; unfold elim_arity in Hlen; rewrite Nat.add_1_r in Hlen; discriminate Hlen.
Qed.

(** ** match *)

Section Case.
  Variable sg : signature.

  (** [Case D s P (c_i Δ' ā) bs ⇝ b_i ā]: a constructor of D applied to
      the parameters and its fields, and the branch at its position. *)
  Definition case_iota (t : term) : option term :=
    match t with
    | Case D _ _ x bs =>
        match sig_ind sg D with
        | Some d =>
            match ctor_view D d x with
            | Some (i, _, xs) => option_map (fun b => apps b xs) (nth_error bs i)
            | None => None
            end
        | None => None
        end
    | _ => None
    end.
End Case.

(** [Πθ̄:Θ̄[ps]. D ps θ̄ → s]: the type of the motive of a match on an
    element of [D ps ū]. *)
Definition case_motive_type (d : ind_desc) (ps : list term) (s : sort) : term :=
  let q := length (ind_indices d) in
  pis (inst_tele ps 0 (ind_indices d))
      (Pi (apps (Const (Ind (ind_name d))) (map (lift q) ps ++ vars 0 q)) (Srt s)).

(** [Πȳ:fields[ps]. P ū[ps, ȳ] (c ps ȳ)]: the type of the branch of the
    constructor [c] for the motive [P]. *)
Definition case_branch_type (d : ind_desc) (ps : list term) (P : term) (c : ctor_desc) : term :=
  let env := params_env ps in
  let n := length (ctor_fields c) in
  pis (inst_tele_env env 0 (field_types (ind_name d) (length (ind_params d)) 0 (ctor_fields c)))
      (apps (lift n P)
         (map (inst_env env n) (ctor_indices c) ++
          [apps (Const (Ctor (ind_name d) (ctor_name c))) (map (lift n) ps ++ vars 0 n)])).

(** ** fix *)

(** [Fix A k b] applied to [k + 1] arguments, up to the structural one. *)
Definition fix_view (t : term) : option (term * nat * term) :=
  match spine_head t with
  | Fix A k b => if Nat.eqb (length (spine_args t)) (S k) then Some (A, k, b) else None
  | _ => None
  end.

Definition full_fix (t : term) : bool :=
  match fix_view t with Some _ => true | None => false end.

(** Unfolding, when the structural argument is a constructor spine:
    [Fix A k b a₀ … a_k ⇝ b[Fix A k b/0] a₀ … a_k]. *)
Definition fix_at (A : term) (k : nat) (b : term) (args : list term) : option term :=
  match spine_head (last args (Var 0)) with
  | Const (Ctor _ _) => Some (apps (subst1 b (Fix A k b)) args)
  | _ => None
  end.

Definition fix_unfold (t : term) : option term :=
  match fix_view t with
  | Some (A, k, b) => fix_at A k b (spine_args t)
  | None => None
  end.

(** ** Spines contracted at their last argument *)

Definition spine_iota (sg : signature) (t : term) : option term :=
  match iota sg t with
  | Some u => Some u
  | None => fix_unfold t
  end.

(** The same contraction from the head of a spine and its arguments:
    [head_arity] is the number of arguments at which the head is
    contracted, [head_iota] contracts them ([spine_iota_head]).  An
    evaluator that keeps the head of a spine and counts its arguments
    tests the arity without walking the spine. *)
Definition head_arity (sg : signature) (h : term) : option nat :=
  match elim_head sg h with
  | Some (_, _, d) => Some (elim_arity d)
  | None => match h with Fix _ k _ => Some (S k) | _ => None end
  end.

Definition head_iota (sg : signature) (h : term) (args : list term) : option term :=
  match elim_head sg h with
  | Some (D, s, d) => iota_at D s d args
  | None => match h with Fix A k b => fix_at A k b args | _ => None end
  end.

(** A spine of [n] arguments under a head of arity [m] is full. *)
Definition at_arity (m : option nat) (n : nat) : bool :=
  match m with Some m' => Nat.eqb n m' | None => false end.

(** A spine contracted at its last argument: its head reaches its
    arity there, the same arity as [spine_iota] ([spine_iota_full]). *)
Definition full_spine (sg : signature) (t : term) : bool :=
  at_arity (head_arity sg (spine_head t)) (length (spine_args t)).

Lemma full_spine_head : forall sg t,
  full_spine sg t = at_arity (head_arity sg (spine_head t)) (length (spine_args t)).
Proof. reflexivity. Qed.

Lemma spine_iota_head : forall sg t,
  spine_iota sg t =
  match head_arity sg (spine_head t) with
  | Some m => if Nat.eqb (length (spine_args t)) m then head_iota sg (spine_head t) (spine_args t) else None
  | None => None
  end.
Proof.
  intros sg t. unfold spine_iota, iota, elim_view, fix_unfold, fix_view, head_arity, head_iota.
  destruct (spine_head t); cbn [elim_head]; try reflexivity.
  - destruct g as [ | | D s | ]; cbn [elim_head]; try reflexivity.
    destruct (sig_elim sg D s) as [[A [|]]|]; destruct (sig_ind sg D) as [d|]; try reflexivity.
    destruct (Nat.eqb _ _); [destruct (iota_at _ _ _ _) | ]; reflexivity.
  - destruct (Nat.eqb _ _); reflexivity.
Qed.

Lemma fix_view_spec : forall t A k b, fix_view t = Some (A, k, b) ->
  spine_head t = Fix A k b /\ length (spine_args t) = S k.
Proof.
  intros t A k b H. unfold fix_view in H.
  destruct (spine_head t) eqn:Eh; try discriminate H.
  destruct (Nat.eqb _ _) eqn:E; [ | discriminate H].
  injection H as <- <- <-. apply Nat.eqb_eq in E. split; [reflexivity | exact E].
Qed.

Lemma fix_unfold_full : forall t u, fix_unfold t = Some u -> full_fix t = true.
Proof.
  intros t u H. unfold fix_unfold in H. unfold full_fix.
  destruct (fix_view t); [reflexivity | discriminate H].
Qed.

Lemma fix_unfold_app : forall t u, fix_unfold t = Some u -> exists f a, t = App f a.
Proof.
  intros t u H. unfold fix_unfold in H.
  destruct (fix_view t) as [[[A k] b]|] eqn:Ev; [ | discriminate H].
  destruct (fix_view_spec _ _ _ _ Ev) as [_ Hl].
  destruct t; try (eexists; eexists; reflexivity). all: discriminate Hl.
Qed.

Lemma spine_iota_full : forall sg t u, spine_iota sg t = Some u -> full_spine sg t = true.
Proof.
  intros sg t u H. rewrite spine_iota_head in H. unfold full_spine, at_arity.
  destruct (head_arity sg (spine_head t)); [ | discriminate H].
  destruct (Nat.eqb _ _); [reflexivity | discriminate H].
Qed.

Lemma spine_iota_app : forall sg t u, spine_iota sg t = Some u -> exists f a, t = App f a.
Proof.
  intros sg t u H. unfold spine_iota in H.
  destruct (iota sg t) eqn:E; [exact (iota_app _ _ _ E) | exact (fix_unfold_app _ _ H)].
Qed.

(** A β-redex is no spine of a constant or a fix. *)
Lemma spine_iota_lam : forall sg b u, spine_iota sg (App (Lam b) u) = None.
Proof. reflexivity. Qed.

Lemma full_spine_lam : forall sg b u, full_spine sg (App (Lam b) u) = false.
Proof. reflexivity. Qed.

Lemma case_iota_case : forall sg t u, case_iota sg t = Some u ->
  exists D s P x bs, t = Case D s P x bs.
Proof.
  intros sg t u H. destruct t; try discriminate H. do 5 eexists. reflexivity.
Qed.

(** ** Opaque δ-constants

    The same signature without its δ-constants: the inductive types and
    the eliminator instances stay, so ι and the unfolding of [fix] do
    not change, and δ is gone.  Its reduction is reduction of the
    signature (PTS.Reduction, [red1_opaque]); conversion tries it first
    ([convert] of PTS.Eval). *)

Definition is_def_entry (e : entry) : bool :=
  match e with EDef _ _ _ => true | _ => false end.

Lemma entries_closed_filter : forall f es, entries_closed es = true -> entries_closed (filter f es) = true.
Proof.
  intros f es H. unfold entries_closed in *. rewrite forallb_forall in *.
  intros e He. apply filter_In in He as [He _]. exact (H e He).
Qed.

Definition sig_opaque (sg : signature) : signature :=
  {| sig_entries := filter (fun e => negb (is_def_entry e)) (sig_entries sg);
     sig_wf := entries_closed_filter _ _ (sig_wf sg) |}.

Lemma find_ind_opaque : forall es D,
  find_ind (filter (fun e => negb (is_def_entry e)) es) D = find_ind es D.
Proof. induction es as [|e es IH]; intros D; [reflexivity | ]. destruct e; cbn; rewrite ?IH; reflexivity. Qed.

Lemma find_elim_opaque : forall es D s,
  find_elim (filter (fun e => negb (is_def_entry e)) es) D s = find_elim es D s.
Proof. induction es as [|e es IH]; intros D s; [reflexivity | ]. destruct e; cbn; rewrite ?IH; reflexivity. Qed.

Lemma find_def_opaque : forall es f, find_def (filter (fun e => negb (is_def_entry e)) es) f = None.
Proof. induction es as [|e es IH]; intros f; [reflexivity | ]. destruct e; cbn; apply IH. Qed.

Lemma sig_ind_opaque : forall sg D, sig_ind (sig_opaque sg) D = sig_ind sg D.
Proof. intros sg D. apply find_ind_opaque. Qed.

Lemma sig_elim_opaque : forall sg D s, sig_elim (sig_opaque sg) D s = sig_elim sg D s.
Proof. intros sg D s. apply find_elim_opaque. Qed.

Lemma sig_delta_opaque : forall sg g, sig_delta (sig_opaque sg) g = None.
Proof. intros sg [ | | | f]; try reflexivity. cbn. unfold sig_def. cbn. rewrite find_def_opaque. reflexivity. Qed.

Lemma iota_opaque : forall sg t, iota (sig_opaque sg) t = iota sg t.
Proof.
  intros sg t. unfold iota, elim_view, elim_head.
  destruct (spine_head t); try reflexivity. destruct g; try reflexivity.
  rewrite sig_elim_opaque, sig_ind_opaque. reflexivity.
Qed.

Lemma case_iota_opaque : forall sg t, case_iota (sig_opaque sg) t = case_iota sg t.
Proof. intros sg t. unfold case_iota. destruct t; try reflexivity. rewrite sig_ind_opaque. reflexivity. Qed.

Lemma spine_iota_opaque : forall sg t, spine_iota (sig_opaque sg) t = spine_iota sg t.
Proof. intros sg t. unfold spine_iota. rewrite iota_opaque. reflexivity. Qed.

(** The contraction of a spine happens only at the full one. *)
Lemma spine_iota_full_head : forall sg t,
  spine_iota sg t = if full_spine sg t then head_iota sg (spine_head t) (spine_args t) else None.
Proof.
  intros sg t. rewrite spine_iota_head. unfold full_spine, at_arity.
  destruct (head_arity sg (spine_head t)); reflexivity.
Qed.

(** ** Closedness and names of declarations *)

Lemma closed_above_pis : forall As B k,
  closed_above k (pis As B) = tele_closed k As && closed_above (k + length As) B.
Proof.
  induction As as [|A As IH]; intros B k; cbn [pis tele_closed length].
  - rewrite Nat.add_0_r. reflexivity.
  - cbn [closed_above]. rewrite IH, Nat.add_succ_r, andb_assoc. reflexivity.
Qed.

Lemma tele_closed_app : forall As Bs k,
  tele_closed k (As ++ Bs) = tele_closed k As && tele_closed (k + length As) Bs.
Proof.
  induction As as [|A As IH]; intros Bs k; cbn [app tele_closed length].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH, Nat.add_succ_r, andb_assoc. reflexivity.
Qed.

Lemma field_types_length : forall D p fs l, length (field_types D p l fs) = length fs.
Proof. intros D p fs. induction fs as [|fd fs IH]; intros l; cbn; [reflexivity | now rewrite IH]. Qed.

(** The field at position [l] lies under the parameters and the [l]
    fields before it. *)
Lemma field_types_closed : forall D p fs l,
  fields_closed (p + l) fs = true -> tele_closed (p + l) (field_types D p l fs) = true.
Proof.
  intros D p fs. induction fs as [|fd fs IH]; intros l H; [reflexivity | ].
  cbn [fields_closed] in H. apply andb_prop in H as [Hf H].
  cbn [field_types tele_closed]. apply andb_true_intro. split.
  - destruct fd as [A | Bs vs]; cbn [field_type field_closed] in *; [exact Hf | ].
    apply andb_prop in Hf as [HB Hv].
    rewrite closed_above_pis, HB. cbn [andb]. rewrite closed_above_apps. cbn [closed_above andb].
    rewrite forallb_app, vars_closed by lia. exact Hv.
  - rewrite <- Nat.add_succ_r. apply IH. rewrite Nat.add_succ_r. exact H.
Qed.

Lemma find_elim_closed : forall es D s A act,
  entries_closed es = true -> find_elim es D s = Some (A, act) -> closed A = true.
Proof.
  induction es as [|e es IH]; intros D s A act Hc H; [discriminate H | ].
  cbn in Hc. apply andb_prop in Hc as [He Hc].
  destruct e as [ | D' s' A' act' | ]; cbn in H; try exact (IH _ _ _ _ Hc H).
  destruct (String.eqb D' D && sort_eqb s' s); [injection H as <- _; exact He | exact (IH _ _ _ _ Hc H)].
Qed.

(** The type of a constant is closed. *)
Lemma sig_type_closed : forall sg g A, sig_type sg g = Some A -> closed A = true.
Proof.
  intros sg g A H. destruct g as [D | D c | D s | f]; cbn [sig_type] in H.
  - destruct (sig_ind sg D) as [d|] eqn:E; [ | discriminate H]. injection H as <-.
    pose proof (find_ind_closed _ _ _ (sig_wf sg) E) as Hd. unfold ind_closed in Hd. cbv zeta in Hd.
    apply andb_prop in Hd as [Hd _]. apply andb_prop in Hd as [Hp Hi].
    unfold closed, ind_type. rewrite closed_above_pis, tele_closed_app, Hp. cbn [Nat.add andb].
    rewrite Hi. reflexivity.
  - destruct (sig_ind sg D) as [d|] eqn:E; [ | discriminate H].
    destruct (find_ctor (ind_ctors d) c) as [[i cd]|] eqn:Ec; [ | discriminate H].
    injection H as <-. cbn [snd].
    pose proof (find_ind_closed _ _ _ (sig_wf sg) E) as Hd. unfold ind_closed in Hd. cbv zeta in Hd.
    apply andb_prop in Hd as [Hd Hcs]. apply andb_prop in Hd as [Hp _].
    pose proof (find_ctor_closed _ _ _ _ _ Hcs Ec) as Hcd. unfold ctor_closed in Hcd.
    apply andb_prop in Hcd as [Hf Hidx].
    pose proof (field_types_closed (ind_name d) (length (ind_params d)) (ctor_fields cd) 0) as Hft.
    rewrite Nat.add_0_r in Hft.
    unfold closed, ctor_type. cbv zeta.
    rewrite closed_above_pis, tele_closed_app, Hp. cbn [Nat.add andb].
    rewrite (Hft Hf), length_app, field_types_length. cbn [andb].
    rewrite closed_above_apps, forallb_app, vars_closed by lia. exact Hidx.
  - destruct (sig_elim sg D s) as [[A' act]|] eqn:E; [ | discriminate H]. injection H as <-.
    exact (find_elim_closed _ _ _ _ _ (sig_wf sg) E).
  - destruct (sig_def sg f) as [[A' b]|] eqn:E; [ | discriminate H]. injection H as <-.
    exact (proj1 (find_def_closed _ _ _ _ (sig_wf sg) E)).
Qed.

(** The description of an inductive type of the signature is closed: the
    indices lie under the parameters, the constructors are closed. *)
Lemma sig_ind_closed : forall sg D d, sig_ind sg D = Some d ->
  tele_closed (length (ind_params d)) (ind_indices d) = true /\
  forallb (ctor_closed (length (ind_params d))) (ind_ctors d) = true.
Proof.
  intros sg D d H. pose proof (find_ind_closed _ _ _ (sig_wf sg) H) as Hd.
  unfold ind_closed in Hd. cbv zeta in Hd.
  apply andb_prop in Hd as [Hd Hcs]. apply andb_prop in Hd as [_ Hi]. split; assumption.
Qed.

Lemma find_ind_name : forall es D d, find_ind es D = Some d -> ind_name d = D.
Proof.
  induction es as [|e es IH]; intros D d H; [discriminate H | ].
  destruct e as [d'| | ]; cbn in H; try exact (IH _ _ H).
  destruct (String.eqb (ind_name d') D) eqn:E; [injection H as <-; apply String.eqb_eq, E | exact (IH _ _ H)].
Qed.

Lemma sig_ind_name : forall sg D d, sig_ind sg D = Some d -> ind_name d = D.
Proof. intros sg D d H. exact (find_ind_name _ _ _ H). Qed.

Lemma find_ctor_name : forall cs c i cd, find_ctor cs c = Some (i, cd) -> ctor_name cd = c.
Proof.
  induction cs as [|cd' cs IH]; intros c i cd H; [discriminate H | ]. cbn [find_ctor] in H.
  destruct (String.eqb (ctor_name cd') c) eqn:E; [injection H as _ <-; apply String.eqb_eq, E | ].
  destruct (find_ctor cs c) as [[i' cd'']|] eqn:Ec; [ | discriminate H].
  cbn [option_map] in H. injection H as _ <-. exact (IH _ _ _ Ec).
Qed.

Lemma sig_type_ind : forall sg D d, sig_ind sg D = Some d -> sig_type sg (Ind D) = Some (ind_type d).
Proof. intros sg D d Hd. cbn [sig_type]. rewrite Hd. reflexivity. Qed.

Lemma case_branch_type_shape : forall d ps c, exists Ts n l a,
  forall Q, case_branch_type d ps Q c = pis Ts (apps (lift n Q) (l ++ [a])).
Proof. intros d ps c. unfold case_branch_type. cbv zeta. do 4 eexists. intros Q. reflexivity. Qed.
