(** * The PTS checker: [infer] and [check]

    One program for every specification: sorts, axioms, Π- and Σ-rules
    are looked up in [S], the primitives Void, Unit, Bool are accepted
    only when [spec_prim S] switches them on, and constants only when
    [spec_decls S] does; a constant takes its closed type from the
    signature [sg], and one missing from it is rejected.  The rules are
    those of the annotated kernel PTS.Bidir.

    Recursion is structural on the term; [fuel] bounds only the evaluation
    done for types, by [whnf] (unfolding a type to a sort or a Π) and by
    [convert] (conversion).  Running out of it is not an error: a run
    ends in one of three answers, [Accepted], [Rejected] with a
    diagnostic, or [Undecided] when the fuel ran out.  Only types are
    evaluated: an argument is checked against the domain and
    then substituted into the codomain, never reduced.

    Both modes are one function [tc]: [tc Γ t None] synthesizes, and
    [tc Γ t (Some T)] checks against [T].  λ and pairs only check.  The synthesis rules are written
    once, in the thunk [synth]; checking a non-λ runs it and compares.
    (Separate mutual [infer] and [check] would have to repeat every
    synthesis rule inside [check], since a call [infer Γ t] on the term
    [check] recurses on violates the guard condition.)

    The run is traced: axioms and rules consulted, types unfolded to a
    sort or a Π (with the type before unfolding), arguments checked,
    codomains instantiated, conversions passed (with the common form both
    sides reach), and the result families of eliminators (with their
    sort: a universe means large elimination).

    A [match] on D is checked in the order of its rule: D is a family of
    the signature, its category allows motives into the given sort
    ([allows_elimination], [EElimSort] otherwise), there is one branch
    per constructor, the type of the scrutinee unfolds to [D ps us],
    the motive checks against [case_motive_type] and every branch
    against its [case_branch_type].  Branches are positional: a missing
    or a repeated branch shows as a wrong number of them.  A [fix]: its
    annotation is a type, its [k]-th domain unfolds to a family of the
    signature, its body starts with [k + 1] λ and checks against the
    annotation with the function itself in the context, and then its
    guard (PTS.Guard) accepts the recursive calls ([ENotGuarded]
    otherwise, with the event [EvGuard] on success).

    The entry points [run_infer] and [run_check] validate the context and
    the expected type before typing the term. *)

From Stdlib Require Import List Bool.
From Stdlib Require String.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Spec Signature Eval Guard.

Inductive error : Type :=
| EUnboundVar : nat -> error
| ENotInSystem : sort -> error           (** not a sort of the specification *)
| ETopSort : sort -> error               (** a sort without a type, e.g. △ of U⁻ *)
| ENoRule : term -> sort -> sort -> error   (** a Π-type and its missing rule (s1, s2, _) *)
| ENotASort : term -> term -> error      (** a type former and its type, not a sort *)
| ENotAPi : term -> term -> error        (** a function or λ and its type, not a Π *)
| EMismatch : term -> term -> term -> error   (** term, expected, inferred *)
| EStuckType : term -> term -> term -> error  (** term, expected, inferred *)
| ECannotInfer : term -> error           (** a λ in a synthesizing position *)
| ENoPrimitives : term -> error          (** a primitive while they are off *)
| EBadFamily : term -> term -> term -> error
    (** result family, expected domain (Void, Unit or Bool), actual domain *)
| ENoSigmaRule : term -> sort -> sort -> error   (** a Σ-type and its missing rule *)
| ENotASigma : term -> term -> error     (** a pair or projected term and its type, not a Σ *)
| ENoDecls : term -> error               (** a constant while constants are off *)
| EUnknownConst : gref -> error          (** a constant missing from the signature *)
| ENotInductive : term -> String.string -> term -> error
    (** a scrutinee, the family of its match, and its type: not an element of the family *)
| EElimSort : String.string -> sort -> error
    (** the category of elimination of D does not allow motives into [s] *)
| EBranchCount : term -> nat -> nat -> error
    (** a match, the number of constructors and of branches *)
| ENoStructArg : term -> nat -> term -> error
    (** a fix, its structural position, and the rest of its type: not a Π *)
| EStructNotInductive : term -> nat -> term -> error
    (** a fix, its structural position, and the type there: not a family of the signature *)
| EFixBody : term -> nat -> error
    (** a fix whose body has fewer λ than its structural position plus one *)
| ENotGuarded : term -> guard_error -> error.
    (** a fix and the recursive call its guard refuses *)

(** The events of a run.  A run of an entry point has three phases, each
    opened by a marker: the entries of the context, from the outermost
    one (de Bruijn level 0), the expected type, and the term itself. *)
Inductive event : Type :=
(** phases *)
| EvCtxEntry : nat -> term -> event              (** entry at level [k] with type [A] *)
| EvExpected : term -> event                     (** expected type [T] *)
| EvTerm : term -> event                         (** the term to type *)
(** typing *)
| EvAxiom : sort -> sort -> event                (** [s : s'] *)
| EvRule : sort -> sort -> sort -> event         (** [(s1, s2, s3)] *)
| EvUnfoldSort : term -> term -> sort -> event   (** [t]: its type [T], not syntactically a sort, unfolds to [s] *)
| EvUnfoldPi : term -> term -> term -> term -> event
    (** [t]: its type [T] unfolds to Π A. B *)
| EvArg : term -> term -> event                  (** argument [u] checked against [A] *)
| EvSubst : term -> term -> term -> event        (** [B], [u], [B[u/0]] *)
| EvConv : term -> term -> term -> event         (** inferred [A] ≡ expected [T], both reaching [V] *)
| EvFamily : term -> term -> sort -> event       (** result family [C] over [D] into [s] *)
| EvSigmaRule : sort -> sort -> sort -> event    (** the Σ-rule [(s1, s2, s3)] *)
| EvUnfoldSigma : term -> term -> term -> term -> event
    (** [t]: its type [T] unfolds to Σ A. B *)
| EvCase : String.string -> sort -> list term -> list term -> event
    (** a match on [D ps us] into [s] *)
| EvBranch : String.string -> term -> event      (** the branch of [c] checked against [T] *)
| EvFix : nat -> String.string -> event          (** a fix structural in its argument [k], of type D *)
| EvGuard : nat -> event.                        (** its recursive calls decrease in the argument [k] *)

(** Inside the checker a run fails either by rejecting the input or by
    running out of fuel while typing a term. *)
Inductive failure : Type :=
| Reject : error -> failure
| NoFuel : term -> failure.

(** The answer of an entry point. *)
Inductive answer (A : Type) : Type :=
| Accepted : A -> answer A
| Rejected : error -> answer A
| Undecided : term -> answer A.    (** fuel ran out while typing this term *)

Arguments Accepted {A} _.
Arguments Rejected {A} _.
Arguments Undecided {A} _.

Definition to_answer {A} (r : result failure A) : answer A :=
  match r with
  | Ok a => Accepted a
  | Err (Reject e) => Rejected e
  | Err (NoFuel t) => Undecided t
  end.

Section Check.
  Variable S : spec.
  Variable sg : signature.
  Variable fuel : nat.

  Definition M (A : Type) : Type := traced event failure A.

  Definition reject {A} (e : error) : M A := tfail (Reject e).
  Definition no_fuel {A} (t : term) : M A := tfail (NoFuel t).

  Definition axiom (s : sort) : M sort :=
    match spec_axiom S s with
    | Some s' => let! _ := temit (EvAxiom s s') in tret s'
    | None => reject (if spec_sort S s then ETopSort s else ENotInSystem s)
    end.

  Definition rule (t : term) (s1 s2 : sort) : M sort :=
    match spec_rule S s1 s2 with
    | Some s3 => let! _ := temit (EvRule s1 s2 s3) in tret s3
    | None => reject (ENoRule t s1 s2)
    end.

  Definition prim (t : term) : M sort :=
    match spec_prim S with
    | Some s0 => tret s0
    | None => reject (ENoPrimitives t)
    end.

  Definition sigma_rule (t : term) (s1 s2 : sort) : M sort :=
    match spec_sigma S s1 s2 with
    | Some s3 => let! _ := temit (EvSigmaRule s1 s2 s3) in tret s3
    | None => reject (ENoSigmaRule t s1 s2)
    end.

  Definition decls (t : term) : M unit :=
    if spec_decls S then tret tt else reject (ENoDecls t).

  (** [T], the type of [t], unfolded to a sort. *)
  Definition as_sort (t T : term) : M sort :=
    match whnf sg fuel T with
    | HeadForm (Srt s) =>
        match T with
        | Srt _ => tret s
        | _ => let! _ := temit (EvUnfoldSort t T s) in tret s
        end
    | HeadForm T' => reject (ENotASort t T')
    | HeadOutOfFuel _ => no_fuel t
    end.

  (** [T], the type of [t], unfolded to a Π. *)
  Definition as_pi (t T : term) : M (term * term) :=
    match whnf sg fuel T with
    | HeadForm (Pi A B) => let! _ := temit (EvUnfoldPi t T A B) in tret (A, B)
    | HeadForm T' => reject (ENotAPi t T')
    | HeadOutOfFuel _ => no_fuel t
    end.

  (** [T], the type of [t], unfolded to a Σ. *)
  Definition as_sigma (t T : term) : M (term * term) :=
    match whnf sg fuel T with
    | HeadForm (Sigma A B) => let! _ := temit (EvUnfoldSigma t T A B) in tret (A, B)
    | HeadForm T' => reject (ENotASigma t T')
    | HeadOutOfFuel _ => no_fuel t
    end.

  (** [t] has the inferred type [A] and the expected type [T]. *)
  Definition check_conv (t A T : term) : M unit :=
    match convert sg fuel A T with
    | ConvEqual V => temit (EvConv A T V)
    | ConvDifferent => reject (EMismatch t T A)
    | ConvStuck => reject (EStuckType t T A)
    | ConvOutOfFuel => no_fuel t
    end.

  (** [TC], the type of the result family [C] of an eliminator over [D0],
      unfolds to [Πx:D. s] with [D ≡ D0]. *)
  Definition family (C TC D0 : term) : M unit :=
    let! p := as_pi C TC in
    let (D, K) := p in
    match convert sg fuel D D0 with
    | ConvEqual _ =>
        let! s := as_sort C K in
        temit (EvFamily C D0 s)
    | ConvOutOfFuel => no_fuel C
    | _ => reject (EBadFamily C D0 D)
    end.

  (** The family [D], as the head of a spine. *)
  Definition is_ind (D : String.string) (h : term) : bool :=
    match h with
    | Const (Ind D') => String.eqb D' D
    | _ => false
    end.

  (** [X], the type of the scrutinee [x] of a match on [D], unfolded to
      [D ps us]: the parameters and the indices. *)
  Definition as_ind (x X : term) (D : String.string) (d : ind_desc) : M (list term * list term) :=
    match whnf sg fuel X with
    | HeadForm X' =>
        let p := length (ind_params d) in
        let args := spine_args X' in
        if is_ind D (spine_head X') && Nat.eqb (length args) (p + length (ind_indices d))
        then tret (firstn p args, skipn p args)
        else reject (ENotInductive x D X')
    | HeadOutOfFuel _ => no_fuel x
    end.

  Definition elim_sort (D : String.string) (d : ind_desc) (s : sort) : M unit :=
    if allows_elimination S (ind_elim d) s then tret tt else reject (EElimSort D s).

  (** The structural argument of the fix [t] at [k0]: the [k]-th domain
      of [T] unfolds to a family of the signature, whose name is returned. *)
  Fixpoint struct_ind (t : term) (k0 : nat) (T : term) (k : nat) : M String.string :=
    match whnf sg fuel T with
    | HeadForm (Pi A B) =>
        match k with
        | O =>
            match whnf sg fuel A with
            | HeadForm A' =>
                match spine_head A' with
                | Const (Ind D) =>
                    match sig_ind sg D with
                    | Some _ => tret D
                    | None => reject (EUnknownConst (Ind D))
                    end
                | _ => reject (EStructNotInductive t k0 A')
                end
            | HeadOutOfFuel _ => no_fuel t
            end
        | Datatypes.S k' => struct_ind t k0 B k'
        end
    | HeadForm T' => reject (ENoStructArg t k0 T')
    | HeadOutOfFuel _ => no_fuel t
    end.

  (** The guard of the fix [t] structural in its argument [k]. *)
  Definition guarded (t : term) (k : nat) (b : term) : M unit :=
    match guard_fix sg k b with
    | Ok _ => temit (EvGuard k)
    | Err e => reject (ENotGuarded t e)
    end.

  Fixpoint tc (G : ctx) (t : term) (expected : option term) {struct t} : M term :=
    (** [A], a component of [t], synthesizes a sort. *)
    let sort_of (G : ctx) (A : term) : M sort :=
      let! K := tc G A None in as_sort A K in
    (** The start of an eliminator [t] over [D0]: primitives are on, and
        the result family [C] is a family over [D0]. *)
    let elim_family (C D0 : term) : M unit :=
      let! _ := prim t in
      let! TC := tc G C None in
      family C TC D0 in
    let synth (_ : unit) : M term :=
      match t with
      | Srt s => let! s' := axiom s in tret (Srt s')
      | Var n =>
          match lookup G n with
          | Some A => tret A
          | None => reject (EUnboundVar n)
          end
      | Pi A B =>
          let! s1 := sort_of G A in
          let! s2 := sort_of (A :: G) B in
          let! s3 := rule t s1 s2 in
          tret (Srt s3)
      | Lam _ => reject (ECannotInfer t)
      | App f u =>
          let! F := tc G f None in
          let! p := as_pi f F in
          let (A, B) := p in
          let! _ := tc G u (Some A) in
          let! _ := temit (EvArg u A) in
          let B' := subst1 B u in
          let! _ := temit (EvSubst B u B') in
          tret B'
      | Ann u A =>
          let! _ := sort_of G A in
          let! _ := tc G u (Some A) in
          tret A
      | Void | Unit | Bool => let! s0 := prim t in tret (Srt s0)
      | Tt => let! _ := prim t in tret Unit
      | BTrue | BFalse => let! _ := prim t in tret Bool
      | ElimVoid C e =>
          let! _ := elim_family C Void in
          let! _ := tc G e (Some Void) in
          tret (App C e)
      | ElimUnit C c u =>
          let! _ := elim_family C Unit in
          let! _ := tc G c (Some (App C Tt)) in
          let! _ := tc G u (Some Unit) in
          tret (App C u)
      | ElimBool C bt bf b =>
          let! _ := elim_family C Bool in
          let! _ := tc G bt (Some (App C BTrue)) in
          let! _ := tc G bf (Some (App C BFalse)) in
          let! _ := tc G b (Some Bool) in
          tret (App C b)
      | Sigma A B =>
          let! s1 := sort_of G A in
          let! s2 := sort_of (A :: G) B in
          let! s3 := sigma_rule t s1 s2 in
          tret (Srt s3)
      | Pair _ _ => reject (ECannotInfer t)
      | Fst p =>
          let! P := tc G p None in
          let! q := as_sigma p P in
          let (A, _) := q in
          tret A
      | Snd p =>
          let! P := tc G p None in
          let! q := as_sigma p P in
          let (_, B) := q in
          let B' := subst1 B (Fst p) in
          let! _ := temit (EvSubst B (Fst p) B') in
          tret B'
      | Const g =>
          let! _ := decls t in
          match sig_type sg g with
          | Some A => tret A
          | None => reject (EUnknownConst g)
          end
      | Case D s P x bs =>
          let! _ := decls t in
          match sig_ind sg D with
          | None => reject (EUnknownConst (Ind D))
          | Some d =>
              let! _ := elim_sort D d s in
              let count := EBranchCount t (length (ind_ctors d)) (length bs) in
              if Nat.eqb (length bs) (length (ind_ctors d)) then
                let! X := tc G x None in
                let! pu := as_ind x X D d in
                let (ps, us) := pu in
                let! _ := temit (EvCase D s ps us) in
                let! _ := tc G P (Some (case_motive_type d ps s)) in
                (* the branches against the constructors, in order *)
                let! _ := titer2 (fun c b =>
                  let T := case_branch_type d ps P c in
                  let! _ := temit (EvBranch (ctor_name c) T) in
                  let! _ := tc G b (Some T) in
                  tret tt) (Reject count) (ind_ctors d) bs in
                tret (apps P (us ++ [x]))
              else reject count
          end
      | Fix A k b =>
          let! _ := sort_of G A in
          let! D := struct_ind t k A k in
          let! _ := temit (EvFix k D) in
          if has_lams (Nat.succ k) b then
            let! _ := tc (A :: G) b (Some (lift 1 A)) in
            let! _ := guarded t k b in
            tret A
          else reject (EFixBody t k)
      end in
    match expected, t with
    | None, _ => synth tt
    | Some T, Lam b =>
        let! p := as_pi t T in
        let (A, B) := p in
        let! _ := tc (A :: G) b (Some B) in
        tret T
    | Some T, Pair a b =>
        let! p := as_sigma t T in
        let (A, B) := p in
        let! _ := tc G a (Some A) in
        let B' := subst1 B a in
        let! _ := temit (EvSubst B a B') in
        let! _ := tc G b (Some B') in
        tret T
    | Some T, _ =>
        let! A := synth tt in
        let! _ := check_conv t A T in
        tret T
    end.

  Definition infer (G : ctx) (t : term) : M term := tc G t None.

  Definition check (G : ctx) (t T : term) : M unit :=
    let! _ := tc G t (Some T) in tret tt.

  Definition infer_sort (G : ctx) (A : term) : M sort :=
    let! K := infer G A in as_sort A K.

  (** ** Admissible inputs

      [infer] and [check] follow the rules of PTS.Bidir, which assume a
      well-formed context and expected type; on other inputs they may
      accept too much.  The entry points first establish [bwf_ctx] and
      [btype]: every entry of the context synthesizes a sort in the
      context behind it, and an expected type is a sort of the system or
      synthesizes a sort.  A sort is accepted as expected type even
      without a type of its own, such as the top sort △ of U⁻. *)

  Fixpoint check_ctx (G : ctx) : M unit :=
    match G with
    | [] => tret tt
    | A :: G' =>
        let! _ := check_ctx G' in
        let! _ := temit (EvCtxEntry (length G') A) in
        let! _ := infer_sort G' A in
        tret tt
    end.

  Definition check_type (G : ctx) (A : term) : M unit :=
    match A with
    | Srt s => if spec_sort S s then tret tt else reject (ENotInSystem s)
    | _ => let! _ := infer_sort G A in tret tt
    end.

  Definition infer_in (G : ctx) (t : term) : M term :=
    let! _ := check_ctx G in
    let! _ := temit (EvTerm t) in
    infer G t.

  Definition check_in (G : ctx) (t T : term) : M unit :=
    let! _ := check_ctx G in
    let! _ := temit (EvExpected T) in
    let! _ := check_type G T in
    let! _ := temit (EvTerm t) in
    check G t T.
End Check.

(** The entry points: validate the inputs, then infer or check. *)

Definition run_answer {A} (m : traced event failure A) : list event * answer A :=
  let (log, r) := run_traced m in (log, to_answer r).

Definition run_infer (S : spec) (sg : signature) (fuel : nat) (G : ctx) (t : term)
  : list event * answer term :=
  run_answer (infer_in S sg fuel G t).

Definition run_check (S : spec) (sg : signature) (fuel : nat) (G : ctx) (t T : term)
  : list event * answer unit :=
  run_answer (check_in S sg fuel G t T).
