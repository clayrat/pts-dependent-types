(** * The PTS checker: [infer] and [check]

    One program for every specification: sorts, axioms and Π-rules are
    looked up in [S], and the primitives Void, Unit, Bool are accepted only
    when [spec_prim S] switches them on.  The rules are those of the
    annotated kernel PTS.Bidir.

    Recursion is structural on the term; [fuel] bounds only the evaluation
    done for types, by [whnf] (unfolding a type to a sort or a Π) and by
    [convert] (conversion).  Running out of it is not an error: a run
    ends in one of three answers, [Accepted], [Rejected] with a
    diagnostic, or [Undecided] when the fuel ran out.  Only types are
    evaluated: an argument is checked against the domain and
    then substituted into the codomain, never reduced.

    Both modes are one function [tc]: [tc Γ t None] synthesizes, and
    [tc Γ t (Some T)] checks against [T].  The synthesis rules are written
    once, in the thunk [synth]; checking a non-λ runs it and compares.
    (Separate mutual [infer] and [check] would have to repeat every
    synthesis rule inside [check], since a call [infer Γ t] on the term
    [check] recurses on violates the guard condition.)

    The run is traced: axioms and rules consulted, types unfolded to a
    sort or a Π (with the type before unfolding), arguments checked,
    codomains instantiated, conversions passed (with the common form both
    sides reach), and the result families of eliminators (with their
    sort: a universe means large elimination).

    The entry points [run_infer] and [run_check] validate the context and
    the expected type before typing the term. *)

From Stdlib Require Import List.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Spec Eval.

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
| EBadFamily : term -> term -> term -> error.
    (** result family, expected domain (Void, Unit or Bool), actual domain *)

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
| EvFamily : term -> term -> sort -> event.      (** result family [C] over [D] into [s] *)

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

  (** [T], the type of [t], unfolded to a sort. *)
  Definition as_sort (t T : term) : M sort :=
    match whnf fuel T with
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
    match whnf fuel T with
    | HeadForm (Pi A B) => let! _ := temit (EvUnfoldPi t T A B) in tret (A, B)
    | HeadForm T' => reject (ENotAPi t T')
    | HeadOutOfFuel _ => no_fuel t
    end.

  (** [t] has the inferred type [A] and the expected type [T]. *)
  Definition check_conv (t A T : term) : M unit :=
    match convert fuel A T with
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
    match convert fuel D D0 with
    | ConvEqual _ =>
        let! s := as_sort C K in
        temit (EvFamily C D0 s)
    | ConvOutOfFuel => no_fuel C
    | _ => reject (EBadFamily C D0 D)
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
      end in
    match expected, t with
    | None, _ => synth tt
    | Some T, Lam b =>
        let! p := as_pi t T in
        let (A, B) := p in
        let! _ := tc (A :: G) b (Some B) in
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

Definition run_infer (S : spec) (fuel : nat) (G : ctx) (t : term) : list event * answer term :=
  run_answer (infer_in S fuel G t).

Definition run_check (S : spec) (fuel : nat) (G : ctx) (t T : term) : list event * answer unit :=
  run_answer (check_in S fuel G t T).
