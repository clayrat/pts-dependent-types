(** * Translation of PCF into U⁻

    Types: [⟦ℕ⟧ = Nat] (Church numerals), [⟦A ⇒ B⟧ = ⟦A⟧ → ⟦B⟧].  Terms
    keep their shape and their names: variables, unannotated λ,
    application and annotations go to the same formers of the named
    syntax of PTS.Named; a literal is a numeral, [succ] and [pred] are
    [csucc] and [cpred], [ifz] is the zero test strict in the whole
    numeral, and [fix_A u] is the looping combinator [L₀ ⟦A⟧ ⟦u⟧].

    The only typed step is [ifz], which needs its result type.  In PCF
    [ifz] only checks, against a known type, so the translator follows the
    bidirectional checker of strictness-pcf: [tr Γ t None] synthesizes a
    type and translates, [tr Γ t (Some A)] checks against [A] and
    translates.  It fails exactly where that checker fails, with its
    error: only well-typed programs are translated.  Both modes are one
    structural function, as in PTS.Check.

    Names are the bridge between the two variable disciplines: a PCF
    variable becomes the variable of the same name, and [resolve] finds
    the nearest binder of that name, as PCF's [lookup] finds the first
    entry.  The encodings pasted in are closed, so they capture nothing,
    and every PCF name, "_" included, is an ordinary name of the target. *)

From Stdlib Require Import String List.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Bidir Check CheckSound.
From DepTypes.Configs Require Import Finite.
From DepTypes.SystemU Require Import Looping Encodings.
From PCF Require Ty Syntax Context Checker.

Open Scope string_scope.
Open Scope nterm_scope.

Notation pcf_ty := PCF.Ty.ty.
Notation pcf_term := PCF.Syntax.term.
Notation pcf_ctx := PCF.Context.ctx.
Notation pcf_error := PCF.Checker.error.
Notation pcf_result := PCF.Checker.result.

Fixpoint tr_ty (A : pcf_ty) : nterm :=
  match A with
  | PCF.Ty.tnat => CNat
  | PCF.Ty.tarr A B => tr_ty A ~> tr_ty B
  end.

Definition pbind {X Y} (r : pcf_result X) (f : X -> pcf_result Y) : pcf_result Y :=
  match r with
  | PCF.Checker.Ok x => f x
  | PCF.Checker.Err e => PCF.Checker.Err e
  end.

Notation "'let%' x ':=' r 'in' body" := (pbind r (fun x => body))
  (at level 200, x name, r at level 100, body at level 200).

(** The translation and the type PCF gives the term (the expected one in
    checking mode). *)
Fixpoint tr (G : pcf_ctx) (t : pcf_term) (expected : option pcf_ty) {struct t}
  : pcf_result (nterm * pcf_ty) :=
  let synth (_ : unit) : pcf_result (nterm * pcf_ty) :=
    match t with
    | PCF.Syntax.tvar x =>
        match PCF.Context.lookup G x with
        | Some A => PCF.Checker.Ok (NVar x, A)
        | None => PCF.Checker.Err (PCF.Checker.E_Unbound x)
        end
    | PCF.Syntax.tnum n => PCF.Checker.Ok (numeral n, PCF.Ty.tnat)
    | PCF.Syntax.tsucc u =>
        let% p := tr G u (Some PCF.Ty.tnat) in PCF.Checker.Ok (csucc (fst p), PCF.Ty.tnat)
    | PCF.Syntax.tpred u =>
        let% p := tr G u (Some PCF.Ty.tnat) in PCF.Checker.Ok (cpred (fst p), PCF.Ty.tnat)
    | PCF.Syntax.tapp f u =>
        let% pf := tr G f None in
        match snd pf with
        | PCF.Ty.tarr A B =>
            let% pu := tr G u (Some A) in PCF.Checker.Ok (NApp (fst pf) (fst pu), B)
        | PCF.Ty.tnat => PCF.Checker.Err (PCF.Checker.E_NotFun f PCF.Ty.tnat)
        end
    | PCF.Syntax.tfix A u =>
        let% p := tr G u (Some (PCF.Ty.tarr A A)) in
        PCF.Checker.Ok (L0 (tr_ty A) (fst p), A)
    | PCF.Syntax.tann u A =>
        let% p := tr G u (Some A) in PCF.Checker.Ok (NAnn (fst p) (tr_ty A), A)
    | PCF.Syntax.tlam _ _ | PCF.Syntax.tifz _ _ _ =>
        PCF.Checker.Err (PCF.Checker.E_NoSynth t)
    end in
  match expected, t with
  | None, _ => synth tt
  | Some B, PCF.Syntax.tlam x u =>
      match B with
      | PCF.Ty.tarr A C =>
          let% p := tr ((x, A) :: G) u (Some C) in PCF.Checker.Ok (NLam x (fst p), B)
      | PCF.Ty.tnat => PCF.Checker.Err (PCF.Checker.E_LamNotFun t PCF.Ty.tnat)
      end
  | Some B, PCF.Syntax.tifz c a b =>
      let% pc := tr G c (Some PCF.Ty.tnat) in
      let% pa := tr G a (Some B) in
      let% pb := tr G b (Some B) in
      PCF.Checker.Ok (ifz (tr_ty B) (fst pc) (fst pa) (fst pb), B)
  | Some B, _ =>
      let% p := synth tt in
      if PCF.Ty.ty_eqb (snd p) B then PCF.Checker.Ok (fst p, B)
      else PCF.Checker.Err (PCF.Checker.E_Mismatch t B (snd p))
  end.

(** ** The translator *)

Inductive tr_error : Type :=
| TrIllTyped : pcf_error -> tr_error     (** the PCF checker rejects the program *)
| TrName : string -> tr_error            (** an unbound name; not for a PCF-checked program *)
| TrTargetRejected : error -> tr_error   (** the U⁻ checker rejects the output *)
| TrTargetUndecided : term -> tr_error.  (** the U⁻ checker runs out of fuel *)

Definition tr_ctx (G : pcf_ctx) : list (string * nterm) :=
  map (fun '(x, A) => (x, tr_ty A)) G.

(** The translation of [Γ ⊢ t ⇓ A] in the PCF checker: the translated
    context and term, as de Bruijn terms. *)
Definition translate (G : pcf_ctx) (t : pcf_term) (A : pcf_ty) : result tr_error (ctx * term) :=
  match tr G t (Some A) with
  | PCF.Checker.Err e => Err (TrIllTyped e)
  | PCF.Checker.Ok (u, _) =>
      match resolve_ctx (tr_ctx G) with
      | Err x => Err (TrName x)
      | Ok (names, G') =>
          match resolve names u with
          | Err x => Err (TrName x)
          | Ok u' => Ok (G', u')
          end
      end
  end.

(** A closed program of type ℕ. *)
Definition translate_program (t : pcf_term) : result tr_error term :=
  match translate [] t PCF.Ty.tnat with
  | Ok (_, u) => Ok u
  | Err e => Err e
  end.

Definition translated_type (A : pcf_ty) : term := build [] (tr_ty A).

(** ** Every output checked

    [translate_checked] runs the U⁻ checker on each output, the
    translated term against the translated type in the translated
    context, and returns the translation only when the checker accepts
    it.  Its success is certified by the soundness of that checker
    ([translate_checked_sound]), independently of the proof that the
    translation preserves typing (PCFTranslation.TranslateSound). *)

Definition translate_checked (fuel : nat) (G : pcf_ctx) (t : pcf_term) (A : pcf_ty)
  : result tr_error (ctx * term) :=
  match translate G t A with
  | Err e => Err e
  | Ok (G', u) =>
      match snd (run_check system_u_minus fuel G' u (translated_type A)) with
      | Accepted _ => Ok (G', u)
      | Rejected e => Err (TrTargetRejected e)
      | Undecided v => Err (TrTargetUndecided v)
      end
  end.

Definition translate_program_checked (fuel : nat) (t : pcf_term) : result tr_error term :=
  match translate_checked fuel [] t PCF.Ty.tnat with
  | Ok (_, u) => Ok u
  | Err e => Err e
  end.

Lemma translate_checked_sound : forall fuel G t A G' u,
  translate_checked fuel G t A = Ok (G', u) ->
  translate G t A = Ok (G', u) /\
  bwf_ctx system_u_minus G' /\ btype system_u_minus G' (translated_type A) /\
  system_u_minus ;; G' ⊢ u ⇓ translated_type A.
Proof.
  intros fuel G t A G' u H. unfold translate_checked in H.
  destruct (translate G t A) as [[G0 u0]|e] eqn:E; [ | discriminate H].
  destruct (snd (run_check system_u_minus fuel G0 u0 (translated_type A))) as [v|e|v] eqn:R;
    try discriminate H.
  injection H as <- <-. split; [reflexivity | ].
  exact (run_check_sound _ _ _ _ _ _ R).
Qed.

Lemma translate_program_checked_sound : forall fuel t u,
  translate_program_checked fuel t = Ok u ->
  system_u_minus ;; [] ⊢ u ⇓ translated_type PCF.Ty.tnat.
Proof.
  intros fuel t u H. unfold translate_program_checked in H.
  destruct (translate_checked fuel [] t PCF.Ty.tnat) as [[G' u0]|e] eqn:E; [ | discriminate H].
  injection H as <-.
  destruct (translate_checked_sound _ _ _ _ _ _ E) as (T & _ & _ & Hc).
  unfold translate in T. destruct (tr [] t (Some PCF.Ty.tnat)) as [[? ?]|?]; [ | discriminate T].
  cbn in T. destruct (resolve [] n) eqn:R; [ | discriminate T].
  injection T as <- <-. exact Hc.
Qed.
