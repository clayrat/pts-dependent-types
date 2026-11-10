(** * The guard of fix on examples

    The guard of PTS/Guard.v on the signatures of MLTT/Constants.v,
    MLTT/Families.v and CIC/Match.v (with [plus]):

    - accepted: [half] directly, with its call two fields down, where
      lecture 7 needed the history; [nat_rect], [plus], [append] and
      [copy] of CIC/Match.v, the last one with its call under a λ; the
      size of a tree of [Tr], whose [fork] has a functional field with
      two positions; a call under several λ and inside the branches of an
      inner match;
    - refused by the checker, after typing: a call on the structural
      argument itself, [g (succ k) = g (pred k)], a partial call, the bare
      function passed to another one, an invalid call inside the argument
      of a valid one, and a call on a variable that shadows a field;
    - refused by the guard alone, on bodies that do not type: a call on a
      non-recursive field, a functional field applied to one of its two
      positions, and a body short of its leading λ.

    Through any of these, the strict positivity of declarations is a
    separate check of the registration (elim-inductive-types). *)

From Stdlib Require Import String List Bool.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Spec Signature Reduction Eval EvalSrc Guard Check Build Runs.
From DepTypes.Configs Require Import Predicative.
From DepTypes.MLTT Require Import Constants Families.
From DepTypes.CIC Require Import Match.

Open Scope string_scope.
Open Scope nterm_scope.

Definition nat_case (x : nterm) (z : nterm) (s : nterm) : nterm :=
  NCase "Nat" (Univ 0) (λ "_", Nat) x [z; s].

(** The guard of a closed fix. *)
Definition guard_of (sg : signature) (t : nterm) : result guard_error unit :=
  match build [] t with
  | Fix _ k b => guard_fix sg k b
  | _ => Ok tt
  end.

(** ** Accepted *)

(** [half (n + 2) = succ (half n)]: the call is on a field of a field,
    directly. *)
Definition half : nterm :=
  NFix "half" (Nat ~> Nat) 0
    (λ "n", nat_case "n" zero (λ "m", nat_case "m" zero (λ "k", succ ("half" "k")))).

Example half_accepted :
  infers predicative sg_nat match_fuel [] half = Accepted (build [] (Nat ~> Nat)) /\
  map (fun n => normalize sg_nat match_fuel (build [] (half (nat_numeral n)))) [0; 1; 4; 5]
  = map (fun n => NormalForm (build [] (nat_numeral n))) [0; 0; 2; 2] /\
  eval_src sg_nat match_fuel (build [] (half (nat_numeral 5))) = CbvValue (build [] (nat_numeral 2)).
Proof. vm_compute. repeat split. Qed.

Example match_programs_guarded :
  map (guard_of sg_match) [nat_rect 0; plus_fix; append; copy] = [Ok tt; Ok tt; Ok tt; Ok tt].
Proof. vm_compute. reflexivity. Qed.

(** The size of a tree: the functional field of [node] applied to its
    position, that of [fork] to both of its positions. *)
Definition size_ty : nterm :=
  Π "A" : Type@ 0, Π "h" : ("A" ~> "A" ~> "A"), Π "x" : "A", Tr "A" "h" "x" ~> Nat.

Definition size : nterm :=
  NFix "size" size_ty 3
    (λ "A", λ "h", λ "x", λ "t",
       NCase "Tr" (Univ 0) (λ "i", λ "_", Nat) "t"
         [λ "a", succ zero;
          λ "a", λ "f", "size" "A" "h" ("h" "a" "a") ("f" "a");
          λ "a", λ "f", "size" "A" "h" ("h" ("h" "a" "a") "a") ("f" "a" "a");
          λ "a", λ "l", λ "b", λ "r",
            NConst (Def "plus") ("size" "A" "h" ("h" "a" "a") ("l" "a")) ("size" "A" "h" ("h" "b" "b") ("r" "b"))]).

Example size_accepted :
  infers predicative sg_match match_fuel [] size = Accepted (build [] size_ty) /\
  map (fun '(x, t) => normalize sg_match match_fuel (build [] (size NBool second x t)))
    [(NTrue, tree); (NFalse, fork_tree); (NTrue, twin_tree)]
  = map (fun n => NormalForm (build [] (nat_numeral n))) [1; 1; 2].
Proof. vm_compute. split; reflexivity. Qed.

(** Several λ and an inner match between the field and the call: the
    marks follow their variables. *)
Definition under_binders : nterm :=
  NFix "f" (Nat ~> Nat ~> Nat) 0
    (λ "n", λ "m",
       nat_case "n" "m"
         (λ "k", ((λ "y", λ "z", nat_case "z" ("f" "k" "y") (λ "w", "f" "k" "w"))
                  ∷ (Nat ~> Nat ~> Nat)) "m" "m")).

Example under_binders_accepted :
  infers predicative sg_nat match_fuel [] under_binders = Accepted (build [] (Nat ~> Nat ~> Nat)).
Proof. vm_compute. reflexivity. Qed.

(** ** Refused after typing *)

Definition rejection (a : answer term) : option guard_error :=
  match refusal a with Some (ENotGuarded _ e) => Some e | _ => None end.

Definition pred_ann : nterm := (λ "n", nat_case "n" zero (λ "k", "k")) ∷ (Nat ~> Nat).
Definition apply_to : nterm := (λ "h", λ "y", "h" "y") ∷ ((Nat ~> Nat) ~> Nat ~> Nat).

(** [g (succ k) = g (pred k)]: the origin is lost through [pred]. *)
Definition g_pred : nterm :=
  NFix "g" (Nat ~> Nat) 0 (λ "n", nat_case "n" zero (λ "k", "g" (pred_ann "k"))).

(** A partial call [f m] with the structural argument second, and the
    bare [f] passed to [apply_to]. *)
Definition partial : nterm :=
  NFix "f" (Nat ~> Nat ~> Nat) 1 (λ "m", λ "n", nat_case "n" "m" (λ "k", apply_to ("f" "m") "k")).

Definition bare : nterm :=
  NFix "f" (Nat ~> Nat) 0 (λ "n", nat_case "n" zero (λ "k", apply_to "f" "k")).

(** [f k (f n m)]: the outer call is valid, the inner one is on [n]. *)
Definition nested : nterm :=
  NFix "f" (Nat ~> Nat ~> Nat) 0 (λ "n", λ "m", nat_case "n" "m" (λ "k", "f" "k" ("f" "n" "m"))).

(** The λ binding [k] again: the call is on the new [k]. *)
Definition shadowed : nterm :=
  NFix "f" (Nat ~> Nat) 0 (λ "n", nat_case "n" zero (λ "k", ((λ "k", "f" "k") ∷ (Nat ~> Nat)) zero)).

Example refused_after_typing :
  map (fun t => rejection (infers predicative sg_nat match_fuel [] t)) [loop; g_pred; partial; bare; nested; shadowed]
  = [Some (GNotSubterm (App (Var 1) (Var 0)) (Var 0));
     Some (GNotSubterm (App (Var 2) (App (build [] pred_ann) (Var 0))) (App (build [] pred_ann) (Var 0)));
     Some (GPartialCall (App (Var 3) (Var 2)));
     Some (GPartialCall (Var 2));
     Some (GNotSubterm (App (App (Var 3) (Var 2)) (Var 1)) (Var 2));
     Some (GNotSubterm (App (Var 3) (Var 0)) (Var 0))].
Proof. vm_compute. reflexivity. Qed.

(** ** Refused by the guard alone *)

(** A call on the non-recursive field [x] of [cons], and the field [f] of
    [fork] applied to one of its two positions. *)
Definition nonrec_field : nterm :=
  NFix "f" (Π "n" : Nat, Vec Nat "n" ~> Nat) 1
    (λ "n", λ "v", NCase "Vec" (Univ 0) (λ "i", λ "_", Nat) "v"
                     [zero; λ "k", λ "x", λ "xs", "f" "k" "x"]).

Definition half_position : nterm :=
  NFix "size" size_ty 3
    (λ "A", λ "h", λ "x", λ "t",
       NCase "Tr" (Univ 0) (λ "i", λ "_", Nat) "t"
         [λ "a", zero; λ "a", λ "f", zero; λ "a", λ "f", "size" "A" "h" "a" ("f" "a"); λ "a", λ "l", λ "b", λ "r", zero]).

Example refused_by_guard :
  guard_of sg_match nonrec_field = Err (GNotSubterm (App (App (Var 5) (Var 2)) (Var 1)) (Var 1)) /\
  guard_of sg_match half_position
  = Err (GNotSubterm (App (App (App (App (Var 6) (Var 5)) (Var 4)) (Var 1)) (App (Var 0) (Var 1)))
                     (App (Var 0) (Var 1))).
Proof. vm_compute. split; reflexivity. Qed.

(** A body short of its [k + 1] leading λ is refused by the guard itself,
    where the missing λ should be; the checker refuses it before typing
    the body ([EFixBody] of [fix_refusals] in CIC/Match.v). *)
Example short_body_refused :
  guard_fix ∅ 0 (Var 0) = Err (GShortBody (Var 0)) /\
  guard_fix sg_nat 1 (Lam (Var 0)) = Err (GShortBody (Var 0)).
Proof. split; reflexivity. Qed.
