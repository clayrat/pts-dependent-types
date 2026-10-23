(** * Families: parameters, indices and functional recursive fields

    ℕ has no parameters, no indices, and its recursive field has an empty
    telescope, so it leaves most of the ι-scheme idle: the lifts under the
    positions ȳ of a recursive field, and the instantiation of its indices
    v̄ with the positions, the earlier fields and the parameters.  Three
    hand-written declarations, over the ℕ of MLTT/Constants.v, exercise
    them:

    - [Vec (A : Type₀) : ℕ → Type₀] with [nil : Vec A zero] and
      [cons : Π(n : ℕ)(x : A)(xs : Vec A n). Vec A (succ n)]: a parameter
      and an index; the index of [xs] is the earlier field [n];
    - [W (A : Type₀) (B : A → Type₀) : Type₀] with
      [sup : Π(a : A)(f : B a → W A B). W A B]: a recursive field with
      one position, whose domain mentions a parameter and an earlier field;
    - [Tr (A : Type₀) (h : A → A → A) : A → Type₀] with
      [leaf : Π(a : A). Tr A h a],
      [node : Π(a : A)(f : Πy:A. Tr A h (h a y)). Tr A h a] and
      [fork : Π(a : A)(f : Πy z:A. Tr A h (h (h a y) z)). Tr A h a] and
      [twin : Π(a : A)(l : Πy:A. Tr A h (h a y))(b : A)(r : Πy:A. Tr A h (h b y)).
       Tr A h (h a b)]: the index [h a y] of a recursive field mentions
      its position [y], the earlier field [a] and the parameter [h] at
      once; [fork] has two positions, in an order the index tells apart;
      in [twin] a field follows a recursive one, so the method takes
      [a, l, ih_l, b, r, ih_r] and the index of [r] reaches past [l].

    For each constructor the ι-rule is checked on open terms three ways:
    the kernel's contraction is syntactically the right side written by
    hand, the two sides are convertible, and both check against the one
    type [P ū (c Δ ā)].  Closed computations follow: the negation of a
    vector under a motive that depends on the index, ℕ as a W-type, where
    the hypothesis of [succ_W] is applied to [tt], and trees whose leaves
    are found through [h], at one position and at two. *)

From Stdlib Require Import String List Bool.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Spec Signature Reduction Eval Bidir Check CheckSound.
From DepTypes.Configs Require Import Predicative.
From DepTypes.SystemU Require Import Looping.
From DepTypes.MLTT Require Import Choose Constants.

Open Scope string_scope.
Open Scope nterm_scope.

Definition family_fuel : nat := 200.

(** ** Vectors *)

Definition Vec (A n : nterm) : nterm := NConst (Ind "Vec") A n.
Definition vnil (A : nterm) : nterm := NConst (Ctor "Vec" "nil") A.
Definition vcons (A n x xs : nterm) : nterm := NConst (Ctor "Vec" "cons") A n x xs.
Definition elim_vec : nterm := NConst (Elim "Vec" 0).

Definition vec_desc : ind_desc := {|
  ind_name := "Vec";
  ind_params := [Srt (Univ 0)];
  ind_indices := [build ["A"] Nat];
  ind_level := 0;
  ind_ctors := [
    {| ctor_name := "nil"; ctor_fields := []; ctor_indices := [build ["A"] zero] |};
    {| ctor_name := "cons";
       ctor_fields := [FArg (build ["A"] Nat); FArg (build ["n"; "A"] "A");
                       FRec [] [build ["x"; "n"; "A"] "n"]];
       ctor_indices := [build ["xs"; "x"; "n"; "A"] (succ "n")] |} ] |}.

Definition vec_motive : nterm := Π "n" : Nat, Vec "A" "n" ~> Type@ 0.
Definition vec_cons_method : nterm :=
  Π "n" : Nat, Π "x" : "A", Π "xs" : Vec "A" "n", "P" "n" "xs" ~> "P" (succ "n") (vcons "A" "n" "x" "xs").

Definition elim_vec_ty : nterm :=
  Π "A" : Type@ 0, Π "P" : vec_motive, "P" zero (vnil "A") ~> vec_cons_method ~>
  Π "n" : Nat, Π "v" : Vec "A" "n", "P" "n" "v".

(** ** W-types *)

Definition W (A B : nterm) : nterm := NConst (Ind "W") A B.
Definition sup (A B a f : nterm) : nterm := NConst (Ctor "W" "sup") A B a f.
Definition elim_w : nterm := NConst (Elim "W" 0).

Definition w_desc : ind_desc := {|
  ind_name := "W";
  ind_params := [Srt (Univ 0); build ["A"] ("A" ~> Type@ 0)];
  ind_indices := [];
  ind_level := 0;
  ind_ctors := [
    {| ctor_name := "sup";
       ctor_fields := [FArg (build ["B"; "A"] "A"); FRec [build ["a"; "B"; "A"] ("B" "a")] []];
       ctor_indices := [] |} ] |}.

Definition w_method : nterm :=
  Π "a" : "A", Π "f" : ("B" "a" ~> W "A" "B"), (Π "b" : "B" "a", "P" ("f" "b")) ~> "P" (sup "A" "B" "a" "f").

Definition elim_w_ty : nterm :=
  Π "A" : Type@ 0, Π "B" : ("A" ~> Type@ 0), Π "P" : (W "A" "B" ~> Type@ 0), w_method ~>
  Π "w" : W "A" "B", "P" "w".

(** ** Trees indexed through a parameter *)

Definition Tr (A h x : nterm) : nterm := NConst (Ind "Tr") A h x.
Definition leaf (A h a : nterm) : nterm := NConst (Ctor "Tr" "leaf") A h a.
Definition node (A h a f : nterm) : nterm := NConst (Ctor "Tr" "node") A h a f.
Definition fork (A h a f : nterm) : nterm := NConst (Ctor "Tr" "fork") A h a f.
Definition twin (A h a l b r : nterm) : nterm := NConst (Ctor "Tr" "twin") A h a l b r.
Definition elim_tr : nterm := NConst (Elim "Tr" 0).

Definition tr_desc : ind_desc := {|
  ind_name := "Tr";
  ind_params := [Srt (Univ 0); build ["A"] ("A" ~> "A" ~> "A")];
  ind_indices := [build ["h"; "A"] "A"];
  ind_level := 0;
  ind_ctors := [
    {| ctor_name := "leaf"; ctor_fields := [FArg (build ["h"; "A"] "A")];
       ctor_indices := [build ["a"; "h"; "A"] "a"] |};
    {| ctor_name := "node";
       ctor_fields := [FArg (build ["h"; "A"] "A");
                       FRec [build ["a"; "h"; "A"] "A"] [build ["y"; "a"; "h"; "A"] ("h" "a" "y")]];
       ctor_indices := [build ["f"; "a"; "h"; "A"] "a"] |};
    {| ctor_name := "fork";
       ctor_fields := [FArg (build ["h"; "A"] "A");
                       FRec [build ["a"; "h"; "A"] "A"; build ["y"; "a"; "h"; "A"] "A"]
                            [build ["z"; "y"; "a"; "h"; "A"] ("h" ("h" "a" "y") "z")]];
       ctor_indices := [build ["f"; "a"; "h"; "A"] "a"] |};
    {| ctor_name := "twin";
       ctor_fields := [FArg (build ["h"; "A"] "A");
                       FRec [build ["a"; "h"; "A"] "A"] [build ["y"; "a"; "h"; "A"] ("h" "a" "y")];
                       FArg (build ["l"; "a"; "h"; "A"] "A");
                       FRec [build ["b"; "l"; "a"; "h"; "A"] "A"] [build ["y"; "b"; "l"; "a"; "h"; "A"] ("h" "b" "y")]];
       ctor_indices := [build ["r"; "b"; "l"; "a"; "h"; "A"] ("h" "a" "b")] |} ] |}.

Definition tr_motive : nterm := Π "x" : "A", Tr "A" "h" "x" ~> Type@ 0.
Definition tr_leaf_method : nterm := Π "a" : "A", "P" "a" (leaf "A" "h" "a").
Definition tr_node_method : nterm :=
  Π "a" : "A", Π "f" : (Π "y" : "A", Tr "A" "h" ("h" "a" "y")),
  (Π "y" : "A", "P" ("h" "a" "y") ("f" "y")) ~> "P" "a" (node "A" "h" "a" "f").
Definition tr_fork_method : nterm :=
  Π "a" : "A", Π "f" : (Π "y" : "A", Π "z" : "A", Tr "A" "h" ("h" ("h" "a" "y") "z")),
  (Π "y" : "A", Π "z" : "A", "P" ("h" ("h" "a" "y") "z") ("f" "y" "z")) ~> "P" "a" (fork "A" "h" "a" "f").

Definition tr_twin_method : nterm :=
  Π "a" : "A", Π "l" : (Π "y" : "A", Tr "A" "h" ("h" "a" "y")),
  (Π "y" : "A", "P" ("h" "a" "y") ("l" "y")) ~>
  Π "b" : "A", Π "r" : (Π "y" : "A", Tr "A" "h" ("h" "b" "y")),
  (Π "y" : "A", "P" ("h" "b" "y") ("r" "y")) ~>
  "P" ("h" "a" "b") (twin "A" "h" "a" "l" "b" "r").

Definition elim_tr_ty : nterm :=
  Π "A" : Type@ 0, Π "h" : ("A" ~> "A" ~> "A"), Π "P" : tr_motive,
  tr_leaf_method ~> tr_node_method ~> tr_fork_method ~> tr_twin_method ~>
  Π "x" : "A", Π "t" : Tr "A" "h" "x", "P" "x" "t".

(** ** The signature *)

Definition family_entries : list entry :=
  [EElim "Tr" 0 (build [] elim_tr_ty) true; EInd tr_desc;
   EElim "W" 0 (build [] elim_w_ty) true; EInd w_desc;
   EElim "Vec" 0 (build [] elim_vec_ty) true; EInd vec_desc] ++ base_entries true.

Definition sg_families : signature := {| sig_entries := family_entries; sig_wf := eq_refl |}.

(** ** The types of the declarations *)

(** Every constant has a type that is a type. *)
Definition is_type (A : term) : bool :=
  match snd (run_infer predicative sg_families family_fuel [] A) with
  | Accepted (Srt _) => true
  | _ => false
  end.

Example constant_types_are_types :
  forallb (fun g => match sig_type sg_families g with Some A => is_type A | None => false end)
    [Ind "Vec"; Ctor "Vec" "nil"; Ctor "Vec" "cons"; Elim "Vec" 0;
     Ind "W"; Ctor "W" "sup"; Elim "W" 0;
     Ind "Tr"; Ctor "Tr" "leaf"; Ctor "Tr" "node"; Ctor "Tr" "fork"; Ctor "Tr" "twin"; Elim "Tr" 0] = true.
Proof. vm_compute. reflexivity. Qed.

(** The types of constructors rebuilt from the descriptions are the ones
    written by hand: the recursive fields apply the family to the
    parameters past their positions and the earlier fields. *)
Definition ctor_type_is (D c : string) (A : nterm) : bool :=
  match sig_type sg_families (Ctor D c) with Some B => term_eqb B (build [] A) | None => false end.

Example constructor_types :
  ctor_type_is "Vec" "cons" (Π "A" : Type@ 0, Π "n" : Nat, Π "x" : "A", Π "xs" : Vec "A" "n",
                             Vec "A" (succ "n")) &&
  ctor_type_is "W" "sup" (Π "A" : Type@ 0, Π "B" : ("A" ~> Type@ 0), Π "a" : "A",
                          Π "f" : ("B" "a" ~> W "A" "B"), W "A" "B") &&
  ctor_type_is "Tr" "leaf" (Π "A" : Type@ 0, Π "h" : ("A" ~> "A" ~> "A"), Π "a" : "A", Tr "A" "h" "a") &&
  ctor_type_is "Tr" "node" (Π "A" : Type@ 0, Π "h" : ("A" ~> "A" ~> "A"), Π "a" : "A",
                            Π "f" : (Π "y" : "A", Tr "A" "h" ("h" "a" "y")), Tr "A" "h" "a") &&
  ctor_type_is "Tr" "fork" (Π "A" : Type@ 0, Π "h" : ("A" ~> "A" ~> "A"), Π "a" : "A",
                            Π "f" : (Π "y" : "A", Π "z" : "A", Tr "A" "h" ("h" ("h" "a" "y") "z")),
                            Tr "A" "h" "a") &&
  ctor_type_is "Tr" "twin" (Π "A" : Type@ 0, Π "h" : ("A" ~> "A" ~> "A"), Π "a" : "A",
                            Π "l" : (Π "y" : "A", Tr "A" "h" ("h" "a" "y")), Π "b" : "A",
                            Π "r" : (Π "y" : "A", Tr "A" "h" ("h" "b" "y")), Tr "A" "h" ("h" "a" "b")) = true.
Proof. vm_compute. reflexivity. Qed.

(** ** ι on open terms *)

Definition vec_rule_ctx : list (string * nterm) :=
  [("xs", Vec "A" "n"); ("x", NVar "A"); ("n", Nat);
   ("mc", vec_cons_method); ("mn", "P" zero (vnil "A")); ("P", vec_motive); ("A", Type@ 0)].

Definition w_rule_ctx : list (string * nterm) :=
  [("f", "B" "a" ~> W "A" "B"); ("a", NVar "A"); ("m", w_method);
   ("P", W "A" "B" ~> Type@ 0); ("B", "A" ~> Type@ 0); ("A", Type@ 0)].

Definition tr_methods_ctx : list (string * nterm) :=
  [("mt", tr_twin_method); ("mf", tr_fork_method); ("mn", tr_node_method); ("ml", tr_leaf_method);
   ("P", tr_motive);
   ("h", "A" ~> "A" ~> "A"); ("A", Type@ 0)].

Definition tr_rule_ctx : list (string * nterm) :=
  ("f", Π "y" : "A", Tr "A" "h" ("h" "a" "y")) :: ("a", NVar "A") :: tr_methods_ctx.

Definition tr_fork_ctx : list (string * nterm) :=
  ("f", Π "y" : "A", Π "z" : "A", Tr "A" "h" ("h" ("h" "a" "y") "z")) :: ("a", NVar "A") :: tr_methods_ctx.

Definition tr_twin_ctx : list (string * nterm) :=
  [("r", Π "y" : "A", Tr "A" "h" ("h" "b" "y")); ("b", NVar "A");
   ("l", Π "y" : "A", Tr "A" "h" ("h" "a" "y")); ("a", NVar "A")] ++ tr_methods_ctx.

Definition accepted (a : answer unit) : bool := match a with Accepted _ => true | _ => false end.

Definition checks (g : list (string * nterm)) (t A : nterm) : bool :=
  accepted (snd (run_check predicative sg_families family_fuel (in_ctx g) (term_in g t) (term_in g A))).

(** The ι-rule of a constructor in the context [g]: the kernel contracts
    [lhs] to [rhs] syntactically, the two are convertible, and both check
    against [ty], the motive at the constructor. *)
Definition iota_rule_holds (g : list (string * nterm)) (lhs rhs ty : nterm) : bool :=
  match iota sg_families (term_in g lhs) with
  | Some u => term_eqb u (term_in g rhs)
  | None => false
  end &&
  match convert sg_families family_fuel (term_in g lhs) (term_in g rhs) with
  | ConvEqual _ => true
  | _ => false
  end &&
  checks g lhs ty && checks g rhs ty.

Example iota_vec :
  iota_rule_holds vec_rule_ctx (elim_vec "A" "P" "mn" "mc" zero (vnil "A")) "mn" ("P" zero (vnil "A")) &&
  iota_rule_holds vec_rule_ctx
    (elim_vec "A" "P" "mn" "mc" (succ "n") (vcons "A" "n" "x" "xs"))
    ("mc" "n" "x" "xs" (elim_vec "A" "P" "mn" "mc" "n" "xs"))
    ("P" (succ "n") (vcons "A" "n" "x" "xs")) = true.
Proof. vm_compute. reflexivity. Qed.

(** The hypothesis of [f] abstracts its position: the eliminator's
    arguments are lifted past [b], and [f] is applied to it. *)
Example iota_w :
  iota_rule_holds w_rule_ctx
    (elim_w "A" "B" "P" "m" (sup "A" "B" "a" "f"))
    ("m" "a" "f" (λ "b", elim_w "A" "B" "P" "m" ("f" "b")))
    ("P" (sup "A" "B" "a" "f")) = true.
Proof. vm_compute. reflexivity. Qed.

(** The index [h a y] of the hypothesis takes its position [y], the field
    [a] and the parameter [h] from three different places. *)
Definition elim_tr_at (x t : nterm) : nterm := elim_tr "A" "h" "P" "ml" "mn" "mf" "mt" x t.

Example iota_tr :
  iota_rule_holds tr_rule_ctx (elim_tr_at "a" (leaf "A" "h" "a")) ("ml" "a")
    ("P" "a" (leaf "A" "h" "a")) &&
  iota_rule_holds tr_rule_ctx
    (elim_tr_at "a" (node "A" "h" "a" "f"))
    ("mn" "a" "f" (λ "y", elim_tr_at ("h" "a" "y") ("f" "y")))
    ("P" "a" (node "A" "h" "a" "f")) = true.
Proof. vm_compute. reflexivity. Qed.

(** Two positions: the hypothesis abstracts both, in order. *)
Example iota_tr_fork :
  iota_rule_holds tr_fork_ctx
    (elim_tr_at "a" (fork "A" "h" "a" "f"))
    ("mf" "a" "f" (λ "y", λ "z", elim_tr_at ("h" ("h" "a" "y") "z") ("f" "y" "z")))
    ("P" "a" (fork "A" "h" "a" "f")) = true.
Proof. vm_compute. reflexivity. Qed.

(** A field after a recursive one: each recursive field is followed by its
    hypothesis, and the index of [r] finds [b] and [h] past [l]. *)
Example iota_tr_twin :
  iota_rule_holds tr_twin_ctx
    (elim_tr_at ("h" "a" "b") (twin "A" "h" "a" "l" "b" "r"))
    ("mt" "a" "l" (λ "y", elim_tr_at ("h" "a" "y") ("l" "y"))
          "b" "r" (λ "y", elim_tr_at ("h" "b" "y") ("r" "y")))
    ("P" ("h" "a" "b") (twin "A" "h" "a" "l" "b" "r")) = true.
Proof. vm_compute. reflexivity. Qed.

(** The typing of the sides tells the instantiation of the index and the
    order of the positions apart: with [h y a] in place of [h a y], or
    with [f z y] in place of [f y z], the right side is ill-typed. *)
Example iota_tr_wrong_sides :
  checks tr_rule_ctx ("mn" "a" "f" (λ "y", elim_tr_at ("h" "y" "a") ("f" "y")))
    ("P" "a" (node "A" "h" "a" "f")) ||
  checks tr_fork_ctx ("mf" "a" "f" (λ "y", λ "z", elim_tr_at ("h" ("h" "a" "y") "z") ("f" "z" "y")))
    ("P" "a" (fork "A" "h" "a" "f")) = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Closed computations *)

Definition checks_closed (t A : nterm) : bool := checks [] t A.

(** Negation of a vector: the motive [λn _. Vec Bool n] depends on the
    index. *)
Definition bnot (x : nterm) : nterm := NElimBool ((λ "_", NBool) ∷ (NBool ~> Type@ 0)) NFalse NTrue x.
Definition two_bools : nterm := vcons NBool (succ zero) NTrue (vcons NBool zero NFalse (vnil NBool)).
Definition vnot : nterm :=
  elim_vec NBool ((λ "n", λ "v", Vec NBool "n") ∷ (Π "n" : Nat, Vec NBool "n" ~> Type@ 0)) (vnil NBool)
    (λ "n", λ "x", λ "xs", λ "r", vcons NBool "n" (bnot "x") "r").

Example vnot_computes :
  checks_closed (vnot (succ (succ zero)) two_bools) (Vec NBool (succ (succ zero))) = true /\
  normalize sg_families family_fuel (build [] (vnot (succ (succ zero)) two_bools))
  = NormalForm (build [] (vcons NBool (succ zero) NFalse (vcons NBool zero NTrue (vnil NBool)))).
Proof. split; vm_compute; reflexivity. Qed.

(** ℕ as a W-type: labels Bool, positions [B b = elimBool (λ_. Type₀) Unit
    Void b]; the method matches on the label to apply the hypothesis to
    [tt] at a successor. *)
Definition positions : nterm :=
  (λ "b", NElimBool ((λ "z", Type@ 0) ∷ (NBool ~> Type@ 1)) NUnit NVoid "b") ∷ (NBool ~> Type@ 0).
Definition nat_w : nterm := W NBool positions.
Definition zero_w : nterm :=
  sup NBool positions NFalse (λ "v", NElimVoid ((λ "_", nat_w) ∷ (NVoid ~> Type@ 0)) "v").
Definition succ_w (n : nterm) : nterm := sup NBool positions NTrue (λ "_", n).
Definition to_nat : nterm :=
  elim_w NBool positions ((λ "_", Nat) ∷ (nat_w ~> Type@ 0))
    (λ "a", λ "f", λ "r",
       NElimBool ((λ "c", (positions "c" ~> Nat) ~> Nat) ∷ (NBool ~> Type@ 0))
         (λ "r'", succ ("r'" NTt)) (λ "r'", zero) "a" "r").

Example nat_w_computes :
  checks_closed (succ_w (succ_w zero_w)) nat_w && checks_closed (to_nat (succ_w (succ_w zero_w))) Nat = true /\
  normalize sg_families family_fuel (build [] (to_nat (succ_w (succ_w zero_w))))
  = NormalForm (build [] (succ (succ zero))).
Proof. split; vm_compute; reflexivity. Qed.

(** Trees over [h = λx y. y]: the subtree of [node] at [y] is the leaf
    [y], that of [fork] at [y z] the leaf [z]; the methods pick the
    subtree at [false], and at [false true]. *)
Definition second : nterm := (λ "x", λ "y", "y") ∷ (NBool ~> NBool ~> NBool).
Definition tree : nterm := node NBool second NTrue (λ "y", leaf NBool second "y").
Definition fork_tree : nterm := fork NBool second NFalse (λ "y", λ "z", leaf NBool second "z").
Definition label : nterm :=
  elim_tr NBool second ((λ "x", λ "t", NBool) ∷ (Π "x" : NBool, Tr NBool second "x" ~> Type@ 0))
    (λ "a", "a") (λ "a", λ "f", λ "r", "r" NFalse) (λ "a", λ "f", λ "r", "r" NFalse NTrue)
    (λ "a", λ "l", λ "il", λ "b", λ "r", λ "ir", "ir" NTrue).

Example tree_label_computes :
  checks_closed tree (Tr NBool second NTrue) && checks_closed (label NTrue tree) NBool = true /\
  normalize sg_families family_fuel (build [] (label NTrue tree)) = NormalForm BFalse.
Proof. split; vm_compute; reflexivity. Qed.

(** The order of the positions shows in the result: [true], not [false]. *)
Example fork_label_computes :
  checks_closed fork_tree (Tr NBool second NFalse) && checks_closed (label NFalse fork_tree) NBool = true /\
  normalize sg_families family_fuel (build [] (label NFalse fork_tree)) = NormalForm BTrue.
Proof. split; vm_compute; reflexivity. Qed.

(** In [twin] the method reaches the hypothesis of the second recursive
    field, and the index [h a b] is that of the tree. *)
Definition twin_tree : nterm :=
  twin NBool second NFalse (λ "y", leaf NBool second "y") NTrue (λ "y", leaf NBool second "y").

Example twin_label_computes :
  checks_closed twin_tree (Tr NBool second NTrue) && checks_closed (label NTrue twin_tree) NBool = true /\
  normalize sg_families family_fuel (build [] (label NTrue twin_tree)) = NormalForm BTrue.
Proof. split; vm_compute; reflexivity. Qed.
