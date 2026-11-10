(* match and fix, assembled independently, as theories/CIC/Match.v:
   nat_rect written with fix and match, plus as a δ-constant, append on
   vectors with its index computed by plus, copy on W, the refused terms,
   and a propositional boolean eliminable into Prop only. *)

open Named
module P = Pts_native
module Co = Constants
module Fa = Families

let nat = Co.nat and zero = Co.zero and succ = Co.succ

let nat_rect_ty = Co.elim_nat_ty_at

let rect_with j branches =
  Fixpoint ("F", nat_rect_ty j, 3,
    abs ["P"; "z"; "s"; "n"]
      (Match ("Nat", P.Univ j, abs ["m"] (Apply (name "P", name "m")), name "n", branches)))

let succ_branch = abs ["m"] (call (name "s") [name "m"; call (name "F") [name "P"; name "z"; name "s"; name "m"]])
let nat_rect j = rect_with j [name "z"; succ_branch]

let rect_ctx = Co.iota_ctx_at

let open_match =
  Match ("Nat", P.Univ 0, abs ["m"] (Apply (name "P", name "m")), name "n",
         [name "z"; abs ["m"] (call (name "s") [name "m"; call (nat_rect 0) [name "P"; name "z"; name "s"; name "m"]])])

let plus_fix =
  Fixpoint ("plus", arrows [nat; nat] nat, 0,
    abs ["n"; "m"]
      (Match ("Nat", P.Univ 0, abs ["_"] nat, name "n",
              [name "m"; abs ["k"] (succ (call (name "plus") [name "k"; name "m"]))])))

let plus a b = call (Const (P.Const (P.Def "plus"))) [a; b]

let signature = Co.add Fa.signature (P.EDef ("plus", build [] (arrows [nat; nat] nat), build [] plus_fix))

let rec nat_numeral k = if k = 0 then zero else succ (nat_numeral (k - 1))

let append_ty =
  pi "A" (universe 0) (pi "n" nat (pi "m" nat
    (arrows [Fa.vec (name "A") (name "n"); Fa.vec (name "A") (name "m")]
       (Fa.vec (name "A") (plus (name "n") (name "m"))))))

let append =
  Fixpoint ("app", append_ty, 3,
    abs ["A"; "n"; "m"; "xs"; "ys"]
      (Match ("Vec", P.Univ 0, abs ["k"; "_"] (Fa.vec (name "A") (plus (name "k") (name "m"))), name "xs",
              [name "ys";
               abs ["k"; "x"; "xs'"]
                 (Fa.vcons (name "A") (plus (name "k") (name "m")) (name "x")
                    (call (name "app") [name "A"; name "k"; name "m"; name "xs'"; name "ys"]))])))

let one_true = Fa.vcons Fa.bool zero (Const P.BTrue) (Fa.vnil Fa.bool)
let one_false = Fa.vcons Fa.bool zero (Const P.BFalse) (Fa.vnil Fa.bool)

let copy_ty = pi "A" (universe 0) (pi "B" (arrow (name "A") (universe 0))
  (arrow (Fa.w (name "A") (name "B")) (Fa.w (name "A") (name "B"))))

let copy =
  Fixpoint ("copy", copy_ty, 2,
    abs ["A"; "B"; "w"]
      (Match ("W", P.Univ 0, abs ["_"] (Fa.w (name "A") (name "B")), name "w",
              [abs ["a"; "f"]
                 (Fa.sup (name "A") (name "B") (name "a")
                    (abs ["b"] (call (name "copy") [name "A"; name "B"; Apply (name "f", name "b")])))])))

(* A motive into Type₁ in a match into Type₀. *)
let wrong_motive =
  Fixpoint ("F", nat_rect_ty 1, 3,
    abs ["P"; "z"; "s"; "n"]
      (Match ("Nat", P.Univ 0, abs ["m"] (Apply (name "P", name "m")), name "n", [name "z"; succ_branch])))

let boolp_desc = {
  P.ind_name = "BoolP"; ind_params = []; ind_indices = []; ind_sort = P.Prp; ind_elim = P.PropOnly;
  ind_ctors = [
    { P.ctor_name = "trueP"; ctor_fields = []; ctor_indices = [] };
    { P.ctor_name = "falseP"; ctor_fields = []; ctor_indices = [] };
  ];
}

let boolp_signature = Co.add P.empty_signature (P.EInd boolp_desc)
let trueP = Const (P.Const (P.Ctor ("BoolP", "trueP")))
let match_boolp s ty a b = Match ("BoolP", s, abs ["_"] ty, trueP, [a; b])

let loop = Fixpoint ("f", arrow nat nat, 0, abs ["n"] (Apply (name "f", name "n")))

(* The guard, as theories/CIC/GuardExamples.v. *)
let nat_case x z s = Match ("Nat", P.Univ 0, abs ["_"] nat, x, [z; s])

let half =
  Fixpoint ("half", arrow nat nat, 0,
    abs ["n"] (nat_case (name "n") zero
                 (abs ["m"] (nat_case (name "m") zero (abs ["k"] (succ (Apply (name "half", name "k"))))))))

let size_ty =
  pi "A" (universe 0) (pi "h" (arrows [name "A"; name "A"] (name "A")) (pi "x" (name "A")
    (arrow (Fa.tr (name "A") (name "h") (name "x")) nat)))

let size_with branches = Fixpoint ("size", size_ty, 3,
  abs ["A"; "h"; "x"; "t"]
    (Match ("Tr", P.Univ 0, abs ["i"; "_"] nat, name "t", branches)))

let h2 a b = call (name "h") [a; b]
let size_at x t = call (name "size") [name "A"; name "h"; x; t]

let size =
  size_with [
    abs ["a"] (succ zero);
    abs ["a"; "f"] (size_at (h2 (name "a") (name "a")) (Apply (name "f", name "a")));
    abs ["a"; "f"] (size_at (h2 (h2 (name "a") (name "a")) (name "a")) (call (name "f") [name "a"; name "a"]));
    abs ["a"; "l"; "b"; "r"]
      (plus (size_at (h2 (name "a") (name "a")) (Apply (name "l", name "a")))
            (size_at (h2 (name "b") (name "b")) (Apply (name "r", name "b"))));
  ]

let half_position =
  size_with [
    abs ["a"] zero; abs ["a"; "f"] zero;
    abs ["a"; "f"] (size_at (name "a") (Apply (name "f", name "a")));
    abs ["a"; "l"; "b"; "r"] zero;
  ]

let under_binders =
  Fixpoint ("f", arrows [nat; nat] nat, 0,
    abs ["n"; "m"]
      (nat_case (name "n") (name "m")
         (abs ["k"] (call (ann (abs ["y"; "z"]
                                  (nat_case (name "z") (call (name "f") [name "k"; name "y"])
                                     (abs ["w"] (call (name "f") [name "k"; name "w"]))))
                             (arrows [nat; nat] nat))
                       [name "m"; name "m"]))))

let pred_ann = ann (abs ["n"] (nat_case (name "n") zero (abs ["k"] (name "k")))) (arrow nat nat)
let apply_to = ann (abs ["h"; "y"] (Apply (name "h", name "y"))) (arrow (arrow nat nat) (arrow nat nat))

let g_pred =
  Fixpoint ("g", arrow nat nat, 0,
    abs ["n"] (nat_case (name "n") zero (abs ["k"] (Apply (name "g", Apply (pred_ann, name "k"))))))

let partial =
  Fixpoint ("f", arrows [nat; nat] nat, 1,
    abs ["m"; "n"] (nat_case (name "n") (name "m")
                      (abs ["k"] (call apply_to [Apply (name "f", name "m"); name "k"]))))

let bare =
  Fixpoint ("f", arrow nat nat, 0,
    abs ["n"] (nat_case (name "n") zero (abs ["k"] (call apply_to [name "f"; name "k"]))))

let nested =
  Fixpoint ("f", arrows [nat; nat] nat, 0,
    abs ["n"; "m"] (nat_case (name "n") (name "m")
                      (abs ["k"] (call (name "f") [name "k"; call (name "f") [name "n"; name "m"]]))))

let shadowed =
  Fixpoint ("f", arrow nat nat, 0,
    abs ["n"] (nat_case (name "n") zero
                 (abs ["k"] (Apply (ann (abs ["k"] (Apply (name "f", name "k"))) (arrow nat nat), zero)))))

let nonrec_field =
  Fixpoint ("f", pi "n" nat (arrow (Fa.vec nat (name "n")) nat), 1,
    abs ["n"; "v"]
      (Match ("Vec", P.Univ 0, abs ["i"; "_"] nat, name "v",
              [zero; abs ["k"; "x"; "xs"] (call (name "f") [name "k"; name "x"])])))
