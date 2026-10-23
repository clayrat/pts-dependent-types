(* Families with parameters, indices and functional recursive fields,
   assembled independently, as theories/MLTT/Families.v: Vec A n, W A B, and
   Tr A h x, whose recursive field f : Πy:A. Tr A h (h a y) has an index
   mentioning its position, an earlier field and a parameter, whose fork has
   two positions in an order its index tells apart, and whose twin has a
   field after a recursive one. *)

open Looping
module P = Pts_native
module Co = Constants

let universe i = Sort (P.Univ i)
let k g = Const (P.Const g)
let bool = Const P.Bool
let nat = Co.nat and zero = Co.zero and succ = Co.succ

(* Vectors. *)
let vec a n = call (k (P.Ind "Vec")) [a; n]
let vnil a = Apply (k (P.Ctor ("Vec", "nil")), a)
let vcons a n x xs = call (k (P.Ctor ("Vec", "cons"))) [a; n; x; xs]
let elim_vec = k (P.Elim ("Vec", 0))

let vec_desc = {
  P.ind_name = "Vec"; ind_params = [P.Srt (P.Univ 0)]; ind_indices = [build ["A"] nat]; ind_level = 0;
  ind_ctors = [
    { P.ctor_name = "nil"; ctor_fields = []; ctor_indices = [build ["A"] zero] };
    { P.ctor_name = "cons";
      ctor_fields = [P.FArg (build ["A"] nat); P.FArg (build ["n"; "A"] (name "A"));
                     P.FRec ([], [build ["x"; "n"; "A"] (name "n")])];
      ctor_indices = [build ["xs"; "x"; "n"; "A"] (succ (name "n"))] };
  ];
}

let vec_motive = pi "n" nat (arrow (vec (name "A") (name "n")) (universe 0))
let vec_cons_method =
  pi "n" nat (pi "x" (name "A") (pi "xs" (vec (name "A") (name "n"))
    (arrow (call (name "P") [name "n"; name "xs"])
       (call (name "P") [succ (name "n"); vcons (name "A") (name "n") (name "x") (name "xs")]))))
let elim_vec_ty =
  pi "A" (universe 0) (pi "P" vec_motive
    (arrows [call (name "P") [zero; vnil (name "A")]; vec_cons_method]
       (pi "n" nat (pi "v" (vec (name "A") (name "n")) (call (name "P") [name "n"; name "v"])))))

(* W-types. *)
let w a b = call (k (P.Ind "W")) [a; b]
let sup a b x f = call (k (P.Ctor ("W", "sup"))) [a; b; x; f]
let elim_w = k (P.Elim ("W", 0))

let w_desc = {
  P.ind_name = "W";
  ind_params = [P.Srt (P.Univ 0); build ["A"] (arrow (name "A") (universe 0))];
  ind_indices = []; ind_level = 0;
  ind_ctors = [
    { P.ctor_name = "sup";
      ctor_fields = [P.FArg (build ["B"; "A"] (name "A"));
                     P.FRec ([build ["a"; "B"; "A"] (Apply (name "B", name "a"))], [])];
      ctor_indices = [] };
  ];
}

let w_method =
  pi "a" (name "A") (pi "f" (arrow (Apply (name "B", name "a")) (w (name "A") (name "B")))
    (arrow (pi "b" (Apply (name "B", name "a")) (Apply (name "P", Apply (name "f", name "b"))))
       (Apply (name "P", sup (name "A") (name "B") (name "a") (name "f")))))
let elim_w_ty =
  pi "A" (universe 0) (pi "B" (arrow (name "A") (universe 0))
    (pi "P" (arrow (w (name "A") (name "B")) (universe 0))
       (arrow w_method (pi "w" (w (name "A") (name "B")) (Apply (name "P", name "w"))))))

(* Trees indexed through the parameter h. *)
let tr a h x = call (k (P.Ind "Tr")) [a; h; x]
let leaf a h x = call (k (P.Ctor ("Tr", "leaf"))) [a; h; x]
let node a h x f = call (k (P.Ctor ("Tr", "node"))) [a; h; x; f]
let fork a h x f = call (k (P.Ctor ("Tr", "fork"))) [a; h; x; f]
let twin a h x l y r = call (k (P.Ctor ("Tr", "twin"))) [a; h; x; l; y; r]
let elim_tr = k (P.Elim ("Tr", 0))
let binary a = arrows [a; a] a

let tr_desc = {
  P.ind_name = "Tr";
  ind_params = [P.Srt (P.Univ 0); build ["A"] (binary (name "A"))];
  ind_indices = [build ["h"; "A"] (name "A")]; ind_level = 0;
  ind_ctors = [
    { P.ctor_name = "leaf"; ctor_fields = [P.FArg (build ["h"; "A"] (name "A"))];
      ctor_indices = [build ["a"; "h"; "A"] (name "a")] };
    { P.ctor_name = "node";
      ctor_fields = [P.FArg (build ["h"; "A"] (name "A"));
                     P.FRec ([build ["a"; "h"; "A"] (name "A")],
                             [build ["y"; "a"; "h"; "A"] (call (name "h") [name "a"; name "y"])])];
      ctor_indices = [build ["f"; "a"; "h"; "A"] (name "a")] };
    { P.ctor_name = "fork";
      ctor_fields = [P.FArg (build ["h"; "A"] (name "A"));
                     P.FRec ([build ["a"; "h"; "A"] (name "A"); build ["y"; "a"; "h"; "A"] (name "A")],
                             [build ["z"; "y"; "a"; "h"; "A"]
                                (call (name "h") [call (name "h") [name "a"; name "y"]; name "z"])])];
      ctor_indices = [build ["f"; "a"; "h"; "A"] (name "a")] };
    { P.ctor_name = "twin";
      ctor_fields = [P.FArg (build ["h"; "A"] (name "A"));
                     P.FRec ([build ["a"; "h"; "A"] (name "A")],
                             [build ["y"; "a"; "h"; "A"] (call (name "h") [name "a"; name "y"])]);
                     P.FArg (build ["l"; "a"; "h"; "A"] (name "A"));
                     P.FRec ([build ["b"; "l"; "a"; "h"; "A"] (name "A")],
                             [build ["y"; "b"; "l"; "a"; "h"; "A"] (call (name "h") [name "b"; name "y"])])];
      ctor_indices = [build ["r"; "b"; "l"; "a"; "h"; "A"] (call (name "h") [name "a"; name "b"])] };
  ];
}

let h_a_y = call (name "h") [name "a"; name "y"]
let h_a_y_z = call (name "h") [h_a_y; name "z"]
let tr_motive = pi "x" (name "A") (arrow (tr (name "A") (name "h") (name "x")) (universe 0))
let tr_leaf_method = pi "a" (name "A") (call (name "P") [name "a"; leaf (name "A") (name "h") (name "a")])
let tr_node_method =
  pi "a" (name "A") (pi "f" (pi "y" (name "A") (tr (name "A") (name "h") h_a_y))
    (arrow (pi "y" (name "A") (call (name "P") [h_a_y; Apply (name "f", name "y")]))
       (call (name "P") [name "a"; node (name "A") (name "h") (name "a") (name "f")])))
let tr_fork_method =
  pi "a" (name "A") (pi "f" (pi "y" (name "A") (pi "z" (name "A") (tr (name "A") (name "h") h_a_y_z)))
    (arrow (pi "y" (name "A") (pi "z" (name "A")
              (call (name "P") [h_a_y_z; call (name "f") [name "y"; name "z"]])))
       (call (name "P") [name "a"; fork (name "A") (name "h") (name "a") (name "f")])))
let h_b_y = call (name "h") [name "b"; name "y"]
let h_a_b = call (name "h") [name "a"; name "b"]
let tr_twin_method =
  pi "a" (name "A") (pi "l" (pi "y" (name "A") (tr (name "A") (name "h") h_a_y))
    (arrow (pi "y" (name "A") (call (name "P") [h_a_y; Apply (name "l", name "y")]))
       (pi "b" (name "A") (pi "r" (pi "y" (name "A") (tr (name "A") (name "h") h_b_y))
          (arrow (pi "y" (name "A") (call (name "P") [h_b_y; Apply (name "r", name "y")]))
             (call (name "P") [h_a_b; twin (name "A") (name "h") (name "a") (name "l") (name "b") (name "r")]))))))
let elim_tr_ty =
  pi "A" (universe 0) (pi "h" (binary (name "A")) (pi "P" tr_motive
    (arrows [tr_leaf_method; tr_node_method; tr_fork_method; tr_twin_method]
       (pi "x" (name "A") (pi "t" (tr (name "A") (name "h") (name "x"))
          (call (name "P") [name "x"; name "t"]))))))

(* Over ℕ and its eliminator, entry by entry. *)
let signature =
  List.fold_left Co.add (Co.base_signature true) [
    P.EInd vec_desc; P.EElim ("Vec", 0, build [] elim_vec_ty, true);
    P.EInd w_desc; P.EElim ("W", 0, build [] elim_w_ty, true);
    P.EInd tr_desc; P.EElim ("Tr", 0, build [] elim_tr_ty, true);
  ]

(* Open terms for the ι-rules: each rule is (context, lhs, rhs, type). *)
let vec_rule_ctx =
  ["xs", vec (name "A") (name "n"); "x", name "A"; "n", nat;
   "mc", vec_cons_method; "mn", call (name "P") [zero; vnil (name "A")]; "P", vec_motive;
   "A", universe 0]
let w_rule_ctx =
  ["f", arrow (Apply (name "B", name "a")) (w (name "A") (name "B")); "a", name "A"; "m", w_method;
   "P", arrow (w (name "A") (name "B")) (universe 0); "B", arrow (name "A") (universe 0);
   "A", universe 0]
let tr_methods_ctx =
  ["mt", tr_twin_method; "mf", tr_fork_method; "mn", tr_node_method; "ml", tr_leaf_method; "P", tr_motive;
   "h", binary (name "A"); "A", universe 0]
let tr_rule_ctx = ("f", pi "y" (name "A") (tr (name "A") (name "h") h_a_y)) :: ("a", name "A") :: tr_methods_ctx
let tr_fork_ctx =
  ("f", pi "y" (name "A") (pi "z" (name "A") (tr (name "A") (name "h") h_a_y_z)))
  :: ("a", name "A") :: tr_methods_ctx
let tr_twin_ctx =
  ["r", pi "y" (name "A") (tr (name "A") (name "h") h_b_y); "b", name "A";
   "l", pi "y" (name "A") (tr (name "A") (name "h") h_a_y); "a", name "A"] @ tr_methods_ctx

let elim_vec_at n v = call elim_vec [name "A"; name "P"; name "mn"; name "mc"; n; v]
let elim_w_at x = call elim_w [name "A"; name "B"; name "P"; name "m"; x]
let elim_tr_at x t =
  call elim_tr [name "A"; name "h"; name "P"; name "ml"; name "mn"; name "mf"; name "mt"; x; t]

let iota_rules = [
  "vec nil", vec_rule_ctx, elim_vec_at zero (vnil (name "A")), name "mn",
    call (name "P") [zero; vnil (name "A")];
  "vec cons", vec_rule_ctx,
    elim_vec_at (succ (name "n")) (vcons (name "A") (name "n") (name "x") (name "xs")),
    call (name "mc") [name "n"; name "x"; name "xs"; elim_vec_at (name "n") (name "xs")],
    call (name "P") [succ (name "n"); vcons (name "A") (name "n") (name "x") (name "xs")];
  "w sup", w_rule_ctx, elim_w_at (sup (name "A") (name "B") (name "a") (name "f")),
    call (name "m") [name "a"; name "f"; abs ["b"] (elim_w_at (Apply (name "f", name "b")))],
    Apply (name "P", sup (name "A") (name "B") (name "a") (name "f"));
  "tr leaf", tr_rule_ctx, elim_tr_at (name "a") (leaf (name "A") (name "h") (name "a")),
    Apply (name "ml", name "a"),
    call (name "P") [name "a"; leaf (name "A") (name "h") (name "a")];
  "tr node", tr_rule_ctx, elim_tr_at (name "a") (node (name "A") (name "h") (name "a") (name "f")),
    call (name "mn") [name "a"; name "f"; abs ["y"] (elim_tr_at h_a_y (Apply (name "f", name "y")))],
    call (name "P") [name "a"; node (name "A") (name "h") (name "a") (name "f")];
  "tr fork", tr_fork_ctx, elim_tr_at (name "a") (fork (name "A") (name "h") (name "a") (name "f")),
    call (name "mf") [name "a"; name "f";
      abs ["y"; "z"] (elim_tr_at h_a_y_z (call (name "f") [name "y"; name "z"]))],
    call (name "P") [name "a"; fork (name "A") (name "h") (name "a") (name "f")];
  "tr twin", tr_twin_ctx,
    elim_tr_at h_a_b (twin (name "A") (name "h") (name "a") (name "l") (name "b") (name "r")),
    call (name "mt") [name "a"; name "l"; abs ["y"] (elim_tr_at h_a_y (Apply (name "l", name "y")));
                      name "b"; name "r"; abs ["y"] (elim_tr_at h_b_y (Apply (name "r", name "y")))],
    call (name "P") [h_a_b; twin (name "A") (name "h") (name "a") (name "l") (name "b") (name "r")];
]

(* Ill-typed right sides: the node rule with the index swapped, the fork
   rule with the positions swapped. *)
let swapped_node =
  call (name "mn") [name "a"; name "f";
    abs ["y"] (elim_tr_at (call (name "h") [name "y"; name "a"]) (Apply (name "f", name "y")))]
let swapped_fork =
  call (name "mf") [name "a"; name "f";
    abs ["y"; "z"] (elim_tr_at h_a_y_z (call (name "f") [name "z"; name "y"]))]

(* Closed computations. *)
let bnot x = ElimBool (ann (abs ["_"] bool) (arrow bool (universe 0)), Const P.BFalse, Const P.BTrue, x)
let two_bools = vcons bool (succ zero) (Const P.BTrue) (vcons bool zero (Const P.BFalse) (vnil bool))
let vnot =
  call elim_vec [bool; ann (abs ["n"; "v"] (vec bool (name "n"))) (pi "n" nat (arrow (vec bool (name "n")) (universe 0)));
                 vnil bool; abs ["n"; "x"; "xs"; "r"] (vcons bool (name "n") (bnot (name "x")) (name "r"))]

let positions =
  ann (abs ["b"] (ElimBool (ann (abs ["z"] (universe 0)) (arrow bool (universe 1)),
                            Const P.Unit, Const P.Void, name "b")))
    (arrow bool (universe 0))
let nat_w = w bool positions
let zero_w =
  sup bool positions (Const P.BFalse)
    (abs ["v"] (ElimVoid (ann (abs ["_"] nat_w) (arrow (Const P.Void) (universe 0)), name "v")))
let succ_w n = sup bool positions (Const P.BTrue) (abs ["_"] n)
let to_nat =
  call elim_w [bool; positions; ann (abs ["_"] nat) (arrow nat_w (universe 0));
    abs ["a"; "f"; "r"]
      (call (ElimBool (ann (abs ["c"] (arrow (arrow (Apply (positions, name "c")) nat) nat))
                         (arrow bool (universe 0)),
                       abs ["r'"] (succ (Apply (name "r'", Const P.Tt))), abs ["r'"] zero, name "a"))
         [name "r"])]

let second = ann (abs ["x"; "y"] (name "y")) (binary bool)
let tree = node bool second (Const P.BTrue) (abs ["y"] (leaf bool second (name "y")))
let fork_tree = fork bool second (Const P.BFalse) (abs ["y"; "z"] (leaf bool second (name "z")))
let twin_tree =
  twin bool second (Const P.BFalse) (abs ["y"] (leaf bool second (name "y")))
    (Const P.BTrue) (abs ["y"] (leaf bool second (name "y")))
let label =
  call elim_tr [bool; second;
    ann (abs ["x"; "t"] bool) (pi "x" bool (arrow (tr bool second (name "x")) (universe 0)));
    abs ["a"] (name "a"); abs ["a"; "f"; "r"] (Apply (name "r", Const P.BFalse));
    abs ["a"; "f"; "r"] (call (name "r") [Const P.BFalse; Const P.BTrue]);
    abs ["a"; "l"; "il"; "b"; "r"; "ir"] (Apply (name "ir", Const P.BTrue))]
