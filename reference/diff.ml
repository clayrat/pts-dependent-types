(* Compare the independent OCaml reference with Rocq extraction.  Answers,
   intermediate evaluator results and complete checker traces must agree. *)

module X = Deptypes
module N = Pts_native
module L = Looping
module E = Encodings
module T = Translate
module C = Choose
module El = Eliminators
module Pa = Pairs
module Co = Constants
module Fa = Families

open Extracted

(* Extracted PCF syntax, as the native translator's. *)
let rec pty_of = function X.Tnat -> T.Nat | X.Tarr (a, b) -> T.Arrow (pty_of a, pty_of b)

let rec pterm_of = function
  | X.Tvar x -> T.Var x
  | X.Tlam (x, b) -> T.Lam (x, pterm_of b)
  | X.Tapp (f, a) -> T.App (pterm_of f, pterm_of a)
  | X.Tnum n -> T.Num n
  | X.Tsucc u -> T.Succ (pterm_of u)
  | X.Tpred u -> T.Pred (pterm_of u)
  | X.Tifz (c, a, b) -> T.Ifz (pterm_of c, pterm_of a, pterm_of b)
  | X.Tfix (a, u) -> T.Fix (pty_of a, pterm_of u)
  | X.Tann (u, a) -> T.Ann (pterm_of u, pty_of a)

let pcf_error_of = function
  | X.E_Unbound x -> T.Unbound x
  | X.E_NoSynth t -> T.NoSynth (pterm_of t)
  | X.E_NotFun (t, a) -> T.NotFun (pterm_of t, pty_of a)
  | X.E_LamNotFun (t, a) -> T.LamNotFun (pterm_of t, pty_of a)
  | X.E_Mismatch (t, e, i) -> T.Mismatch (pterm_of t, pty_of e, pty_of i)

let assertions = ref 0

let equal label native extracted =
  incr assertions;
  if native <> extracted then failwith ("reference differs from extraction: " ^ label)

(* A run compares the two kernels in the same signature: a pair of the
   native one and the extracted one, empty by default. *)
let empty = (N.empty_signature, X.sig_empty)

let check_infer ?(sg = empty) name xspec nspec fuel gamma term =
  let nsg, xsg = sg in
  let ngamma = List.map term_of_extracted gamma in
  let nterm = term_of_extracted term in
  let events, result = N.run_infer ~sg:nsg nspec fuel ngamma nterm in
  let native = List.map event_to_extracted events, answer_to_extracted term_to_extracted result in
  equal name native (X.run_infer xspec xsg fuel gamma term)

let check_check ?(sg = empty) name xspec nspec fuel gamma term expected =
  let nsg, xsg = sg in
  let ngamma = List.map term_of_extracted gamma in
  let nterm = term_of_extracted term in
  let nexp = term_of_extracted expected in
  let events, result = N.run_check ~sg:nsg nspec fuel ngamma nterm nexp in
  let native = List.map event_to_extracted events, answer_to_extracted Fun.id result in
  equal name native (X.run_check xspec xsg fuel gamma term expected)

let check_eval ?native ?(sg = empty) ?(fuels = [0; 1; 2; 5]) name term =
  let nsg, xsg = sg in
  let native = match native with Some t -> t | None -> term_of_extracted term in
  equal (name ^ "/classify") (shape_to_extracted (N.classify ~sg:nsg native)) (X.classify xsg term);
  List.iter (fun fuel ->
    let trace, result = N.normalize_trace ~sg:nsg fuel native in
    equal (Printf.sprintf "%s/trace/%d" name fuel)
      (List.map term_to_extracted trace, eval_to_extracted result)
      (X.normalize_trace xsg fuel term);
    equal (Printf.sprintf "%s/normalize/%d" name fuel)
      (eval_to_extracted (N.normalize ~sg:nsg fuel native)) (X.normalize xsg fuel term);
    equal (Printf.sprintf "%s/whnf/%d" name fuel)
      (head_to_extracted (N.whnf ~sg:nsg fuel native)) (X.whnf xsg fuel term)) fuels

let convert_case ?(sg = empty) name t u =
  let nsg, xsg = sg in
  let nt = term_of_extracted t and nu = term_of_extracted u in
  List.iter (fun fuel ->
    equal (Printf.sprintf "%s/conv/%d" name fuel)
      (conv_to_extracted (N.convert ~sg:nsg fuel nt nu)) (X.convert xsg fuel t u)) [0; 1; 2; 5]

let () =
  let open X in
  let identity = id_tm in
  let annotated_beta = App (Ann (Lam (Var 0), Pi (Bool, Bool)), BTrue) in
  let raw_stuck = App (Tt, Ann (Tt, Unit)) in
  let neutral_bool = ElimBool (type_family, Unit, Bool, Var 0) in
  let samples = [
    "sort", Srt Star; "var", Var 0; "pi", id_ty;
    "identity", identity; "applied", id_applied;
    "beta", annotated_beta; "stuck", raw_stuck;
    "omega", raw_omega; "unit elim", ElimUnit (Lam Unit, Tt, Tt);
    "bool elim", ElimBool (type_family, Unit, Bool, BTrue);
    "neutral bool", neutral_bool;
    "void elim", ElimVoid (Void, Ann (Var 0, Void));
    "open substitution", App (Lam (Lam (Var 2)), Var 5);
    "neutral app", App (Var 0, Ann (Tt, Unit));
    "pi step", Pi (Ann (Unit, Srt (Univ 0)), Ann (Bool, Srt (Univ 0)));
    "lambda step", Lam (Ann (Var 0, Unit));
    "unit neutral", ElimUnit (Ann (Lam Unit, Pi (Unit, Srt (Univ 0))),
                                    Ann (Tt, Unit), Var 0);
    "bool false", ElimBool (type_family, Unit, Bool, BFalse);
    "void neutral", ElimVoid (Ann (Void, Srt (Univ 0)), Var 0);
    "product", Sigma (Bool, Unit); "dependent sum", Sigma (Srt (Univ 0), Var 0);
    "pair", Pair (BTrue, Tt); "fst pair", Fst (Pair (BTrue, Tt));
    "snd pair", Snd (Pair (Ann (Tt, Unit), BTrue)); "fst neutral", Fst (Var 0);
    "snd stuck", Snd Tt; "pair step", Pair (Ann (Tt, Unit), Var 0);
    "sum step", Sigma (Ann (Bool, Srt (Univ 0)), Ann (Unit, Srt (Univ 0)));
    "constant", Const (Def "f");
  ] in
  List.iter (fun (name, term) -> check_eval name term) samples;
  List.iter (fun (name, term) ->
    convert_case (name ^ "/refl") term term;
    convert_case (name ^ "/unit") term Unit;
    convert_case (name ^ "/bool") term Bool) samples;
  convert_case "eta" (Var 0) (Lam (App (Var 1, Var 0)));
  convert_case "annotation" (Ann (Unit, Srt (Univ 0))) Unit;

  let specs = [
    "U-", system_u_minus, N.system_u_minus;
    "U", system_u, N.system_u;
    "lambda-star", lambda_star, N.lambda_star;
    "predicative", predicative, N.predicative;
    "pure-predicative", pure_predicative, N.pure_predicative;
  ] in
  let sorts = [Star; Box; Tri; Univ 0; Univ 1; Univ 2] in
  List.iter (fun (name, extracted, native) ->
    equal (name ^ "/primitives")
      (Option.map sort_to_extracted native.N.primitive_sort) extracted.spec_prim;
    equal (name ^ "/constants") native.N.constants extracted.spec_decls;
    List.iter (fun s ->
      let ns = sort_of_extracted s in
      equal (name ^ "/sort") (native.N.sort_allowed ns) (extracted.spec_sort s);
      equal (name ^ "/axiom")
        (Option.map sort_to_extracted (native.N.axiom ns)) (extracted.spec_axiom s);
      List.iter (fun t ->
        equal (name ^ "/product")
          (Option.map sort_to_extracted (native.N.product ns (sort_of_extracted t)))
          (extracted.spec_rule s t);
        equal (name ^ "/sigma")
          (Option.map sort_to_extracted (native.N.sigma ns (sort_of_extracted t)))
          (extracted.spec_sigma s t)) sorts) sorts) specs;
  List.iter (fun (system, extracted, native) ->
    List.iter (fun fuel ->
      List.iter (fun (name, term) ->
        check_infer (system ^ "/" ^ name ^ "/infer/" ^ string_of_int fuel)
          extracted native fuel [] term) samples;
      check_check (system ^ "/identity/check/" ^ string_of_int fuel)
        extracted native fuel [] identity id_ty;
      check_check (system ^ "/large-elim/check/" ^ string_of_int fuel)
        extracted native fuel [] Tt large_elim_ty;
      check_infer (system ^ "/open-context/" ^ string_of_int fuel)
        extracted native fuel id_applied_ctx id_applied;
      check_infer (system ^ "/bad-context/" ^ string_of_int fuel)
        extracted native fuel [BTrue] (Var 0)) [0; 1; 5; 100]) specs;
  check_check "wrong branch" predicative N.predicative 100 []
    (ElimBool (type_family, Unit, Tt, BTrue)) (Srt (Univ 0));
  check_check "unbound expected" predicative N.predicative 100 []
    BTrue (Ann (Bool, Var 0));
  check_check "top expected" system_u_minus N.system_u_minus 100 []
    (Srt Box) (Srt Tri);
  (* The native construction is independent of the extracted builder. *)
  equal "looping/type" (term_to_extracted L.looping_ty) looping_ty;
  List.iter (fun n ->
    equal (Printf.sprintf "looping/term/%d" n)
      (term_to_extracted (L.looping n)) (looping n)) [0; 1; 2; 3];
  List.iter (fun n ->
    equal (Printf.sprintf "looping/applied/%d" n)
      (term_to_extracted (L.looping_applied n)) (looping_applied n)) [0; 1; 2];
  (* Complete native checker traces in U⁻ and up to the predicative
     failure, then the normal-order unfolding. *)
  List.iter (fun n ->
    let events, answer = N.run_infer N.system_u_minus looping_fuel [] (L.looping n) in
    equal (Printf.sprintf "looping %d/U-" n)
      (List.map event_to_extracted events, answer_to_extracted term_to_extracted answer)
      (X.run_infer system_u_minus X.sig_empty looping_fuel [] (looping n))) [0; 1];
  check_infer "looping/predicative" pure_predicative N.pure_predicative looping_fuel []
    (map_sorts u_to_univ (looping 0));
  check_eval ~native:(L.looping_applied 0) "looping applied" (looping_applied 0);
  List.iter (fun fuel ->
    equal (Printf.sprintf "looping unfolding/%d" fuel)
      (List.map term_to_extracted (fst (N.normalize_trace fuel (L.looping_applied 0))))
      (fst (X.normalize_trace X.sig_empty fuel (looping_applied 0)))) [11; 30];
  (* Church numerals: the same terms, the same typing traces in U⁻, and the
     same bounded normal-order results on the strictness programs. *)
  List.iter2 (fun ((name, t), ty) (_, nt, nty) ->
    let t = church t and ty = church ty in
    equal ("encoding/term/" ^ name) (term_to_extracted (E.church nt)) t;
    equal ("encoding/type/" ^ name) (term_to_extracted (E.church nty)) ty;
    let events, answer = N.run_infer N.system_u_minus looping_fuel [] (E.church nt) in
    equal ("encoding/infer/" ^ name)
      (List.map event_to_extracted events, answer_to_extracted term_to_extracted answer)
      (X.run_infer system_u_minus X.sig_empty looping_fuel [] t)) encodings_typed E.encodings_typed;
  List.iter2 (fun ((name, t), expected) (_, nt, nexpected) ->
    let t = church t and nt = E.church nt in
    equal ("strictness/term/" ^ name) (term_to_extracted nt) t;
    equal ("strictness/expected/" ^ name) nexpected expected;
    let events, answer = N.run_check N.system_u_minus looping_fuel [] nt (E.church E.c_nat) in
    equal ("strictness/check/" ^ name)
      (List.map event_to_extracted events, answer_to_extracted Fun.id answer)
      (X.run_check system_u_minus X.sig_empty looping_fuel [] t (church cNat));
    let native = N.normalize observe_fuel nt in
    equal ("strictness/normalize/" ^ name) (eval_to_extracted native) (X.normalize X.sig_empty observe_fuel t);
    equal ("strictness/decode/" ^ name)
      (match native with N.NormalForm v -> E.decode_nat v | _ -> None)
      (match X.normalize X.sig_empty observe_fuel t with X.NormalForm v -> decode_nat v | _ -> None))
    strictness_cases E.strictness_cases;
  (* The translator: the same translations and the same first errors. *)
  let translation_of_extracted = function
    | X.Ok (g, u) -> Stdlib.Ok (List.map term_of_extracted g, term_of_extracted u)
    | X.Err (X.TrIllTyped e) -> Stdlib.Error (T.IllTyped (pcf_error_of e))
    | X.Err (X.TrName x) -> Stdlib.Error (T.Name x)
    | X.Err (X.TrTargetRejected _) | X.Err (X.TrTargetUndecided _) ->
        failwith "the unchecked translation does not run the target checker"
  in
  let check_translate name g t a =
    equal ("translate/" ^ name)
      (T.translate (List.map (fun (x, a) -> (x, pty_of a)) g) (pterm_of t) (pty_of a))
      (translation_of_extracted (X.translate g t a))
  in
  List.iter (fun ((name, t), _) -> check_translate name [] t Tnat) pcf_cases;
  let nat_to_nat = Tarr (Tnat, Tnat) in
  List.iter (fun (name, g, t, a) -> check_translate name g t a) [
    "not a function", [], Tapp (Tnum 0, Tnum 1), Tnat;
    "lambda at ℕ", [], Tlam ("x", Tvar "x"), Tnat;
    "unbound", [], Tvar "y", Tnat;
    "ifz synthesized", [], Tapp (Tifz (Tnum 0, Tnum 1, Tnum 2), Tnum 0), Tnat;
    "mismatch", [], Tann (Tnum 0, nat_to_nat), Tnat;
    "anonymous name", [], Tapp (Tann (Tlam ("_", Tvar "_"), nat_to_nat), Tnum 0), Tnat;
    "open context", [("x", Tnat); ("f", nat_to_nat)], Tapp (Tvar "f", Tvar "x"), Tnat;
    "shadowing", [("x", Tnat); ("x", nat_to_nat)], Tsucc (Tvar "x"), Tnat;
    "fix at ℕ → ℕ", [], Tfix (nat_to_nat, Tlam ("g", Tvar "g")), nat_to_nat;
  ];
  (* Checked translations: both accept every program, with the same term. *)
  List.iter (fun ((name, t), _) ->
    let tag_x = function
      | X.Ok u -> `Accepted (term_of_extracted u)
      | X.Err (X.TrTargetRejected _) -> `Rejected
      | X.Err (X.TrTargetUndecided _) -> `Undecided
      | X.Err _ -> `Other in
    let tag_n = function
      | Stdlib.Ok u -> `Accepted u
      | Stdlib.Error (T.TargetRejected _) -> `Rejected
      | Stdlib.Error (T.TargetUndecided _) -> `Undecided
      | Stdlib.Error _ -> `Other in
    equal ("translate checked/" ^ name)
      (tag_n (T.translate_program_checked looping_fuel (pterm_of t)))
      (tag_x (X.translate_program_checked looping_fuel t))) pcf_cases;
  (* Normal-order results of short translated programs. *)
  List.iter (fun ((name, t), expected) ->
    match expected, X.translate_program t, T.translate_program (pterm_of t) with
    | Some k, X.Ok u, Stdlib.Ok nu when k <= 5 ->
        equal ("translated/normalize/" ^ name)
          (eval_to_extracted (N.normalize translation_fuel nu)) (X.normalize X.sig_empty translation_fuel u)
    | _ -> ()) pcf_cases;
  (* choose: the same terms and contexts, the same checker traces, and the
     same normal forms. *)
  let in_x g = X.in_ctx g and term_x g t = X.term_in g t in
  equal "choose/types ctx" (List.map term_to_extracted (C.in_ctx C.types_ctx)) (in_x types_ctx);
  equal "choose/open ctx" (List.map term_to_extracted (C.in_ctx C.open_ctx)) (in_x open_ctx);
  let runs = [
    "choose", C.types_ctx, C.choose, C.choose_ty, types_ctx, choose, choose_ty;
    "choose true", C.args_ctx, C.choose_at (Looping.Const N.BTrue), Looping.name "A",
      args_ctx, choose_at NTrue, NVar "A";
    "choose false", C.args_ctx, C.choose_at (Looping.Const N.BFalse), Looping.name "B",
      args_ctx, choose_at NFalse, NVar "B";
    "choose open", C.open_ctx, C.choose_at (Looping.name "b"), Looping.name "A",
      open_ctx, choose_at (NVar "b"), NVar "A";
    "choose swapped", C.types_ctx, C.choose_swapped, C.choose_ty, types_ctx, choose_swapped, choose_ty;
  ] in
  List.iter (fun (name, ng, nt, na, g, t, a) ->
    equal ("choose/term/" ^ name) (term_to_extracted (C.term_in ng nt)) (term_x g t);
    let events, answer =
      N.run_check N.predicative choose_fuel (C.in_ctx ng) (C.term_in ng nt) (C.term_in ng na) in
    equal ("choose/check/" ^ name)
      (List.map event_to_extracted events, answer_to_extracted Fun.id answer)
      (X.run_check predicative X.sig_empty choose_fuel (in_x g) (term_x g t) (term_x g a));
    equal ("choose/normalize/" ^ name)
      (eval_to_extracted (N.normalize choose_fuel (C.term_in ng nt)))
      (X.normalize X.sig_empty choose_fuel (term_x g t))) runs;
  check_infer "choose/low family" predicative N.predicative choose_fuel [] (X.build [] low_family);
  (* Void and Unit: the same terms, checker traces and normal forms. *)
  let elim_runs = [
    "void", El.void_ctx, El.void_elim, Looping.name "A", void_ctx, void_elim, NVar "A";
    "void wrong scrutinee", El.void_ctx, Looping.ElimVoid (El.void_family, Looping.Const N.Tt),
      Looping.name "A", void_ctx, NElimVoid (void_family, NTt), NVar "A";
    "unit tt", [], El.unit_elim (Looping.Const N.Tt), Looping.Const N.Bool, [], unit_elim NTt, NBool;
    "unit open", El.unit_ctx, El.unit_elim (Looping.name "u"), Looping.Const N.Bool,
      unit_ctx, unit_elim (NVar "u"), NBool;
  ] in
  List.iter (fun (name, ng, nt, na, g, t, a) ->
    equal ("elim/term/" ^ name) (term_to_extracted (C.term_in ng nt)) (term_x g t);
    let events, answer =
      N.run_check N.predicative elim_fuel (C.in_ctx ng) (C.term_in ng nt) (C.term_in ng na) in
    equal ("elim/check/" ^ name)
      (List.map event_to_extracted events, answer_to_extracted Fun.id answer)
      (X.run_check predicative X.sig_empty elim_fuel (in_x g) (term_x g t) (term_x g a));
    equal ("elim/normalize/" ^ name)
      (eval_to_extracted (N.normalize elim_fuel (C.term_in ng nt)))
      (X.normalize X.sig_empty elim_fuel (term_x g t))) elim_runs;
  (* Dependent pairs: the same terms, checker traces and normal forms. *)
  let build = Looping.build [] in
  equal "pairs/is true" (term_to_extracted (build Pa.is_true)) (X.build [] is_true);
  equal "pairs/sigma ctx" (List.map term_to_extracted Pa.sigma_ctx) sigma_ctx;
  List.iter (fun (name, nt, na, t, a) ->
    let t = X.build [] t and a = X.build [] a in
    equal ("pairs/term/" ^ name) (term_to_extracted (build nt)) t;
    equal ("pairs/type/" ^ name) (term_to_extracted (build na)) a;
    check_check ("pairs/check/" ^ name) predicative N.predicative pair_fuel [] t a;
    check_check ("pairs/u-minus/" ^ name) system_u_minus N.system_u_minus pair_fuel [] t a;
    check_eval ("pairs/eval/" ^ name) t) [
    "true", Pa.true_pair, Pa.true_sigma, NPair (NTrue, NTt), true_sigma;
    "false", Pa.false_pair, Pa.true_sigma, NPair (NFalse, NTt), true_sigma;
    "product", Pa.bool_pair, Pa.bools, NPair (NTrue, NFalse), NTimes (NBool, NBool);
  ];
  check_infer "pairs/snd" predicative N.predicative pair_fuel sigma_ctx (Snd (Var 0));
  check_infer "pairs/fst" predicative N.predicative pair_fuel sigma_ctx (Fst (Var 0));
  check_eval "pairs/snd type" (App (X.build [] is_true, Fst (Var 0)));
  equal "pairs/projection" (term_to_extracted (build Pa.first_of_pair))
    (X.build [] (NFst (NAnn (NPair (NTrue, NFalse), NTimes (NBool, NBool)))));
  check_eval "pairs/projection" (term_to_extracted (build Pa.first_of_pair));
  convert_case "pairs/no eta" (Var 0) (Pair (Fst (Var 0), Snd (Var 0)));
  equal "pairs/universe" (term_to_extracted (build Pa.sigma_of_universe))
    (X.build [] (NSigma ("b", NBool, NSrt (Univ 0))));
  check_infer "pairs/universe" predicative N.predicative pair_fuel []
    (term_to_extracted (build Pa.sigma_of_universe));
  (* Constants: the same signature, types, checker traces, δ- and ι-steps. *)
  let nsg = Co.signature true and nsg_off = Co.signature false in
  let nsg_base = Co.base_signature true in
  equal "constants/base" (List.map entry_to_extracted nsg_base) sg_nat_base;
  List.iter (fun (name, entry) ->
    equal ("constants/sig add/" ^ name)
      (Option.map (List.map entry_to_extracted) (N.sig_add nsg_base entry))
      (X.sig_add sg_nat_base (entry_to_extracted entry))) [
    "double", N.EDef ("double", build (Looping.arrow Co.nat Co.nat), build Co.double_body);
    "open", N.EDef ("bad", N.Var 0, N.Tt);
    "open elim", N.EElim ("Nat", 1, N.Pi (N.Var 0, N.Var 1), true);
  ];
  equal "constants/signature" (List.map entry_to_extracted nsg) sg_nat;
  equal "constants/inactive" (List.map entry_to_extracted nsg_off) sg_nat_inactive;
  equal "constants/elim type" (term_to_extracted (build Co.elim_nat_ty)) (X.build [] elim_nat_ty);
  equal "constants/double" (term_to_extracted (build Co.double_body)) (X.build [] double_body);
  equal "constants/iota ctx" (List.map term_to_extracted (C.in_ctx Co.iota_ctx)) (in_x iota_ctx);
  let active = (nsg, sg_nat) and inactive = (nsg_off, sg_nat_inactive) in
  List.iter (fun g ->
    equal "constants/sig type"
      (Option.map term_to_extracted (N.sig_type nsg (gref_of_extracted g))) (X.sig_type sg_nat g))
    [Ind "Nat"; Ctor ("Nat", "zero"); Ctor ("Nat", "succ"); Ctor ("Nat", "pred");
     Elim ("Nat", 0); Elim ("Nat", 1); Def "double"; Ind "Bool2"];
  let nat = build Co.nat in
  let step_r = Looping.abs ["m"; "r"] (Looping.name "r") in
  List.iter (fun (name, t, a) ->
    let t = term_to_extracted (build t) and a = term_to_extracted (build a) in
    List.iter (fun (which, sg) ->
      check_check ~sg ("constants/check/" ^ which ^ "/" ^ name) predicative N.predicative
        const_fuel [] t a;
      check_eval ~sg ~fuels:[0; 1; 2; 5; const_fuel] ("constants/eval/" ^ which ^ "/" ^ name) t)
      ["active", active; "inactive", inactive];
    check_check ~sg:active ("constants/u-minus/" ^ name) system_u_minus N.system_u_minus
      const_fuel [] t a;
    check_check ("constants/empty/" ^ name) predicative N.predicative const_fuel [] t a) [
    "two", Co.succ (Co.succ Co.zero), Co.nat;
    "elimNat", Co.elim_nat, Co.elim_nat_ty;
    "double body", Co.double_body, Looping.arrow Co.nat Co.nat;
    "double one", Co.double (Co.succ Co.zero), Co.nat;
    "object first", Co.elim_with step_r (Co.double Co.zero), Co.nat;
    "unit at Nat", Looping.Const N.Tt, Co.nat;
  ];
  (* The body of [double] in the signature without [double], and a body
     mentioning [double] there. *)
  let base = (nsg_base, sg_nat_base) and nat_to_nat = term_to_extracted (build (Looping.arrow Co.nat Co.nat)) in
  check_check ~sg:base "constants/base/double body" predicative N.predicative const_fuel []
    (term_to_extracted (build Co.double_body)) nat_to_nat;
  check_check ~sg:base "constants/base/self reference" predicative N.predicative const_fuel []
    (term_to_extracted (build (Looping.abs ["n"] (Co.double (Looping.name "n"))))) nat_to_nat;
  let open_spine = App (term_to_extracted (build (Looping.call Co.elim_nat
                                                [Co.const_nat; Co.zero; step_r])), Var 0) in
  check_infer ~sg:active "constants/open spine" predicative N.predicative const_fuel
    [term_to_extracted nat] open_spine;
  check_eval ~sg:active ~fuels:[0; 1; 5; const_fuel] "constants/open spine" open_spine;
  let in_iota t = term_to_extracted (C.term_in Co.iota_ctx t) in
  let n = Looping.name in
  let iota_lhs = in_iota (Looping.call Co.elim_nat [n "P"; n "z"; n "s"; Co.succ (n "n")]) in
  let iota_rhs =
    in_iota (Looping.call (n "s") [n "n"; Looping.call Co.elim_nat [n "P"; n "z"; n "s"; n "n"]]) in
  equal "constants/iota" (Option.map term_to_extracted (N.iota nsg (term_of_extracted iota_lhs)))
    (X.iota sg_nat iota_lhs);
  List.iter (fun (which, sg) ->
    convert_case ~sg ("constants/iota open/" ^ which) iota_lhs iota_rhs;
    check_infer ~sg ("constants/iota open/" ^ which) predicative N.predicative const_fuel
      (in_x iota_ctx) iota_lhs) ["active", active; "inactive", inactive];
  check_infer ~sg:active "constants/unknown" predicative N.predicative const_fuel [] (Const (Ind "Bool2"));
  (* Families: the same declarations, types of constants and contexts;
     the native ι is the right side written by hand and agrees with the
     extracted one; both sides check against the same type with the same
     traces, convert, and evaluate alike. *)
  let nfam = Fa.signature in
  let fam = (nfam, sg_families) in
  equal "families/signature" (List.map entry_to_extracted nfam) sg_families;
  equal "families/elim types"
    (List.map (fun t -> term_to_extracted (build t)) [Fa.elim_vec_ty; Fa.elim_w_ty; Fa.elim_tr_ty])
    (List.map (X.build []) [elim_vec_ty; elim_w_ty; elim_tr_ty]);
  List.iter (fun (name, nctx, xctx) ->
    equal ("families/ctx/" ^ name) (List.map term_to_extracted (C.in_ctx nctx)) (in_x xctx))
    ["vec", Fa.vec_rule_ctx, vec_rule_ctx; "w", Fa.w_rule_ctx, w_rule_ctx; "tr", Fa.tr_rule_ctx, tr_rule_ctx;
     "tr fork", Fa.tr_fork_ctx, tr_fork_ctx; "tr twin", Fa.tr_twin_ctx, tr_twin_ctx];
  List.iter (fun g ->
    equal "families/sig type"
      (Option.map term_to_extracted (N.sig_type nfam (gref_of_extracted g))) (X.sig_type sg_families g))
    [Ind "Vec"; Ctor ("Vec", "nil"); Ctor ("Vec", "cons"); Elim ("Vec", 0);
     Ind "W"; Ctor ("W", "sup"); Elim ("W", 0);
     Ind "Tr"; Ctor ("Tr", "leaf"); Ctor ("Tr", "node"); Ctor ("Tr", "fork"); Ctor ("Tr", "twin"); Elim ("Tr", 0)];
  List.iter (fun (name, ng, lhs, rhs, ty) ->
    let lhs = C.term_in ng lhs and rhs = C.term_in ng rhs and ty = C.term_in ng ty in
    equal ("families/iota is rhs/" ^ name) (N.iota nfam lhs) (Some rhs);
    let xl = term_to_extracted lhs and xr = term_to_extracted rhs and xt = term_to_extracted ty in
    let g = List.map term_to_extracted (C.in_ctx ng) in
    equal ("families/iota/" ^ name) (Option.map term_to_extracted (N.iota nfam lhs)) (X.iota sg_families xl);
    convert_case ~sg:fam ("families/conv/" ^ name) xl xr;
    check_check ~sg:fam ("families/check lhs/" ^ name) predicative N.predicative family_fuel g xl xt;
    check_check ~sg:fam ("families/check rhs/" ^ name) predicative N.predicative family_fuel g xr xt;
    check_eval ~sg:fam ~fuels:[0; 1; 5; family_fuel] ("families/eval/" ^ name) xl) Fa.iota_rules;
  List.iter (fun (name, ng, rhs, ctor) ->
    check_check ~sg:fam ("families/wrong side/" ^ name) predicative N.predicative family_fuel
      (List.map term_to_extracted (C.in_ctx ng)) (term_to_extracted (C.term_in ng rhs))
      (term_to_extracted (C.term_in ng
         (Looping.call (Looping.name "P") [Looping.name "a";
            ctor (Looping.name "A") (Looping.name "h") (Looping.name "a") (Looping.name "f")]))))
    ["swapped index", Fa.tr_rule_ctx, Fa.swapped_node, Fa.node;
     "swapped positions", Fa.tr_fork_ctx, Fa.swapped_fork, Fa.fork];
  List.iter (fun (name, nt, xt) ->
    equal ("families/term/" ^ name) (term_to_extracted (build nt)) (X.build [] xt)) [
    "two bools", Fa.two_bools, two_bools; "vnot", Fa.vnot, vnot;
    "positions", Fa.positions, positions; "nat_w", Fa.nat_w, nat_w;
    "succ_w zero_w", Fa.succ_w Fa.zero_w, succ_w zero_w; "to_nat", Fa.to_nat, to_nat;
    "second", Fa.second, second; "tree", Fa.tree, tree; "fork tree", Fa.fork_tree, fork_tree;
    "twin tree", Fa.twin_tree, twin_tree;
    "label", Fa.label, label;
  ];
  List.iter (fun (name, t, a) ->
    let t = term_to_extracted (build t) and a = term_to_extracted (build a) in
    check_check ~sg:fam ("families/closed check/" ^ name) predicative N.predicative family_fuel [] t a;
    check_eval ~sg:fam ~fuels:[0; 1; 5; family_fuel] ("families/closed eval/" ^ name) t) [
    "vnot", Looping.call Fa.vnot [Co.succ (Co.succ Co.zero); Fa.two_bools],
      Fa.vec Fa.bool (Co.succ (Co.succ Co.zero));
    "to_nat", Looping.Apply (Fa.to_nat, Fa.succ_w (Fa.succ_w Fa.zero_w)), Co.nat;
    "label", Looping.call Fa.label [Looping.Const N.BTrue; Fa.tree], Fa.bool;
    "fork label", Looping.call Fa.label [Looping.Const N.BFalse; Fa.fork_tree], Fa.bool;
    "twin label", Looping.call Fa.label [Looping.Const N.BTrue; Fa.twin_tree], Fa.bool;
  ];
  Printf.printf "reference: %d comparisons with extraction passed\n" !assertions
