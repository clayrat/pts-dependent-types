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
module Ma = Matches

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

(* [infer] alone, in a context taken as checked: [run_infer_open] of the
   reference, which erasure-cic uses, against [run_answer (infer …)]. *)
let check_infer_open ?(sg = empty) name xspec nspec fuel gamma term =
  let nsg, xsg = sg in
  let ngamma = List.map term_of_extracted gamma in
  let nterm = term_of_extracted term in
  let events, result = N.run_infer_open ~sg:nsg nspec fuel ngamma nterm in
  let native = List.map event_to_extracted events, answer_to_extracted term_to_extracted result in
  equal name native (X.run_answer (X.infer xspec xsg fuel gamma term))

(* eval_src of the reference against the extract, on a native term and the
   extracted one, at several budgets. *)
let check_eval_src ?(sg = empty) ~fuels name native term =
  let nsg, xsg = sg in
  List.iter (fun fuel ->
    equal (Printf.sprintf "%s/%d" name fuel)
      (cbv_to_extracted (N.eval_src ~sg:nsg fuel native)) (X.eval_src xsg fuel term))
    fuels

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

let convert_case ?(sg = empty) ?(fuels = [0; 1; 2; 5]) name t u =
  let nsg, xsg = sg in
  let nt = term_of_extracted t and nu = term_of_extracted u in
  List.iter (fun fuel ->
    equal (Printf.sprintf "%s/conv/%d" name fuel)
      (conv_to_extracted (N.convert ~sg:nsg fuel nt nu)) (X.convert xsg fuel t u)) fuels

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
    "fix", Fix (Pi (Bool, Bool), 0, Lam (Var 0));
    "fix step", Fix (Ann (Pi (Bool, Bool), Srt (Univ 0)), 0, Lam (Ann (Var 0, Bool)));
    "fix on a variable", App (Fix (Pi (Bool, Bool), 0, Lam (Var 0)), Var 0);
    "fix on a pair", App (Fix (Pi (Bool, Bool), 0, Lam (Var 0)), Pair (Tt, Tt));
    "match on a variable", Case ("Nat", Univ 0, Lam Bool, Var 0, [BTrue; Lam BFalse]);
    "match step", Case ("Nat", Univ 0, Ann (Lam Bool, Pi (Bool, Srt (Univ 0))), Var 0,
                         [Ann (BTrue, Bool); Lam BFalse]);
    "match on a λ", Case ("Nat", Univ 0, Lam Bool, Lam (Var 0), [BTrue]);
    "match without branches", Case ("Void", Prp, Lam Bool, Var 0, []);
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
    "coc", coc, N.coc;
    "predicative-prop", predicative_prop, N.predicative_prop;
  ] in
  let sorts = [Star; Box; Tri; Univ 0; Univ 1; Univ 2; Prp] in
  List.iter (fun (name, extracted, native) ->
    equal (name ^ "/primitives")
      (Option.map sort_to_extracted native.N.primitive_sort) extracted.spec_prim;
    equal (name ^ "/constants") native.N.constants extracted.spec_decls;
    List.iter (fun s ->
      let ns = sort_of_extracted s in
      equal (name ^ "/sort") (native.N.sort_allowed ns) (extracted.spec_sort s);
      List.iter (fun (cls, ncls) ->
        equal (name ^ "/allows elimination")
          (N.allows_elimination native ncls ns) (allows_elimination extracted cls s))
        (List.map (fun c -> (elim_class_to_extracted c, c)) [N.PropOnly; N.AllSorts]);
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
        extracted native fuel [BTrue] (Var 0);
      check_infer_open (system ^ "/open-context/infer-open/" ^ string_of_int fuel)
        extracted native fuel id_applied_ctx id_applied;
      check_infer_open (system ^ "/bad-context/infer-open/" ^ string_of_int fuel)
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
    "choose true", C.args_ctx, C.choose_at (Named.Const N.BTrue), Named.name "A",
      args_ctx, choose_at NTrue, NVar "A";
    "choose false", C.args_ctx, C.choose_at (Named.Const N.BFalse), Named.name "B",
      args_ctx, choose_at NFalse, NVar "B";
    "choose open", C.open_ctx, C.choose_at (Named.name "b"), Named.name "A",
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
    "void", El.void_ctx, El.void_elim, Named.name "A", void_ctx, void_elim, NVar "A";
    "void wrong scrutinee", El.void_ctx, Named.ElimVoid (El.void_family, Named.Const N.Tt),
      Named.name "A", void_ctx, NElimVoid (void_family, NTt), NVar "A";
    "unit tt", [], El.unit_elim (Named.Const N.Tt), Named.Const N.Bool, [], unit_elim NTt, NBool;
    "unit open", El.unit_ctx, El.unit_elim (Named.name "u"), Named.Const N.Bool,
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
  let build = Named.build [] in
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
    "double", N.EDef ("double", build (Named.arrow Co.nat Co.nat), build Co.double_body);
    "open", N.EDef ("bad", N.Var 0, N.Tt);
    "open elim", N.EElim ("Nat", N.Univ 1, N.Pi (N.Var 0, N.Var 1), true);
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
     Elim ("Nat", Univ 0); Elim ("Nat", Univ 1); Elim ("Nat", Prp); Def "double"; Ind "Bool2"];
  let nat = build Co.nat in
  let step_r = Named.abs ["m"; "r"] (Named.name "r") in
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
    "double body", Co.double_body, Named.arrow Co.nat Co.nat;
    "double one", Co.double (Co.succ Co.zero), Co.nat;
    "object first", Co.elim_with step_r (Co.double Co.zero), Co.nat;
    "unit at Nat", Named.Const N.Tt, Co.nat;
  ];
  (* eval_src on the spines of elimNat, from the bare instance to its full
     arity: short of it a value with active rules, stuck without them. *)
  List.iter (fun n ->
    let args = List.filteri (fun i _ -> i < n) [Named.abs ["_"] Co.nat; Co.zero; step_r; Co.zero] in
    let nt = build (Named.call Co.elim_nat args) in
    List.iter (fun (which, sg) ->
      check_eval_src ~sg ~fuels:[1; 5; const_fuel] (Printf.sprintf "constants/eval_src/%s/%d args" which n)
        nt (term_to_extracted nt))
      ["active", active; "inactive", inactive]) [0; 1; 2; 3; 4];
  (* The body of [double] in the signature without [double], and a body
     mentioning [double] there. *)
  let base = (nsg_base, sg_nat_base) and nat_to_nat = term_to_extracted (build (Named.arrow Co.nat Co.nat)) in
  check_check ~sg:base "constants/base/double body" predicative N.predicative const_fuel []
    (term_to_extracted (build Co.double_body)) nat_to_nat;
  check_check ~sg:base "constants/base/self reference" predicative N.predicative const_fuel []
    (term_to_extracted (build (Named.abs ["n"] (Co.double (Named.name "n"))))) nat_to_nat;
  let open_spine = App (term_to_extracted (build (Named.call Co.elim_nat
                                                [Co.const_nat; Co.zero; step_r])), Var 0) in
  check_infer ~sg:active "constants/open spine" predicative N.predicative const_fuel
    [term_to_extracted nat] open_spine;
  check_eval ~sg:active ~fuels:[0; 1; 5; const_fuel] "constants/open spine" open_spine;
  let in_iota t = term_to_extracted (C.term_in Co.iota_ctx t) in
  let n = Named.name in
  let iota_lhs = in_iota (Named.call Co.elim_nat [n "P"; n "z"; n "s"; Co.succ (n "n")]) in
  let iota_rhs =
    in_iota (Named.call (n "s") [n "n"; Named.call Co.elim_nat [n "P"; n "z"; n "s"; n "n"]]) in
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
    [Ind "Vec"; Ctor ("Vec", "nil"); Ctor ("Vec", "cons"); Elim ("Vec", Univ 0);
     Ind "W"; Ctor ("W", "sup"); Elim ("W", Univ 0);
     Ind "Tr"; Ctor ("Tr", "leaf"); Ctor ("Tr", "node"); Ctor ("Tr", "fork"); Ctor ("Tr", "twin"); Elim ("Tr", Univ 0)];
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
         (Named.call (Named.name "P") [Named.name "a";
            ctor (Named.name "A") (Named.name "h") (Named.name "a") (Named.name "f")]))))
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
    "vnot", Named.call Fa.vnot [Co.succ (Co.succ Co.zero); Fa.two_bools],
      Fa.vec Fa.bool (Co.succ (Co.succ Co.zero));
    "to_nat", Named.Apply (Fa.to_nat, Fa.succ_w (Fa.succ_w Fa.zero_w)), Co.nat;
    "label", Named.call Fa.label [Named.Const N.BTrue; Fa.tree], Fa.bool;
    "fork label", Named.call Fa.label [Named.Const N.BFalse; Fa.fork_tree], Fa.bool;
    "twin label", Named.call Fa.label [Named.Const N.BTrue; Fa.twin_tree], Fa.bool;
  ];
  (* match and fix: the same terms built independently, the same checker
     traces, normal-order and call-by-value results. *)
  let nmatch = Ma.signature and nboolp = Ma.boolp_signature in
  let mat = (nmatch, sg_match) and nat_sg = (nsg, sg_nat) and boolp = (nboolp, sg_boolp) in
  equal "match/signature" (List.map entry_to_extracted nmatch) sg_match;
  equal "match/boolp" (List.map entry_to_extracted nboolp) sg_boolp;
  List.iter (fun j ->
    equal ("match/rect ctx/" ^ string_of_int j)
      (List.map term_to_extracted (C.in_ctx (Ma.rect_ctx j))) (in_x (X.rect_ctx j))) [0; 1];
  let closed_terms = [
    "nat_rect 0", Ma.nat_rect 0, nat_rect 0;
    "nat_rect 1", Ma.nat_rect 1, nat_rect 1;
    "plus", Ma.plus_fix, plus_fix;
    "append", Ma.append, append;
    "copy", Ma.copy, copy;
    "missing branch", Ma.rect_with 0 [Named.name "z"], rect_body [NVar "z"];
    "repeated branch", Ma.rect_with 0 [Named.name "z"; Ma.succ_branch; Ma.succ_branch],
      rect_body [NVar "z"; succ_branch; succ_branch];
    "wrong motive", Ma.wrong_motive, wrong_motive;
    "loop", Ma.loop, loop;
    "struct past", Fixpoint ("f", Named.arrow Co.nat Co.nat, 1, Named.abs ["n"; "m"] (Named.name "m")),
      NFix ("f", NArrow (NConst (Ind "Nat"), NConst (Ind "Nat")), 1, NLam ("n", NLam ("m", NVar "m")));
    "struct bool", Fixpoint ("f", Named.arrow Fa.bool Fa.bool, 0, Named.abs ["b"] (Named.name "b")),
      NFix ("f", NArrow (NBool, NBool), 0, NLam ("b", NVar "b"));
    "short body", Fixpoint ("f", Named.arrow Co.nat Co.nat, 0, Named.name "f"),
      NFix ("f", NArrow (NConst (Ind "Nat"), NConst (Ind "Nat")), 0, NVar "f");
    "wrong scrutinee", Match ("Nat", N.Univ 0, Named.abs ["m"] Co.nat, Named.Const N.BTrue,
                              [Co.zero; Named.abs ["m"] (Named.name "m")]),
      NCase ("Nat", Univ 0, NLam ("m", NConst (Ind "Nat")), NTrue,
             [NConst (Ctor ("Nat", "zero")); NLam ("m", NVar "m")]);
  ] in
  List.iter (fun (name, nt, xt) ->
    let t = X.build [] xt in
    equal ("match/term/" ^ name) (term_to_extracted (build nt)) t;
    List.iter (fun (which, sg) ->
      check_infer ~sg ("match/infer/" ^ which ^ "/" ^ name) predicative N.predicative match_fuel [] t;
      check_infer ~sg ("match/infer prop/" ^ which ^ "/" ^ name) predicative_prop N.predicative_prop
        match_fuel [] t;
      check_eval ~sg ~fuels:[0; 1; 5] ("match/eval/" ^ which ^ "/" ^ name) t)
      ["nat", nat_sg; "match", mat; "families", fam]) closed_terms;
  List.iter (fun (name, nt, xt) ->
    let t = X.build [] xt in
    equal ("match/closed term/" ^ name) (term_to_extracted (build nt)) t;
    check_eval ~sg:mat ~fuels:[0; 1; 5; match_fuel] ("match/closed eval/" ^ name) t;
    check_eval_src ~sg:mat ~fuels:[0; 1; 3; 10; match_fuel] ("match/eval_src/" ^ name) (build nt) t) [
    "plus 2 3", Ma.plus (Ma.nat_numeral 2) (Ma.nat_numeral 3), NApp (NApp (plus, nat_numeral 2), nat_numeral 3);
    "append", Named.call Ma.append [Fa.bool; Ma.nat_numeral 1; Ma.nat_numeral 1; Ma.one_true; Ma.one_false],
      NApp (NApp (NApp (NApp (NApp (append, NBool), nat_numeral 1), nat_numeral 1), one_true), one_false);
    "copy", Named.Apply (Fa.to_nat, Named.call Ma.copy [Fa.bool; Fa.positions; Fa.succ_w (Fa.succ_w Fa.zero_w)]),
      NApp (to_nat, NApp (NApp (NApp (copy, NBool), positions), succ_w (succ_w zero_w)));
    "loop zero", Named.Apply (Ma.loop, Co.zero), NApp (loop, NConst (Ctor ("Nat", "zero")));
  ];
  (* Lazy δ with m, k as Var 0, Var 1: a folded spine shared by both
     sides, one unfolding, two disjoint ones, a difference after an
     unfolding, and nested spines where the inner one is unfolded, the
     outer one is, or the inner one does not help.  The unfoldings need
     more fuel than the default. *)
  let xplus a b = App (App (Const (Def "plus"), a), b) and xsucc a = App (Const (Ctor ("Nat", "succ")), a) in
  let m = Var 0 and k = Var 1 in
  List.iter (fun (name, t, u) -> convert_case ~sg:mat ~fuels:[0; 5; match_fuel] ("match/lazy/" ^ name) t u) [
    "shared spine", Pair (xplus k m, Bool), Pair (xplus k m, Unit);
    "one unfolding", xplus (xsucc k) m, xsucc (xplus k m);
    "two unfoldings", Pair (xplus (xsucc k) m, xplus (xsucc m) k), Pair (xsucc (xplus k m), xsucc (xplus m k));
    "difference after", Pair (xplus (xsucc k) m, Bool), Pair (xsucc (xplus k m), Unit);
    "inner unfolded", xplus (xplus (xsucc k) m) k, xplus (xsucc (xplus k m)) k;
    "outer unfolded", xplus (xsucc (xplus k m)) m, xsucc (xplus (xplus k m) m);
    "inner differs", xplus (xplus k m) k, xplus (xplus m k) k;
    "outer differs after", xplus (xplus (xsucc k) m) k, xplus (xsucc (xplus k m)) m;
  ];
  (* Open terms: the equations of nat_rect, neutral matches and fixes. *)
  List.iter (fun j ->
    let g = Ma.rect_ctx j and xg = X.rect_ctx j in
    let n = Named.name in
    let rect args = Named.call (Ma.nat_rect j) args and xrect args = X.napps (nat_rect j) args in
    let pzs = [n "P"; n "z"; n "s"] and xpzs = [NVar "P"; NVar "z"; NVar "s"] in
    List.iter (fun (name, lhs, rhs, xlhs, xrhs) ->
      let l = term_x xg xlhs and r = term_x xg xrhs in
      equal ("match/open lhs/" ^ name) (term_to_extracted (C.term_in g lhs)) l;
      equal ("match/open rhs/" ^ name) (term_to_extracted (C.term_in g rhs)) r;
      convert_case ~sg:nat_sg ("match/equation/" ^ name) l r;
      check_eval ~sg:nat_sg ~fuels:[0; 1; 5; match_fuel] ("match/open eval/" ^ name) l;
      check_infer ~sg:nat_sg ("match/open infer/" ^ name) predicative N.predicative match_fuel (in_x xg) l;
      check_eval_src ~sg:nat_sg ~fuels:[1; 5; 50] ("match/open eval_src/" ^ name) (C.term_in g lhs) l)
      [ Printf.sprintf "zero/%d" j, rect (pzs @ [Co.zero]), n "z", xrect (xpzs @ [NConst (Ctor ("Nat", "zero"))]), NVar "z";
        Printf.sprintf "succ/%d" j, rect (pzs @ [Co.succ (n "n")]),
          Named.call (n "s") [n "n"; rect (pzs @ [n "n"])],
          xrect (xpzs @ [NApp (NConst (Ctor ("Nat", "succ")), NVar "n")]),
          NApp (NApp (NVar "s", NVar "n"), xrect (xpzs @ [NVar "n"]));
        Printf.sprintf "free/%d" j, rect (pzs @ [n "n"]), rect (pzs @ [n "n"]),
          xrect (xpzs @ [NVar "n"]), xrect (xpzs @ [NVar "n"]) ]) [0; 1];
  equal "match/open match" (term_to_extracted (C.term_in (Ma.rect_ctx 0) Ma.open_match))
    (term_x (X.rect_ctx 0) open_match);
  check_infer ~sg:nat_sg "match/open match" predicative N.predicative match_fuel (in_x (X.rect_ctx 0))
    (term_x (X.rect_ctx 0) open_match);
  (* The category of elimination in the typing of match. *)
  List.iter (fun (name, s, ty, a, b, xs, xty, xa, xb, g, xg) ->
    let t = term_x xg (match_boolp xs xty xa xb) in
    equal ("match/boolp term/" ^ name) (term_to_extracted (C.term_in g (Ma.match_boolp s ty a b))) t;
    check_infer ~sg:boolp ("match/boolp/" ^ name) predicative_prop N.predicative_prop match_fuel (in_x xg) t;
    check_eval ~sg:boolp ("match/boolp eval/" ^ name) t)
    [ "into Prop", N.Prp, Named.name "A", Named.name "a", Named.name "a",
        Prp, NVar "A", NVar "a", NVar "a",
        ["a", Named.name "A"; "A", Named.Sort N.Prp], [("a", NVar "A"); ("A", NSrt Prp)];
      "into Type₀", N.Univ 0, Fa.bool, Named.Const N.BTrue, Named.Const N.BFalse,
        Univ 0, NBool, NTrue, NFalse, [], [] ];
  (* The types of the motive and the branches, for the parameters of a
     vector and of a W-type. *)
  let ps_vec = [Var 7] and ps_w = [Var 3; Var 2] in
  List.iter (fun (name, d, nd, ps, s) ->
    let nps = List.map term_of_extracted ps in
    equal ("match/motive type/" ^ name)
      (term_to_extracted (N.case_motive_type nd nps (sort_of_extracted s))) (case_motive_type d ps s);
    List.iter2 (fun c nc ->
      equal ("match/branch type/" ^ name ^ "/" ^ nc.N.ctor_name)
        (term_to_extracted (N.case_branch_type nd nps (N.Var 5) nc)) (case_branch_type d ps (Var 5) c))
      d.ind_ctors nd.N.ind_ctors)
    ["vec", vec_desc, Fa.vec_desc, ps_vec, Univ 1; "w", w_desc, Fa.w_desc, ps_w, Prp;
     "tr", tr_desc, Fa.tr_desc, [Var 1; Var 0], Univ 0];
  (* The guard: the same terms built independently, the same checker
     traces and guard results, and the guard of every body of a corpus
     under several marks and structural positions. *)
  let guards = [
    "half", Ma.half, half; "size", Ma.size, size; "under binders", Ma.under_binders, under_binders;
    "g pred", Ma.g_pred, g_pred; "partial", Ma.partial, partial; "bare", Ma.bare, bare;
    "nested", Ma.nested, nested; "shadowed", Ma.shadowed, shadowed;
    "nonrec field", Ma.nonrec_field, nonrec_field; "half position", Ma.half_position, half_position;
    "loop", Ma.loop, loop; "nat_rect", Ma.nat_rect 0, nat_rect 0; "plus", Ma.plus_fix, plus_fix;
    "append", Ma.append, append; "copy", Ma.copy, copy;
  ] in
  List.iter (fun (name, nt, xt) ->
    let t = X.build [] xt in
    let native = build nt in
    equal ("guard/term/" ^ name) (term_to_extracted native) t;
    (match native, t with
     | N.Fix (_, k, nb), X.Fix (_, _, b) ->
         List.iter (fun (which, nsg, xsg) ->
           equal ("guard/fix/" ^ which ^ "/" ^ name)
             (guard_result_to_extracted (N.guard_fix nsg k nb)) (X.guard_fix xsg k b))
           ["nat", nsg, sg_nat; "match", nmatch, sg_match]
     | _ -> failwith ("guard/not a fix/" ^ name));
    List.iter (fun (which, sg) ->
      check_infer ~sg ("guard/infer/" ^ which ^ "/" ^ name) predicative N.predicative match_fuel [] t)
      ["nat", nat_sg; "match", mat]) guards;
  (* A body short of its k + 1 leading λ is refused by the guard itself. *)
  List.iter (fun (name, k, nb) ->
    equal ("guard/short body/" ^ name)
      (guard_result_to_extracted (N.guard_fix nsg k nb)) (X.guard_fix sg_nat k (term_to_extracted nb)))
    ["var", 0, N.Var 0; "one λ of two", 1, N.Lam (N.Var 0); "λ of three", 2, N.Lam (N.App (N.Var 0, N.Var 0))];
  let mark_lists = [
    []; [N.Self]; [N.Arg; N.Self]; [N.Sub 0; N.Arg; N.Self]; [N.Sub 1; N.Large; N.Arg; N.Self];
    [N.Large; N.Sub 2; N.Self; N.Arg]; [N.Self; N.Sub 0]; N.entry_marks 2;
  ] in
  let bodies =
    List.concat_map (fun (_, nt, _) ->
      match build nt with
      | N.Fix (_, _, b) ->
          let rec unlam acc = function N.Lam b -> unlam (b :: acc) b | _ -> acc in
          unlam [b] b
      | _ -> []) guards
    @ List.map (fun (_, t) -> term_of_extracted t) samples in
  List.iteri (fun i b ->
    List.iteri (fun j ms ->
      List.iter (fun k ->
        List.iter (fun spine ->
          equal (Printf.sprintf "guard/sweep/%d/%d/%d/%b" i j k spine)
            (guard_result_to_extracted (N.guard nmatch k ms b spine))
            (X.guard sg_match k (List.map mark_to_extracted ms) (term_to_extracted b) spine)) [false; true])
        [0; 1; 2; 3]) mark_lists) bodies;
  List.iter (fun n ->
    let nt = Named.Apply (Ma.half, Ma.nat_numeral n) in
    let t = term_to_extracted (build nt) in
    check_eval ~sg:nat_sg ~fuels:[0; 5; match_fuel] ("guard/half/" ^ string_of_int n) t;
    check_eval_src ~sg:nat_sg ~fuels:[match_fuel] ("guard/half eval_src/" ^ string_of_int n) (build nt) t)
    [0; 1; 4; 5];
  Printf.printf "reference: %d comparisons with extraction passed\n" !assertions
