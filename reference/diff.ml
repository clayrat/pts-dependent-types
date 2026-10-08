(* Compare the independent OCaml reference with Rocq extraction.  Answers,
   intermediate evaluator results and complete checker traces must agree. *)

module X = Deptypes
module N = Pts_native
module L = Looping

let sort_of_extracted = function
  | X.Star -> N.Star | X.Box -> N.Box | X.Tri -> N.Tri | X.Univ i -> N.Univ i

let sort_to_extracted = function
  | N.Star -> X.Star | N.Box -> X.Box | N.Tri -> X.Tri | N.Univ i -> X.Univ i

let rec term_of_extracted = function
  | X.Srt s -> N.Srt (sort_of_extracted s)
  | X.Var n -> N.Var n
  | X.Pi (a, b) -> N.Pi (term_of_extracted a, term_of_extracted b)
  | X.Lam b -> N.Lam (term_of_extracted b)
  | X.App (f, a) -> N.App (term_of_extracted f, term_of_extracted a)
  | X.Ann (t, a) -> N.Ann (term_of_extracted t, term_of_extracted a)
  | X.Void -> N.Void
  | X.ElimVoid (c, e) -> N.ElimVoid (term_of_extracted c, term_of_extracted e)
  | X.Unit -> N.Unit | X.Tt -> N.Tt
  | X.ElimUnit (c, branch, u) ->
      N.ElimUnit (term_of_extracted c, term_of_extracted branch, term_of_extracted u)
  | X.Bool -> N.Bool | X.BTrue -> N.BTrue | X.BFalse -> N.BFalse
  | X.ElimBool (c, yes, no, b) ->
      N.ElimBool (term_of_extracted c, term_of_extracted yes,
                  term_of_extracted no, term_of_extracted b)

let rec term_to_extracted = function
  | N.Srt s -> X.Srt (sort_to_extracted s)
  | N.Var n -> X.Var n
  | N.Pi (a, b) -> X.Pi (term_to_extracted a, term_to_extracted b)
  | N.Lam b -> X.Lam (term_to_extracted b)
  | N.App (f, a) -> X.App (term_to_extracted f, term_to_extracted a)
  | N.Ann (t, a) -> X.Ann (term_to_extracted t, term_to_extracted a)
  | N.Void -> X.Void
  | N.ElimVoid (c, e) -> X.ElimVoid (term_to_extracted c, term_to_extracted e)
  | N.Unit -> X.Unit | N.Tt -> X.Tt
  | N.ElimUnit (c, branch, u) ->
      X.ElimUnit (term_to_extracted c, term_to_extracted branch, term_to_extracted u)
  | N.Bool -> X.Bool | N.BTrue -> X.BTrue | N.BFalse -> X.BFalse
  | N.ElimBool (c, yes, no, b) ->
      X.ElimBool (term_to_extracted c, term_to_extracted yes,
                  term_to_extracted no, term_to_extracted b)

let error_to_extracted = function
  | N.EUnboundVar n -> X.EUnboundVar n
  | N.ENotInSystem s -> X.ENotInSystem (sort_to_extracted s)
  | N.ETopSort s -> X.ETopSort (sort_to_extracted s)
  | N.ENoRule (t, a, b) ->
      X.ENoRule (term_to_extracted t, sort_to_extracted a, sort_to_extracted b)
  | N.ENotASort (t, ty) -> X.ENotASort (term_to_extracted t, term_to_extracted ty)
  | N.ENotAPi (t, ty) -> X.ENotAPi (term_to_extracted t, term_to_extracted ty)
  | N.EMismatch (t, expected, inferred) ->
      X.EMismatch (term_to_extracted t, term_to_extracted expected,
                   term_to_extracted inferred)
  | N.EStuckType (t, expected, inferred) ->
      X.EStuckType (term_to_extracted t, term_to_extracted expected,
                    term_to_extracted inferred)
  | N.ECannotInfer t -> X.ECannotInfer (term_to_extracted t)
  | N.ENoPrimitives t -> X.ENoPrimitives (term_to_extracted t)
  | N.EBadFamily (c, expected, actual) ->
      X.EBadFamily (term_to_extracted c, term_to_extracted expected,
                    term_to_extracted actual)

let event_to_extracted = function
  | N.EvCtxEntry (n, ty) -> X.EvCtxEntry (n, term_to_extracted ty)
  | N.EvExpected ty -> X.EvExpected (term_to_extracted ty)
  | N.EvTerm t -> X.EvTerm (term_to_extracted t)
  | N.EvAxiom (a, b) -> X.EvAxiom (sort_to_extracted a, sort_to_extracted b)
  | N.EvRule (a, b, c) ->
      X.EvRule (sort_to_extracted a, sort_to_extracted b, sort_to_extracted c)
  | N.EvUnfoldSort (t, ty, s) ->
      X.EvUnfoldSort (term_to_extracted t, term_to_extracted ty, sort_to_extracted s)
  | N.EvUnfoldPi (t, ty, a, b) ->
      X.EvUnfoldPi (term_to_extracted t, term_to_extracted ty,
                    term_to_extracted a, term_to_extracted b)
  | N.EvArg (t, ty) -> X.EvArg (term_to_extracted t, term_to_extracted ty)
  | N.EvSubst (b, u, result) ->
      X.EvSubst (term_to_extracted b, term_to_extracted u, term_to_extracted result)
  | N.EvConv (a, b, common) ->
      X.EvConv (term_to_extracted a, term_to_extracted b, term_to_extracted common)
  | N.EvFamily (c, domain, s) ->
      X.EvFamily (term_to_extracted c, term_to_extracted domain, sort_to_extracted s)

let answer_to_extracted value = function
  | N.Accepted a -> X.Accepted (value a)
  | N.Rejected e -> X.Rejected (error_to_extracted e)
  | N.Undecided t -> X.Undecided (term_to_extracted t)

let eval_to_extracted = function
  | N.NormalForm t -> X.NormalForm (term_to_extracted t)
  | N.StuckTerm t -> X.StuckTerm (term_to_extracted t)
  | N.OutOfFuel t -> X.OutOfFuel (term_to_extracted t)

let head_to_extracted = function
  | N.HeadForm t -> X.HeadForm (term_to_extracted t)
  | N.HeadOutOfFuel t -> X.HeadOutOfFuel (term_to_extracted t)

let shape_to_extracted = function
  | N.Step t -> X.Steps (term_to_extracted t)
  | N.Neutral -> X.IsNe | N.Normal -> X.IsNf | N.Stuck -> X.IsStuck

let conv_to_extracted = function
  | N.ConvEqual t -> X.ConvEqual (term_to_extracted t)
  | N.ConvDifferent -> X.ConvDifferent
  | N.ConvOutOfFuel -> X.ConvOutOfFuel
  | N.ConvStuck -> X.ConvStuck

let assertions = ref 0

let equal label native extracted =
  incr assertions;
  if native <> extracted then failwith ("reference differs from extraction: " ^ label)

let check_infer name xspec nspec fuel gamma term =
  let ngamma = List.map term_of_extracted gamma in
  let nterm = term_of_extracted term in
  let events, result = N.run_infer nspec fuel ngamma nterm in
  let native = List.map event_to_extracted events, answer_to_extracted term_to_extracted result in
  equal name native (X.run_infer xspec fuel gamma term)

let check_check name xspec nspec fuel gamma term expected =
  let ngamma = List.map term_of_extracted gamma in
  let nterm = term_of_extracted term in
  let nexp = term_of_extracted expected in
  let events, result = N.run_check nspec fuel ngamma nterm nexp in
  let native = List.map event_to_extracted events, answer_to_extracted Fun.id result in
  equal name native (X.run_check xspec fuel gamma term expected)

let check_eval ?native name term =
  let native = match native with Some t -> t | None -> term_of_extracted term in
  equal (name ^ "/classify") (shape_to_extracted (N.classify native)) (X.classify term);
  List.iter (fun fuel ->
    let trace, result = N.normalize_trace fuel native in
    equal (Printf.sprintf "%s/trace/%d" name fuel)
      (List.map term_to_extracted trace, eval_to_extracted result)
      (X.normalize_trace fuel term);
    equal (Printf.sprintf "%s/normalize/%d" name fuel)
      (eval_to_extracted (N.normalize fuel native)) (X.normalize fuel term);
    equal (Printf.sprintf "%s/whnf/%d" name fuel)
      (head_to_extracted (N.whnf fuel native)) (X.whnf fuel term)) [0; 1; 2; 5]

let convert_case name t u =
  let nt = term_of_extracted t and nu = term_of_extracted u in
  List.iter (fun fuel ->
    equal (Printf.sprintf "%s/conv/%d" name fuel)
      (conv_to_extracted (N.convert fuel nt nu)) (X.convert fuel t u)) [0; 1; 2; 5]

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
    List.iter (fun s ->
      let ns = sort_of_extracted s in
      equal (name ^ "/sort") (native.N.sort_allowed ns) (extracted.spec_sort s);
      equal (name ^ "/axiom")
        (Option.map sort_to_extracted (native.N.axiom ns)) (extracted.spec_axiom s);
      List.iter (fun t ->
        equal (name ^ "/product")
          (Option.map sort_to_extracted (native.N.product ns (sort_of_extracted t)))
          (extracted.spec_rule s t)) sorts) sorts) specs;
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
      (X.run_infer system_u_minus looping_fuel [] (looping n))) [0; 1];
  check_infer "looping/predicative" pure_predicative N.pure_predicative looping_fuel []
    (map_sorts u_to_univ (looping 0));
  check_eval ~native:(L.looping_applied 0) "looping applied" (looping_applied 0);
  List.iter (fun fuel ->
    equal (Printf.sprintf "looping unfolding/%d" fuel)
      (List.map term_to_extracted (fst (N.normalize_trace fuel (L.looping_applied 0))))
      (fst (X.normalize_trace fuel (looping_applied 0)))) [11; 30];
  Printf.printf "reference: %d comparisons with extraction passed\n" !assertions
