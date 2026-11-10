(* Regression tests of the extracted checker and of the printer. *)
open Deptypes
open Pretty

let failures = ref 0

let expect name actual expected =
  if actual <> expected then begin
    incr failures;
    Printf.printf "FAIL %s\n  expected: %s\n  actual:   %s\n" name expected actual
  end

let answer_term g (_, a) = pp_answer (pp_term ~names:(ctx_names g)) a
let answer_unit (_, a) = pp_answer (fun () -> "") a

let () =
  expect "id type" (pp_term id_ty) "ΠA:∗. A → A";
  expect "id term" (pp_term id_tm) "((λA. λx. x) : ΠA:∗. A → A)";
  expect "id context" (pp_ctx id_applied_ctx) "A : ∗, x : A";
  expect "dangling index" (pp_term (App (Var 0, Var 3))) "#0 #3";
  expect "depth bound" (pp_term ~depth:2 (App (App (Var 0, Var 1), Var 2))) "… #2";
  expect "id applied"
    (answer_term id_applied_ctx (run_infer system_u_minus sig_empty 100 id_applied_ctx id_applied))
    "accepted: A";
  expect "no (∗, □)"
    (answer_term star_box_ctx (run_infer system_u_minus sig_empty 100 star_box_ctx star_box))
    "rejected: no rule (∗, □, _) for #0 → ∗";
  expect "Type₁"
    (answer_term [] (run_infer predicative sig_empty 100 [] (map_sorts u_to_univ id_ty)))
    "accepted: Type₁";
  expect "not Type₀"
    (answer_unit (run_check predicative sig_empty 100 [] (map_sorts u_to_univ id_ty) (Srt (Univ 0))))
    "rejected: ΠA:Type₀. A → A has type Type₁, expected Type₀";
  expect "large elimination" (answer_unit (run_check predicative sig_empty 100 [] Tt large_elim_ty))
    "accepted";
  expect "no fuel" (answer_unit (run_check predicative sig_empty 0 [] Tt large_elim_ty))
    "undecided: out of fuel while typing Unit";
  expect "Ω" (pp_eval_result (normalize sig_empty 5 raw_omega)) "out of fuel at (λx. x x) (λx. x x)";
  expect "bad family"
    (answer_term []
       (run_infer predicative sig_empty 100 []
          (ElimBool (Ann (Lam Bool, Pi (Unit, Srt (Univ 0))), BTrue, BTrue, BTrue))))
    "rejected: result family ((λx. Bool) : Unit → Type₀) is over Unit, expected over Bool";
  expect "context entry"
    (pp_event ~ctx:id_applied_ctx (EvCtxEntry (1, Var 0))) "context entry x : A";
  (* The term builder, used from OCaml: names in, de Bruijn terms out. *)
  let named_id =
    NAnn (NLam ("A", NLam ("x", NVar "x")), NPi ("A", NSrt Star, NArrow (NVar "A", NVar "A")))
  in
  let resolved = function Ok t -> pp_term t | Err x -> "unbound " ^ x in
  expect "named id" (resolved (resolve [] named_id)) (pp_term id_tm);
  expect "named unbound" (resolved (resolve [ "x" ] (NApp (NVar "x", NVar "y")))) "unbound y";
  expect "named context"
    (match resolve_ctx [ ("x", NVar "A"); ("A", NSrt Star) ] with
     | Ok (names, g) -> String.concat "," names ^ " ⊢ " ^ pp_ctx g
     | Err x -> "unbound " ^ x)
    "x,A ⊢ A : ∗, x : A";
  (* The looping combinator. *)
  expect "L₀ in U⁻"
    (answer_term [] (run_infer system_u_minus sig_empty looping_fuel [] (looping 0)))
    "accepted: ΠA:∗. (A → A) → A";
  expect "L₀ predicative"
    (match snd (run_infer pure_predicative sig_empty looping_fuel [] (map_sorts u_to_univ (looping 0))) with
     | Rejected (EMismatch (_, Srt (Univ 0), Srt (Univ 2))) -> "Type₂, expected Type₀"
     | a -> pp_answer pp_term a)
    "Type₂, expected Type₀";
  expect "L unfolds"
    (String.concat ","
       (List.map
          (fun n ->
            string_of_bool
              (unfolds_to unfolding_fuel (looping_applied n) (Var 0) (looping_applied (n + 1))))
          [ 0; 1 ]))
    "true,true";
  (* Church numerals and strictness. *)
  List.iter
    (fun ((name, t), expected) ->
      expect ("strictness: " ^ name)
        (string_of_bool
           (typed_in_u_minus t cNat
            && verdict_of expected (observe observe_fuel (church t)) = best_verdict expected))
        "true")
    strictness_cases;
  expect "lazy test"
    (pp_observation
       (observe observe_fuel (church (ifz_lazy cNat (NApp (csucc, omega_nat)) czero (numeral 1)))))
    "1";
  (* The PCF translation. *)
  List.iter
    (fun ((name, t), expected) ->
      expect ("translation: " ^ name)
        (string_of_bool
           (pcf_as_expected expected t
            && (match translate_program_checked looping_fuel t with
                | Ok u -> verdict_of expected (observe (fuel_for expected) u) = best_verdict expected
                | Err _ -> false)))
        "true")
    pcf_cases;
  (* choose. *)
  let accepted = function Accepted _ -> "accepted" | Rejected _ -> "rejected" | Undecided _ -> "undecided" in
  let names g = List.map fst g in
  expect "choose typed"
    (accepted (snd (run_check predicative sig_empty choose_fuel (in_ctx types_ctx)
                      (term_in types_ctx choose) (term_in types_ctx choose_ty))))
    "accepted";
  List.iter
    (fun (b, ty, v, label) ->
      expect ("choose " ^ label ^ " typed")
        (accepted (snd (run_check predicative sig_empty choose_fuel (in_ctx args_ctx)
                          (term_in args_ctx (choose_at b)) (term_in args_ctx (NVar ty)))))
        "accepted";
      expect ("choose " ^ label ^ " evaluates")
        (pp_eval_result ~names:(names args_ctx) (normalize sig_empty choose_fuel (term_in args_ctx (choose_at b))))
        ("normal form " ^ v))
    [ (NTrue, "A", "a", "true"); (NFalse, "B", "c", "false") ];
  expect "choose open not A"
    (accepted (snd (run_check predicative sig_empty choose_fuel (in_ctx open_ctx)
                      (term_in open_ctx (choose_at (NVar "b"))) (term_in open_ctx (NVar "A")))))
    "rejected";
  expect "choose swapped"
    (accepted (snd (run_check predicative sig_empty choose_fuel (in_ctx types_ctx)
                      (term_in types_ctx choose_swapped) (term_in types_ctx choose_ty))))
    "rejected";
  expect "low family"
    (pp_answer pp_term (snd (run_infer predicative sig_empty choose_fuel [] (build [] low_family))))
    "rejected: Type₀ has type Type₁, expected Type₀";
  (* Void and Unit. *)
  expect "void elimination"
    (accepted (snd (run_check predicative sig_empty elim_fuel (in_ctx void_ctx) (term_in void_ctx void_elim)
                      (term_in void_ctx (NVar "A")))))
    "accepted";
  expect "unit elimination typed"
    (accepted (snd (run_check predicative sig_empty elim_fuel [] (build [] (unit_elim NTt)) Bool)))
    "accepted";
  expect "unit elimination computes"
    (pp_eval_result (normalize sig_empty elim_fuel (build [] (unit_elim NTt)))) "normal form true";
  expect "unit elimination open"
    (accepted (snd (run_check predicative sig_empty elim_fuel (in_ctx unit_ctx)
                      (term_in unit_ctx (unit_elim (NVar "u"))) Bool)))
    "rejected";
  (* Σ and constants *)
  expect "product" (pp_term (Sigma (Bool, Unit))) "Bool × Unit";
  expect "dependent sum" (pp_term (Sigma (Srt (Univ 0), Var 0))) "ΣA:Type₀. A";
  expect "pair" (pp_term (Pair (BTrue, Tt))) "⟨true, tt⟩";
  expect "projections" (pp_term ~names:[ "p" ] (App (Fst (Var 0), Snd (Var 0)))) "fst p (snd p)";
  expect "constants"
    (pp_term (App (App (Const (Elim ("Nat", Univ 1)), Const (Ind "Nat")), Const (Ctor ("Nat", "zero")))))
    "elimNat[1] Nat zero";
  expect "eliminator into Prop" (pp_term (Const (Elim ("eq", Prp)))) "elimeq[Prop]";
  expect "dependent pair"
    (answer_unit (run_check predicative sig_empty 100 [] (Pair (BTrue, Tt)) (Sigma (Bool, Unit))))
    "accepted";
  expect "no Σ in U⁻"
    (answer_term [] (run_infer system_u_minus sig_empty 100 [] (Sigma (Srt Star, Var 0))))
    "rejected: no Σ-rule (□, ∗, _) for ΣA:∗. A";
  expect "unknown constant"
    (answer_term [] (run_infer predicative sig_empty 100 [] (Const (Def "double"))))
    "rejected: the constant double is not in the signature";
  expect "constants off"
    (answer_term [] (run_infer system_u_minus sig_empty 100 [] (Const (Ind "Nat"))))
    "rejected: Nat: constants are off in this system";
  (* match and fix (CIC/Match.v). *)
  let infer_in s sg g t = answer_term (in_ctx g) (run_infer s sg match_fuel (in_ctx g) (term_in g t)) in
  expect "nat_rect" (pp_term (build [] (nat_rect 0))) "fix f : Πx:Nat → Type₀. x zero → (Πy:Nat. x y → x (succ y)) → Πy:Nat. x y {struct 3} := λx. λy. λz. λu. matchNat[0] u return (λv. x v) with y | λv. z v (f x y z v) end";
  expect "nat_rect typed" (infer_in predicative sg_nat [] (nat_rect 1)) "accepted: Πx:Nat → Type₁. x zero → (Πy:Nat. x y → x (succ y)) → Πy:Nat. x y";
  expect "append typed" (infer_in predicative sg_match [] append) "accepted: ΠA:Type₀. Πx:Nat. Πy:Nat. Vec A x → Vec A y → Vec A (plus x y)";
  expect "copy typed" (infer_in predicative sg_families [] copy) "accepted: ΠA:Type₀. Πx:A → Type₀. W A x → W A x";
  expect "plus computes"
    (pp_eval_result (normalize sg_match match_fuel (build [] (napps plus [ nat_numeral 2; nat_numeral 3 ]))))
    "normal form succ (succ (succ (succ (succ zero))))";
  expect "open match"
    (pp_eval_result ~names:(ctx_names (in_ctx (rect_ctx 0)))
       (normalize sg_nat match_fuel (term_in (rect_ctx 0) open_match)))
    "normal form matchNat[0] u return (λv. x v) with y | λv. z v ((fix f : Πw:Nat → Type₀. w zero → (Πx':Nat. w x' → w (succ x')) → Πx':Nat. w x' {struct 3} := λw. λx'. λy'. λz'. matchNat[0] z' return (λu'. w u') with x' | λu'. y' u' (f w x' y' u') end) x y z v) end";
  expect "missing branch" (infer_in predicative sg_nat [] (rect_body [ NVar "z" ])) "rejected: matchNat[0] #0 return (λx. #3 x) with #2 end: 1 branches for 2 constructors";
  expect "wrong motive" (infer_in predicative sg_nat [] wrong_motive) "rejected: #4 #0 has type Type₁, expected Type₀";
  expect "motive into Type₀ on BoolP"
    (infer_in predicative_prop sg_boolp [] (match_boolp (Univ 0) NBool NTrue NFalse)) "rejected: the category of elimination of BoolP does not allow motives in Type₀";
  expect "structural position past the type"
    (infer_in predicative sg_nat [] (NFix ("f", NArrow (NConst (Ind "Nat"), NConst (Ind "Nat")), 1,
                                           NLam ("n", NLam ("m", NVar "m")))))
    "rejected: fix f : Nat → Nat {struct 1} := λx. λy. y: no argument 1 in its type, Nat is not a Π-type";
  expect "structural argument not inductive"
    (infer_in predicative sg_nat [] (NFix ("f", NArrow (NBool, NBool), 0, NLam ("b", NVar "b"))))
    "rejected: fix f : Bool → Bool {struct 0} := λx. x: its structural argument 0 has type Bool, not an inductive type";
  expect "eval_src"
    (pp_cbv_result (eval_src sg_match match_fuel (build [] (napps append [ NBool; nat_numeral 1; nat_numeral 1; one_true; one_false ]))))
    "value cons Bool (succ zero) true (cons Bool zero false (nil Bool))";
  expect "eval_src stuck"
    (pp_cbv_result ~names:(ctx_names (in_ctx (rect_ctx 0)))
       (eval_src sg_nat match_fuel (term_in (rect_ctx 0) open_match)))
    "stuck at u";
  (* The guard (CIC/GuardExamples.v). *)
  let guard_result t = match guard_of sg_match t with Ok () -> "guarded" | Err e -> pp_guard_error e in
  expect "half" (infer_in predicative sg_nat [] half) "accepted: Nat → Nat";
  expect "half computes"
    (pp_eval_result (normalize sg_nat match_fuel (build [] (NApp (half, nat_numeral 5)))))
    "normal form succ (succ zero)";
  expect "size on Tr" (guard_result size) "guarded";
  expect "loop" (infer_in predicative sg_nat [] loop) "rejected: the guard refuses the call #1 #0: #0 is not a strict subterm of the structural argument";
  expect "g (pred k)" (infer_in predicative sg_nat [] g_pred) "rejected: the guard refuses the call #2 (((λx. matchNat[0] x return (λy. Nat) with zero | λy. y end) : Nat → Nat) #0): ((λx. matchNat[0] x return (λy. Nat) with zero | λy. y end) : Nat → Nat) #0 is not a strict subterm of the structural argument";
  expect "partial call" (infer_in predicative sg_nat [] partial) "rejected: the guard refuses the partial call #3 #2: the structural argument is missing";
  expect "bare function" (infer_in predicative sg_nat [] bare) "rejected: the guard refuses the partial call #2: the structural argument is missing";
  expect "nested call" (infer_in predicative sg_nat [] nested) "rejected: the guard refuses the call #3 #2 #1: #2 is not a strict subterm of the structural argument";
  expect "non-recursive field" (guard_result nonrec_field) "the call #5 #2 #1: #1 is not a strict subterm of the structural argument";
  expect "one of two positions" (guard_result half_position) "the call #6 #5 #4 #1 (#0 #1): #0 #1 is not a strict subterm of the structural argument";
  expect "guard event" (pp_event (EvGuard 3)) "  guard: every recursive call is on a strict subterm of argument 3";
  if !failures > 0 then exit 1 else print_endline "regress: all tests passed"
