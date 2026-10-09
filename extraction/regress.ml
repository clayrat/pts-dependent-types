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
    (answer_term id_applied_ctx (run_infer system_u_minus 100 id_applied_ctx id_applied))
    "accepted: A";
  expect "no (∗, □)"
    (answer_term star_box_ctx (run_infer system_u_minus 100 star_box_ctx star_box))
    "rejected: no rule (∗, □, _) for #0 → ∗";
  expect "Type₁"
    (answer_term [] (run_infer predicative 100 [] (map_sorts u_to_univ id_ty)))
    "accepted: Type₁";
  expect "not Type₀"
    (answer_unit (run_check predicative 100 [] (map_sorts u_to_univ id_ty) (Srt (Univ 0))))
    "rejected: ΠA:Type₀. A → A has type Type₁, expected Type₀";
  expect "large elimination" (answer_unit (run_check predicative 100 [] Tt large_elim_ty))
    "accepted";
  expect "no fuel" (answer_unit (run_check predicative 0 [] Tt large_elim_ty))
    "undecided: out of fuel while typing Unit";
  expect "Ω" (pp_eval_result (normalize 5 raw_omega)) "out of fuel at (λx. x x) (λx. x x)";
  expect "bad family"
    (answer_term []
       (run_infer predicative 100 []
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
    (answer_term [] (run_infer system_u_minus looping_fuel [] (looping 0)))
    "accepted: ΠA:∗. (A → A) → A";
  expect "L₀ predicative"
    (match snd (run_infer pure_predicative looping_fuel [] (map_sorts u_to_univ (looping 0))) with
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
  if !failures > 0 then exit 1 else print_endline "regress: all tests passed"
