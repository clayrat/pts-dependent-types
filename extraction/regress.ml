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
  expect "Ω" (pp_eval_result (normalize 5 omega)) "out of fuel at (λx. x x) (λx. x x)";
  expect "bad family"
    (answer_term []
       (run_infer predicative 100 []
          (ElimBool (Ann (Lam Bool, Pi (Unit, Srt (Univ 0))), BTrue, BTrue, BTrue))))
    "rejected: result family ((λx. Bool) : Unit → Type₀) is over Unit, expected over Bool";
  expect "context entry"
    (pp_event ~ctx:id_applied_ctx (EvCtxEntry (1, Var 0))) "context entry x : A";
  if !failures > 0 then exit 1 else print_endline "regress: all tests passed"
