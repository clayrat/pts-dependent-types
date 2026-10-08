(* Lecture demonstrations: one checker, several PTS specifications.

   Each demo prints the input, the trace of the run and the answer.  The
   phase markers of the trace (context entries, expected type, term) use
   the names of the input context; in the other events, #k is a free
   variable with de Bruijn index k, since events carry open terms without
   their context.  Divergent evaluations are printed as bounded traces. *)
open Deptypes
open Pretty

let fuel = 100
let depth = 8

let header title =
  print_newline ();
  print_endline ("== " ^ title)

let print_trace g events = List.iter (fun ev -> print_endline (pp_event ~depth ~ctx:g ev)) events

let demo_infer title spec g t =
  header title;
  print_endline ("  " ^ pp_ctx g ^ " ⊢ " ^ pp_term ~names:(ctx_names g) t ^ " ⇑ ?");
  let events, answer = run_infer spec fuel g t in
  print_trace g events;
  print_endline (pp_answer ~depth (pp_term ~names:(ctx_names g)) answer)

let demo_check title spec g t ty =
  header title;
  let names = ctx_names g in
  print_endline ("  " ^ pp_ctx g ^ " ⊢ " ^ pp_term ~names t ^ " ⇓ " ^ pp_term ~names ty);
  let events, answer = run_check spec fuel g t ty in
  print_trace g events;
  print_endline (pp_answer ~depth (fun () -> "") answer)

let demo_normalize ?(names = []) ?(depth = depth) title steps t =
  header title;
  let trace, result = normalize_trace steps t in
  List.iteri (fun i u -> Printf.printf "  %d. %s\n" i (pp_term ~depth ~names u)) trace;
  print_endline (pp_eval_result ~depth ~names result)

(* The looping combinator: its trace in U⁻ has thousands of events, so
   only their number is printed. *)
let demo_looping () =
  header "U⁻: the looping combinator L₀ from Hurkens' paradox";
  let events, answer = run_infer system_u_minus looping_fuel [] (looping 0) in
  Printf.printf "  ⊢ L₀ ⇑ ?   (%d trace events)\n" (List.length events);
  print_endline (pp_answer (pp_term ~depth) answer);
  header "Predicative: L₀ with ∗, □, △ read as Type₀, Type₁, Type₂";
  let events, answer =
    run_infer pure_predicative looping_fuel [] (map_sorts u_to_univ (looping 0)) in
  Printf.printf "  ⊢ L₀ ⇑ ?   (%d trace events before the failure)\n" (List.length events);
  print_endline (pp_answer ~depth:6 (pp_term ~depth) answer);
  demo_normalize ~names:[ "f"; "β" ] ~depth:4
    "U⁻: L₀ β f reaches f M by normal order (β : ∗, f : β → β)" 11 (looping_applied 0);
  header "U⁻: M meets L₁ β f, and so on: Lₙ β f =β f (Lₙ₊₁ β f)";
  List.iter
    (fun n ->
      Printf.printf "  n = %d: %b\n" n
        (unfolds_to unfolding_fuel (looping_applied n) (Var 0) (looping_applied (n + 1))))
    [ 0; 1; 2 ]

let () =
  print_endline "In events, #k is the free variable with de Bruijn index k.";
  demo_infer "U⁻: the polymorphic identity applied, id A x" system_u_minus
    id_applied_ctx id_applied;
  demo_infer "U⁻: types do not depend on terms, no rule (∗, □)" system_u_minus
    star_box_ctx star_box;
  demo_infer "U⁻: primitives are off" system_u_minus [] Bool;
  demo_infer "Predicative: ΠA:Type₀. A → A lives in Type₁" predicative []
    (map_sorts u_to_univ id_ty);
  demo_check "Predicative: ... and not in Type₀" predicative []
    (map_sorts u_to_univ id_ty) (Srt (Univ 0));
  demo_check "Predicative: large elimination computes the type Unit" predicative []
    Tt large_elim_ty;
  demo_normalize "Raw Ω under normal order, 3 steps" 3 raw_omega;
  demo_looping ()
