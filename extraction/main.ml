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

(* Pads to [n] characters, counting UTF-8 code points, not bytes. *)
let pad n s =
  let width = ref 0 in
  String.iter (fun c -> if Char.code c land 0xC0 <> 0x80 then incr width) s;
  s ^ String.make (max 0 (n - !width)) ' '

(* Church numerals and the strictness of PCF. *)
let demo_strictness () =
  header "U⁻: Church numerals with the zero test strict in the whole numeral";
  List.iter
    (fun ((name, t), expected) ->
      let typed = typed_in_u_minus t cNat in
      let observed = observe observe_fuel (church t) in
      Printf.printf "  %s %s %s %s\n" (pad 36 name)
        (pad 10 (if typed then ": ℕ" else "ILL-TYPED"))
        (pad 31 (pp_observation observed))
        (match verdict_of expected observed with
         | Agrees -> "the PCF result"
         | NoResult -> "no result within the limit (PCF diverges)"
         | Contradicts -> "CONTRADICTS PCF"))
    strictness_cases;
  print_endline "  No result within the limit is not a proof of divergence.";
  header "U⁻: the usual lazy test answers where PCF diverges";
  let observed =
    observe observe_fuel (church (ifz_lazy cNat (NApp (csucc, omega_nat)) czero (numeral 1))) in
  Printf.printf "  ifz_lazy (succ Ω) then 0 else 1 = %s%s\n" (pp_observation observed)
    (if verdict_of None observed = Contradicts then ", which contradicts PCF" else "")

(* choose: a type computed from a boolean, in the predicative hierarchy. *)
let demo_choose () =
  let names g = List.map fst g in
  header "Predicative MLTT: choose : Πb:Bool. A → B → (if b then A else B)";
  let g = types_ctx in
  Printf.printf "  A : Type₀, B : Type₀ ⊢ choose ⇓ %s\n"
    (pp_term ~names:(names g) (term_in g choose_ty));
  print_endline
    (pp_answer (fun () -> "")
       (snd (run_check predicative choose_fuel (in_ctx g) (term_in g choose) (term_in g choose_ty))));
  let g = args_ctx in
  header "Predicative MLTT: choose true a c ⇓ A, with a : A and c : B";
  let events, answer =
    run_check predicative choose_fuel (in_ctx g) (term_in g (choose_at NTrue)) (term_in g (NVar "A")) in
  (* The application spine is typed in the context itself, so its events
     are printed with its names; the checks of the definition of choose
     and of the expected type are left out. *)
  let pp = pp_term ~depth:5 ~names:(names g) in
  List.iter
    (function
      | EvArg (u, a) -> Printf.printf "  argument %s : %s\n" (pp u) (pp a)
      | EvSubst (_, _, b') -> Printf.printf "    the rest of the type: %s\n" (pp b')
      | _ -> ())
    events;
  (match List.rev events with
   | EvConv (a, t, v) :: _ ->
       Printf.printf "  conversion: %s ≡ %s, both ⇝ %s\n" (pp a) (pp t) (pp v)
   | _ -> ());
  print_endline (pp_answer (fun () -> "") answer);
  List.iter
    (fun (b, label) ->
      Printf.printf "  choose %s a c by normal order: %s\n" label
        (pp_eval_result ~names:(names g) (normalize choose_fuel (term_in g (choose_at b)))))
    [ (NTrue, "true"); (NFalse, "false") ];
  let g = open_ctx in
  header "Predicative MLTT: with b : Bool free, the type stays neutral";
  (match snd (run_infer predicative choose_fuel (in_ctx g) (term_in g (choose_at (NVar "b")))) with
   | Accepted ty ->
       Printf.printf "  choose b a c ⇑ %s\n" (pp_term ~names:(names g) ty);
       Printf.printf "  its normal form: %s\n"
         (pp_eval_result ~names:(names g) (normalize choose_fuel ty))
   | a -> print_endline (pp_answer (pp_term ~names:(names g)) a));
  Printf.printf "  choose b a c ⇓ A: %s\n"
    (pp_answer ~depth:3 ~names:(names g) (fun () -> "")
       (snd (run_check predicative choose_fuel (in_ctx g) (term_in g (choose_at (NVar "b")))
               (term_in g (NVar "A")))));
  header "Predicative MLTT: errors";
  let g = types_ctx in
  Printf.printf "  branches swapped: %s\n"
    (pp_answer ~depth:4 (fun () -> "")
       (snd (run_check predicative choose_fuel (in_ctx g) (term_in g choose_swapped)
               (term_in g choose_ty))));
  Printf.printf "  (λ_. Type₀) ∷ Bool → Type₀: %s\n"
    (pp_answer (pp_term ~depth) (snd (run_infer predicative choose_fuel [] (build [] low_family))))

(* The eliminators of Void and Unit. *)
let demo_eliminators () =
  let names g = List.map fst g in
  let answer ty = pp_answer ~depth:4 (pp_term ~depth:4 ~names:ty) in
  header "Predicative MLTT: Void in a non-empty context";
  let g = void_ctx in
  Printf.printf "  A : Type₀, v : Void ⊢ %s ⇓ A: %s\n"
    (pp_term ~names:(names g) (term_in g void_elim))
    (pp_answer (fun () -> "")
       (snd (run_check predicative elim_fuel (in_ctx g) (term_in g void_elim) (term_in g (NVar "A")))));
  Printf.printf "  its normal form: %s\n"
    (pp_eval_result ~names:(names g) (normalize elim_fuel (term_in g void_elim)));
  header "Predicative MLTT: the dependent eliminator of Unit, C u = elimUnit (λ_. Type₀) Bool u";
  (match snd (run_infer predicative elim_fuel [] (build [] (unit_elim NTt))) with
   | Accepted ty -> Printf.printf "  ⊢ elimUnit C true tt ⇑ %s\n" (pp_term ~depth:4 ty)
   | a -> print_endline (answer [] a));
  Printf.printf "  C tt by normal order: %s\n"
    (pp_eval_result (normalize elim_fuel (App (build [] unit_family, Tt))));
  Printf.printf "  elimUnit C true tt by normal order: %s\n"
    (pp_eval_result (normalize elim_fuel (build [] (unit_elim NTt))));
  let g = unit_ctx in
  Printf.printf "  u : Unit ⊢ elimUnit C true u ⇓ Bool: %s\n"
    (pp_answer ~depth:4 ~names:(names g) (fun () -> "")
       (snd (run_check predicative elim_fuel (in_ctx g) (term_in g (unit_elim (NVar "u"))) Bool)));
  print_endline "  (no η for Unit: C u stays neutral and is not Bool)"

(* The PCF translation, run against the PCF evaluator. *)
let pcf_result t =
  match evalFuel pcf_fuel t with
  | Value (Tnum k) -> string_of_int k
  | Value _ -> "a value"
  | Timeout -> "no value within the fuel"
  | Stuck _ -> "stuck"

let demo_translation () =
  header "PCF → U⁻: programs, PCF evaluator, and the translation by normal order";
  print_endline "  Each translation is checked against ℕ by the U⁻ checker before it runs.";
  List.iter
    (fun ((name, t), expected) ->
      match translate_program_checked looping_fuel t with
      | Err (TrTargetRejected e) ->
          Printf.printf "  %s REJECTED BY THE U⁻ CHECKER: %s\n" (pad 36 name) (pp_error e)
      | Err (TrTargetUndecided _) ->
          Printf.printf "  %s U⁻ checker out of fuel\n" (pad 36 name)
      | Err _ -> Printf.printf "  %s NOT TRANSLATED\n" (pad 36 name)
      | Ok u ->
          let observed = observe (fuel_for expected) u in
          Printf.printf "  %s PCF %s  U⁻ %s %s %s\n" (pad 36 name)
            (pad 25 (pcf_result t))
            ": ℕ"
            (pad 31 (pp_observation observed))
            (match verdict_of expected observed with
             | Agrees -> "agrees"
             | NoResult -> "no result within the limit"
             | Contradicts -> "CONTRADICTS PCF"))
    pcf_cases;
  print_endline "  fact 4 = 24 takes about 1.4 million steps: make -C extraction slow"

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
  demo_looping ();
  demo_strictness ();
  demo_translation ();
  demo_choose ();
  demo_eliminators ()
