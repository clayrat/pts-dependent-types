(* Slow test: fact 4 through the PCF translation.  The translation is
   accepted by the U⁻ checker against ℕ, then run by normal order (about 1.4
   million steps); the source program is run by the PCF evaluator, and the
   two numbers must agree, and be 24.  Not part of the regular tests. *)
open Deptypes

let () =
  let program = Tapp (fact, Tnum 4) in
  let t0 = Sys.time () in
  let source =
    match evalFuel 10_000_000 program with
    | Value (Tnum k) -> Some k
    | _ -> None
  in
  Printf.printf "slow: fact 4 by the PCF evaluator: %s (%.1fs)\n%!"
    (match source with Some k -> string_of_int k | None -> "no value within the fuel")
    (Sys.time () -. t0);
  match translate_program_checked looping_fuel program with
  | Err _ -> print_endline "slow: fact 4 not translated or not accepted by the U⁻ checker"; exit 1
  | Ok u ->
      let t1 = Sys.time () in
      let observed = observe 2_000_000 u in
      Printf.printf "slow: fact 4, checked at ℕ in U⁻, by normal order: %s (%.1fs)\n%!"
        (Pretty.pp_observation observed) (Sys.time () -. t1);
      (match source, observed with
       | Some k, ObsNumeral j when k = j && k = 24 ->
           print_endline "slow: the translation agrees with the PCF evaluator"
       | _ -> print_endline "slow: the translation does not agree with PCF"; exit 1)
