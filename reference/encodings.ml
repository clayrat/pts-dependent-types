(* Church numerals in pure System U- and the strictness of PCF, assembled
   independently with the named builder of looping.ml.  The terms follow
   theories/SystemU/Encodings.v: the zero test is strict in the whole
   numeral (its step uses the result of the inner layer), the lazy test is
   kept as the counterexample, and the predecessor is Kleene's.  diff.ml
   compares the terms, their typing and their evaluation with the extract. *)

module P = Pts_native
open Looping

let c_nat = pi "X" star (arrows [arrow (name "X") (name "X"); name "X"] (name "X"))
let c_bool = pi "X" star (arrows [name "X"; name "X"] (name "X"))

let c_true = ann (abs ["X"; "a"; "b"] (name "a")) c_bool
let c_false = ann (abs ["X"; "a"; "b"] (name "b")) c_bool

let c_zero = ann (abs ["X"; "f"; "x"] (name "x")) c_nat
let c_succ =
  ann
    (abs ["n"; "X"; "f"; "x"]
       (call (name "f") [call (name "n") [name "X"; name "f"; name "x"]]))
    (arrow c_nat c_nat)

let numeral k =
  if k < 0 then invalid_arg "numeral: negative";
  let rec iter k = if k = 0 then name "x" else call (name "f") [iter (k - 1)] in
  ann (abs ["X"; "f"; "x"] (iter k)) c_nat

(* Kleene's predecessor through pairs of numerals. *)
let c_pair_ty = pi "X" star (arrow (arrows [c_nat; c_nat] (name "X")) (name "X"))
let c_pair =
  ann (abs ["a"; "b"; "X"; "k"] (call (name "k") [name "a"; name "b"]))
    (arrows [c_nat; c_nat] c_pair_ty)
let c_fst =
  ann (abs ["p"] (call (name "p") [c_nat; abs ["a"; "b"] (name "a")]))
    (arrow c_pair_ty c_nat)
let c_snd =
  ann (abs ["p"] (call (name "p") [c_nat; abs ["a"; "b"] (name "b")]))
    (arrow c_pair_ty c_nat)
let c_shift =
  ann
    (abs ["p"]
       (call c_pair [call c_snd [name "p"];
                     call c_succ [call c_snd [name "p"]]]))
    (arrow c_pair_ty c_pair_ty)
let c_pred =
  ann
    (abs ["n"]
       (call c_fst [call (name "n") [c_pair_ty; c_shift;
                                     call c_pair [c_zero; c_zero]]]))
    (arrow c_nat c_nat)

let is_zero =
  ann
    (abs ["n"]
       (call (name "n")
          [c_bool; abs ["r"] (call (name "r") [c_bool; c_false; c_false]); c_true]))
    (arrow c_nat c_bool)

let is_zero_lazy =
  ann
    (abs ["n"] (call (name "n") [c_bool; abs ["r"] c_false; c_true]))
    (arrow c_nat c_bool)

let ifz ty c a b = call is_zero [c; ty; a; b]
let ifz_lazy ty c a b = call is_zero_lazy [c; ty; a; b]

let omega_nat = call l0 [c_nat; abs ["x"] (name "x")]
let omega_fun = call l0 [arrow c_nat c_nat; abs ["g"] (name "g")]

let church t = build [] t

(* A numeral in normal form is λX f x. f^k x. *)
let decode_nat = function
  | P.Lam (P.Lam (P.Lam body)) ->
      let rec count = function
        | P.Var 0 -> Some 0
        | P.App (P.Var 1, u) -> Option.map succ (count u)
        | _ -> None
      in
      count body
  | _ -> None

let encodings_typed = [
  "true", c_true, c_bool; "false", c_false, c_bool;
  "zero", c_zero, c_nat; "succ", c_succ, arrow c_nat c_nat;
  "numeral 3", numeral 3, c_nat;
  "pair", c_pair, arrows [c_nat; c_nat] c_pair_ty;
  "fst", c_fst, arrow c_pair_ty c_nat; "snd", c_snd, arrow c_pair_ty c_nat;
  "shift", c_shift, arrow c_pair_ty c_pair_ty;
  "pred", c_pred, arrow c_nat c_nat;
  "is_zero", is_zero, arrow c_nat c_bool;
  "is_zero_lazy", is_zero_lazy, arrow c_nat c_bool;
  "Ω_ℕ", omega_nat, c_nat; "Ω_ℕ→ℕ", omega_fun, arrow c_nat c_nat;
  "ifz at ℕ → ℕ", ifz (arrow c_nat c_nat) c_zero c_succ c_pred, arrow c_nat c_nat;
]

(* [Some k]: the PCF program yields k; [None]: it diverges. *)
let strictness_cases = [
  "(λx:ℕ. 0) Ω", call (ann (abs ["x"] c_zero) (arrow c_nat c_nat)) [omega_nat], Some 0;
  "ifz (succ Ω) then 0 else 1", ifz c_nat (call c_succ [omega_nat]) c_zero (numeral 1), None;
  "ifz 0 then 7 else Ω", ifz c_nat c_zero (numeral 7) omega_nat, Some 7;
  "ifz 1 then Ω else 7", ifz c_nat (numeral 1) omega_nat (numeral 7), Some 7;
  "pred 0", call c_pred [c_zero], Some 0;
  "pred Ω", call c_pred [omega_nat], None;
  "ifz (pred (succ Ω)) then 0 else 1",
    ifz c_nat (call c_pred [call c_succ [omega_nat]]) c_zero (numeral 1), None;
  "succ Ω", call c_succ [omega_nat], None;
  "(ifz 0 then succ else pred) 5",
    call (ifz (arrow c_nat c_nat) c_zero c_succ c_pred) [numeral 5], Some 6;
  "(ifz 1 then succ else pred) 5",
    call (ifz (arrow c_nat c_nat) (numeral 1) c_succ c_pred) [numeral 5], Some 4;
  "(ifz (succ Ω) then succ else pred) 5",
    call (ifz (arrow c_nat c_nat) (call c_succ [omega_nat]) c_succ c_pred) [numeral 5], None;
  "(ifz 0 then succ else Ω_ℕ→ℕ) 5",
    call (ifz (arrow c_nat c_nat) c_zero c_succ omega_fun) [numeral 5], Some 6;
]
