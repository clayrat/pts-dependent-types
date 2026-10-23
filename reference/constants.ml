(* A signature written by hand, assembled independently, as
   theories/MLTT/Constants.v: ℕ with zero and succ, the instance elimNat[0]
   with active ι-rules, and the δ-constant
   double = λn. elimNat (λ_. Nat) zero (λ_ r. succ (succ r)) n. *)

open Looping
module P = Pts_native

let nat_desc = {
  P.ind_name = "Nat"; ind_params = []; ind_indices = []; ind_level = 0;
  ind_ctors = [
    { P.ctor_name = "zero"; ctor_fields = []; ctor_indices = [] };
    { P.ctor_name = "succ"; ctor_fields = [P.FRec ([], [])]; ctor_indices = [] };
  ];
}

let nat = Const (P.Const (P.Ind "Nat"))
let zero = Const (P.Const (P.Ctor ("Nat", "zero")))
let succ n = Apply (Const (P.Const (P.Ctor ("Nat", "succ"))), n)
let elim_nat = Const (P.Const (P.Elim ("Nat", 0)))
let double n = Apply (Const (P.Const (P.Def "double")), n)

let elim_nat_ty =
  pi "P" (arrow nat (Sort (P.Univ 0)))
    (arrows [Apply (name "P", zero);
             pi "n" nat (arrow (Apply (name "P", name "n")) (Apply (name "P", succ (name "n"))))]
       (pi "n" nat (Apply (name "P", name "n"))))

let const_nat = ann (abs ["_"] nat) (arrow nat (Sort (P.Univ 0)))
let elim_with step n = call elim_nat [const_nat; zero; step; n]
let double_body = abs ["n"] (elim_with (abs ["m"; "r"] (succ (succ (name "r")))) (name "n"))

(* Registered entry by entry, newest first; [sig_add] checks closedness.
   The base signature has ℕ and its eliminator: the body of [double] is
   checked there, before [double] is registered. *)
let add sg entry =
  match P.sig_add sg entry with Some sg -> sg | None -> invalid_arg "an entry is not closed"

let base_signature active =
  List.fold_left add P.empty_signature
    [P.EInd nat_desc; P.EElim ("Nat", 0, build [] elim_nat_ty, active)]

let signature active =
  add (base_signature active) (P.EDef ("double", build [] (arrow nat nat), build [] double_body))

(* The ι-rule on open terms: P z s n are free. *)
let iota_ctx =
  ["n", nat;
   "s", pi "n" nat (arrow (Apply (name "P", name "n")) (Apply (name "P", succ (name "n"))));
   "z", Apply (name "P", zero);
   "P", arrow nat (Sort (P.Univ 0))]
