(* Conversions between the syntax of the native reference and the Rocq
   extract: terms, sorts and constant names both ways; descriptions,
   signature entries, errors, events, answers and evaluation results from
   the native side, for comparison with the extract.  Shared by [diff.ml]
   and by the differential tests of the lectures built on this kernel. *)

module X = Deptypes
module N = Pts_native

let sort_of_extracted = function
  | X.Star -> N.Star | X.Box -> N.Box | X.Tri -> N.Tri | X.Univ i -> N.Univ i

let sort_to_extracted = function
  | N.Star -> X.Star | N.Box -> X.Box | N.Tri -> X.Tri | N.Univ i -> X.Univ i

let gref_of_extracted = function
  | X.Ind d -> N.Ind d | X.Ctor (d, c) -> N.Ctor (d, c)
  | X.Elim (d, j) -> N.Elim (d, j) | X.Def f -> N.Def f

let gref_to_extracted = function
  | N.Ind d -> X.Ind d | N.Ctor (d, c) -> X.Ctor (d, c)
  | N.Elim (d, j) -> X.Elim (d, j) | N.Def f -> X.Def f

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
  | X.Sigma (a, b) -> N.Sigma (term_of_extracted a, term_of_extracted b)
  | X.Pair (a, b) -> N.Pair (term_of_extracted a, term_of_extracted b)
  | X.Fst p -> N.Fst (term_of_extracted p)
  | X.Snd p -> N.Snd (term_of_extracted p)
  | X.Const g -> N.Const (gref_of_extracted g)

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
  | N.Sigma (a, b) -> X.Sigma (term_to_extracted a, term_to_extracted b)
  | N.Pair (a, b) -> X.Pair (term_to_extracted a, term_to_extracted b)
  | N.Fst p -> X.Fst (term_to_extracted p)
  | N.Snd p -> X.Snd (term_to_extracted p)
  | N.Const g -> X.Const (gref_to_extracted g)

let field_to_extracted = function
  | N.FArg a -> X.FArg (term_to_extracted a)
  | N.FRec (domains, indices) ->
      X.FRec (List.map term_to_extracted domains, List.map term_to_extracted indices)

let ctor_to_extracted c = {
  X.ctor_name = c.N.ctor_name;
  ctor_fields = List.map field_to_extracted c.N.ctor_fields;
  ctor_indices = List.map term_to_extracted c.N.ctor_indices }

let desc_to_extracted d = {
  X.ind_name = d.N.ind_name;
  ind_params = List.map term_to_extracted d.N.ind_params;
  ind_indices = List.map term_to_extracted d.N.ind_indices;
  ind_level = d.N.ind_level;
  ind_ctors = List.map ctor_to_extracted d.N.ind_ctors }

let entry_to_extracted = function
  | N.EInd d -> X.EInd (desc_to_extracted d)
  | N.EElim (d, j, ty, active) -> X.EElim (d, j, term_to_extracted ty, active)
  | N.EDef (f, ty, body) -> X.EDef (f, term_to_extracted ty, term_to_extracted body)

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
  | N.ENoSigmaRule (t, a, b) ->
      X.ENoSigmaRule (term_to_extracted t, sort_to_extracted a, sort_to_extracted b)
  | N.ENotASigma (t, ty) -> X.ENotASigma (term_to_extracted t, term_to_extracted ty)
  | N.ENoDecls t -> X.ENoDecls (term_to_extracted t)
  | N.EUnknownConst g -> X.EUnknownConst (gref_to_extracted g)

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
  | N.EvSigmaRule (a, b, c) ->
      X.EvSigmaRule (sort_to_extracted a, sort_to_extracted b, sort_to_extracted c)
  | N.EvUnfoldSigma (t, ty, a, b) ->
      X.EvUnfoldSigma (term_to_extracted t, term_to_extracted ty,
                       term_to_extracted a, term_to_extracted b)

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
