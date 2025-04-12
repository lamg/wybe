module GriesSchneider.Axioms

open ExpressionMatch
open TypedExpression
open Inference

let x, y, z = Var "x", Var "y", Var "z"

// x ≡ y  ⇒  f.x ≡ f.y
let ``≡ leibniz`` =
  let fx, fy = Var "fx", Var "fy"
  x === y ==> (fx === fy) |> axiom "≡ leibniz"


// (x ≡ y) ∧ (y ≡ z)  ⇒  (x ≡ z)
let ``≡ transitivity`` =
  x === y <&&> (y === z) ==> (x === z) |> axiom "≡ transitivity"

// x ≡ y ≡ y ≡ x
let ``≡ sym`` = x === y === (y === x) |> axiom "≡ sym"

// (x ≡ x) ≡ true
let ``≡ ident`` = x === x === True |> axiom "≡ ident"

// false ≡ ¬true
let ``false def`` = False === !True |> axiom "false def"

// ¬(x ≡ y) ≡ ¬x ≡ y
let ``¬ over ≡`` = !(x === y) === (!x === y) |> axiom "¬ over ≡"

// x ≢ y ≡ ¬(x ≡ y)
let ``≢ def`` = x !== y === !(x === y) |> axiom "≢ def"

// (x ≡ y) ≡ z  ≡  x ≡ (y ≡ z)
let ``≡ assoc`` =
  let lhs = x === y === z
  let rhs = x === (y === z)
  lhs === rhs |> axiom "≡ assoc"

let rec extractLaw (x: obj) =
  match x with
  | :? (unit -> Result<CheckedCalculation, CalculationCE.CalcError>) as r -> r () |> extractLaw
  | :? Result<CheckedCalculation, CalculationCE.CalcError> as r ->
    match r with
    | Ok x -> x.calculation.demonstrandum
    | Error e -> failwith $"cannot get symmetric, failed proof: {e}"
  | :? Law as x -> x
  | _ -> failwith $"cannot get law, unsupported value {x}"

let sym (r: obj) =
  let symLaw =
    function
    | { expr = { node = n; subtrees = [ x; y ] }
        id = id } ->
      { expr = { node = n; subtrees = [ y; x ] }
        id = $"sym {id}" }

    | _ -> failwith $"no symmetric law for {x}"

  r |> extractLaw |> symLaw


let twice x = [ x; x ]

// GS 3.4 Disjunction
let ``∨ sym`` = x <||> y === (y <||> x) |> axiom "∨ sym"

let ``∨ assoc`` = x <||> y <||> z === (x <||> (y <||> z)) |> axiom "∨ assoc"

let ``∨ idempotency`` = x <||> x === x |> axiom "∨ idempotency"

let ``∨ over ≡`` =
  x <||> (y === z) === (x <||> y === (x <||> z)) |> axiom "∨ over ≡"

let ``excluded middle`` = x <||> !x |> axiom "excluded middle"

// any two laws are equivalent
let eqLaws th0 th1 =
  let l0 = extractLaw th0
  let l1 = extractLaw th1

  let expr =
    { node = { equivSymbol with signature = boolId }
      subtrees = [ l0.expr; l1.expr ] }

  { id = $"{l0.id} ≡ {l1.id}"
    expr = expr }
