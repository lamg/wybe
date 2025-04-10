module GriesSchneider.Axioms

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

let sym (r: obj) =
  let symLaw =
    function
    | { expr = { node = n; subtrees = [ x; y ] }
        id = id } ->
      { expr = { node = n; subtrees = [ y; x ] }
        id = $"sym {id}" }

    | _ -> failwith $"no symmetric law for {x}"

  match r with
  | :? Result<CheckedCalculation, CalculationCE.CalcError> as r ->
    match r with
    | Ok x -> symLaw x.calculation.demonstrandum

    | Error e -> failwith $"cannot get symmetric, failed proof: {e}"
  | :? Law as x -> symLaw x
  | _ -> failwith $"cannot get symmetric, unsupported value {r}"


let twice x = [ x; x ]
