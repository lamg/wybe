module GriesSchneider.Axioms

open TypedExpression
open Inference

let x, y, z = Var "x", Var "y", Var "z"

// x ≡ y  ⇒  f.x ≡ f.y
let ``≡ leibniz`` =
  let fx, fy = Var "fx", Var "fy"
  (x === y) ==> (fx === fy) |> law "≡ leibniz"


// (x ≡ y) ∧ (y ≡ z)  ⇒  (x ≡ z)
let ``≡ transitivity`` =
  ((x === y) <&&> (y === z)) ==> (x === z) |> law "≡ transitivity"

// x ≡ y ≡ y ≡ x
let ``≡ sym`` = (x === y) === (y === x) |> law "≡ sym"

// (x ≡ x) ≡ true
let ``≡ ident`` = (x === x) === True |> law "≡ ident"

// false ≡ ¬true
let ``false def`` = False === !True |> law "false def"

// ¬(x ≡ y) ≡ ¬x ≡ y
let ``¬ over ≡`` = !(x === y) === (!x === y) |> law "¬ over ≡"

// x ≢ y ≡ ¬(x ≡ y)
let ``≢ def`` = (x !== y) === !(x === y) |> law "≢ def"

// (x ≡ y) ≡ z  ≡  x ≡ (y ≡ z)
let ``≡ assoc`` =
  let lhs = (x === y) === z
  let rhs = x === (y === z)
  lhs === rhs |> law "≡ assoc"

let sym x =
  match x with
  | { expr = { node = n; subtrees = [ x; y ] }
      id = id } ->
    { expr = { node = n; subtrees = [ y; x ] }
      id = $"sym {id}" }

  | _ -> failwith $"no symmetric law for {x}"

let twice x = [ x; x ]
