module GriesSchneider.Axioms

open Z3

let x, y, z = Var "x", Var "y", Var "z"

// x ≡ y  ⇒  f.x ≡ f.y
let ``≡ leibniz`` () =
  let fx, fy = Var "fx", Var "fy"
  x === y ==> (fx === fy)


// (x ≡ y) ∧ (y ≡ z)  ⇒  (x ≡ z)
let ``≡ transitivity`` () =
  x === y <&&> (y === z) ==> (x === z) |> axiom "≡ transitivity"

// x ≡ y ≡ y ≡ x
let ``≡ sym`` () = x === y === (y === x) |> axiom "≡ sym"

// (x ≡ x) ≡ true
let ``≡ ident`` () = x === x === True |> axiom "≡ ident"

// false ≡ ¬true
let ``false def`` () = False === !True |> axiom "false def"

// ¬(x ≡ y) ≡ ¬x ≡ y
let ``¬ over ≡`` () =
  !(x === y) === (!x === y) |> axiom "¬ over ≡"

// x ≢ y ≡ ¬(x ≡ y)
let ``≢ def`` () = x !== y === !(x === y) |> axiom "≢ def"

// (x ≡ y) ≡ z  ≡  x ≡ (y ≡ z)
let ``≡ assoc`` () =
  let lhs = x === y === z
  let rhs = x === (y === z)
  lhs === rhs |> axiom "≡ assoc"

// GS 3.4 Disjunction
let ``∨ sym`` () =
  x <||> y === (y <||> x) |> axiom "∨ sym"

let ``∨ assoc`` () =
  x <||> y <||> z === (x <||> (y <||> z)) |> axiom "∨ assoc"

let ``∨ idempotency`` () = x <||> x === x |> axiom "∨ idempotency"

let ``∨ over ≡`` () =
  x <||> (y === z) === (x <||> y === (x <||> z)) |> axiom "∨ over ≡"

let ``excluded middle`` () = x <||> !x |> axiom "excluded middle"


let twice x = [ x; x ]

// GS 3.5

let ``golden rule`` () =
  x <&&> y === (x === y === (x <||> y)) |> axiom "golden rule"
