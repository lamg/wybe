module GriesSchneider.PredicateCalculus

open Core

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

let ``true theorem`` () =
  let p, q = Var "p", Var "q"

  proof () {
    Theorem("true theorem", True)
    p === q === (q === p)

    ``≡`` { ``≡ ident`` }

    True
  }


// GS = "A Logical Approach to Discrete Math, by David Gries and Fred B. Schneider"
let ``GS 3.11`` () =
  proof () {
    Theorem("GS 3.11", !x === y === (x === !y))

    !x === y === (x === !y)

    ``≡`` { ``¬ over ≡`` }

    !(x === y) === (x === !y)

    ``≡`` { ``¬ over ≡`` }

    !(x === y) === !(x === y)

    ``≡`` { ``≡ ident`` }

    True
  }

let ``double negation`` () =
  proof () {
    Theorem("double negation", !(!x) === x)
    !(!x) === x
    ``≡`` { ``GS 3.11`` }
    !x === !x
    ``≡`` { ``≡ ident`` }
    True
  }

let ``negation of false`` () =
  proof () {
    Theorem("negation of false", !False === True)

    !False === True

    ``≡`` { ``¬ over ≡`` }

    !(True === False)

    ``≡`` { ``¬ over ≡`` }

    False === !True
  }

let ``GS 3.14`` () =
  proof () {
    Theorem("GS 3.14", x !== y === (!x === y))
    x !== y
    ``≡`` { ``≢ def`` }
    !(x === y)
    ``≡`` { ``¬ over ≡`` }
    !x === y
  }


let ``symmetry of ≢`` () =
  proof () {
    Theorem("symmetry of ≢", x !== y === (y !== x))
    x !== y === (y !== x)

    ``≡`` {
      ``≢ def``
      ``≢ def``
    }

    !(x === y) === !(y === x)

    ``≡`` { ``≡ ident`` }

    True
  }


let ``associativity of ≢`` () =
  let secondHalf =
    proof () {
      Theorem("lemma for proving associativity of ≢ ", x !== (y !== z) === (x === (y === z)))
      x !== (y !== z)
      ``≡`` { twice ``GS 3.14`` }
      !x === (!y === z)
      ``≡`` { twice ``¬ over ≡`` }
      !(x === !(y === z))

      ``≡`` { ``¬ over ≡`` }

      !(!(y === z === x))

      ``≡`` { ``double negation`` }

      x === (y === z)
    }

  proof () {
    Theorem("associativity of ≢", x !== y !== z === (x !== (y !== z)))
    x !== y !== z

    ``≡`` { twice ``GS 3.14`` }

    !(!x === y) === z

    ``≡`` {
      ``¬ over ≡``
      ``double negation``
    }

    x === (y === z)
    ``≡`` { secondHalf }
    x !== (y !== z)
  }

let ``mutual associativity`` () =
  proof () {
    Theorem("mutual associativity", x !== y === z === (x !== (y === z)))
    x !== y === z

    ``≡`` { ``GS 3.14`` }

    !x === (y === z)
    ``≡`` { ``GS 3.14`` }
    x !== (y === z)
  }

let ``mutual interchangeability`` () =
  proof () {
    Theorem("mutual interchangeability", x !== y === z === (x === (y !== z)))
    x !== y === z

    ``≡`` {
      ``GS 3.14``
      ``≡ assoc``
    }

    !x === (y === z)
    ``≡`` { ``GS 3.11`` }
    x === !(y === z)
    ``≡`` { ``≢ def`` }
    x === (y !== z)
  }

// GS 3.4 Disjunction

let ``∨ zero`` () =

  proof () {
    Theorem("∨ zero", x <||> True === True)
    x <||> True

    ``≡`` { ``excluded middle`` }

    x <||> (x <||> !x)

    ``≡`` {
      ``∨ assoc``
      ``∨ idempotency``
    }

    x <||> !x
    ``≡`` { ``excluded middle`` }
    True
  }

let ``∨ identity`` () =
  proof () {
    Theorem("∨ identity", x <||> False === x)


    x <||> False === x
    ``≡`` { ``∨ idempotency`` }
    x <||> False === (x <||> x)
    ``≡`` { ``∨ over ≡`` }
    x <||> (False === x)
    ``≡`` { ``false def`` }
    x <||> (!True === x)
    ``≡`` { ``¬ over ≡`` }
    x <||> !(True === x)
    ``≡`` { ``≡ ident`` }
    x <||> !x
  }

let ``∨ over ∨`` () =
  proof () {
    Theorem("∨ over ∨", x <||> (y <||> z) === (x <||> y <||> (x <||> z)))
    x <||> y <||> x <||> z
    ``≡`` { ``∨ idempotency`` }
    y <||> x <||> z
    ``≡`` { ``∨ sym`` }
    x <||> y <||> z
    ``≡`` { ``∨ assoc`` }
    x <||> (y <||> z)
  }

let ``GS 3.32`` () =
  proof () {
    Theorem("GS 3.32", x <||> y === (x <||> !y) === x)
    x <||> y === (x <||> !y)
    ``≡`` { ``∨ over ≡`` }
    x <||> (y === !y)
    ``≡`` { ``¬ over ≡`` }
    x <||> !(y === y)
    ``≡`` { ``≡ ident`` }
    x <||> !True
    ``≡`` { ``false def`` }
    x <||> False
    ``≡`` { ``∨ identity`` }
    x
  }

// GS 3.5 conjuction

let ``∧ sym`` () =
  proof () {
    Theorem("∧ sym", x <&&> y === (y <&&> x))
    x <&&> y
    ``≡`` { ``golden rule`` }
    x === y === (x <||> y)

    ``≡`` { }

    y === x === (y <||> x)
    ``≡`` { ``golden rule`` }
    y <&&> x
  }

let ``∧ assoc`` () =
  proof () {
    Theorem("∧ assoc", x <&&> y <&&> z === (x <&&> (y <&&> z)))

    x <&&> y <&&> z
    ``≡`` { ``golden rule`` }
    x <&&> y === z === (x <&&> y <||> z)
    ``≡`` { twice ``golden rule`` }
    x === y === (x <||> y) === z === (x === y === (x <||> y) <||> z)

    ``≡`` { ``∨ over ≡`` }

    x
    === y
    === (x <||> y)
    === z
    === (z <||> x === (z <||> y) === (z <||> (x <||> y)))

    ``≡`` { }

    x
    === (y === z === (y <||> z))
    === (x <||> y === (x <||> z) === (x <||> (y <||> z)))

    ``≡`` {
      twice ``∨ over ≡``
      ``∨ over ≡``
    }

    x === (y === z === (y <||> z)) === (x <||> (y === z === (y <||> z)))

    ``≡`` { twice ``golden rule`` }

    x === (y <&&> z) === (x <||> (y <&&> z))

    ``≡`` { ``golden rule`` }

    x <&&> (y <&&> z)

  }
