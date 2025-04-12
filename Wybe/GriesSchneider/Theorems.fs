module GriesSchneider.Theorems

open CalculationCE
open Axioms
open TypedExpression

let ``true theorem`` () =
  let p, q = Var "p", Var "q"

  proof () {
    Theorem("true theorem", True)
    WithLaws [ ``≡ sym`` ]
    p === q === (q === p)

    ``≡`` {
      ``≡ sym``
      ``≡ ident``
    }

    True
  }


// GS = "A Logical Approach to Discrete Math, by David Gries and Fred B. Schneider"
let ``GS 3.11`` () =
  proof () {
    Theorem("GS 3.11", !x === y === (x === !y))
    withLaws { ``true theorem`` }

    !x === y === (x === !y)

    ``≡`` {
      sym ``¬ over ≡``
      ``≡ sym``
      sym ``¬ over ≡``
    }

    !(x === y) === !(y === x)

    ``≡`` {
      ``≡ sym``
      ``≡ ident``
    }

    True
  }

let ``double negation`` () =
  proof () {
    Theorem("double negation", !(!x) === x)
    withLaws { ``true theorem`` }
    !(!x) === x
    ``≡`` { ``GS 3.11`` }
    !x === !x
    ``≡`` { ``≡ ident`` }
    True
  }

let ``negation of false`` () =
  proof () {
    Theorem("negation of false", !False === True)
    withLaws { ``false def`` }
    !False === True

    ``≡`` {
      sym ``¬ over ≡``
      ``≡ sym``
    }

    !(True === False)

    ``≡`` {
      ``¬ over ≡``
      ``≡ sym``
    }

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
    withLaws { ``true theorem`` }
    x !== y === (y !== x)

    ``≡`` {
      ``≢ def``
      ``≢ def``
    }

    !(x === y) === !(y === x)

    ``≡`` {
      ``≡ sym``
      ``≡ ident``
    }

    True
  }


let ``associativity of ≢`` () =
  proof () {
    Theorem("associativity of ≢", x !== y !== z === (x !== (y !== z)))
    x !== y !== z

    ``≡`` {
      ``GS 3.14``
      ``symmetry of ≢``
      ``GS 3.14``
      ``≡ sym``
    }

    !x === y === !z
    ``≡`` { ``≡ assoc`` }
    !x === (y === !z)

    ``≡`` {
      sym ``GS 3.14``
      ``≡ sym``
      sym ``GS 3.14``
    }

    x !== (z !== y)
    ``≡`` { ``symmetry of ≢`` }
    x !== (y !== z)
  }

let ``mutual associativity`` () =
  proof () {
    Theorem("mutual associativity", x !== y === z === (x !== (y === z)))
    x !== y === z

    ``≡`` {
      ``GS 3.14``
      ``≡ assoc``
    }

    !x === (y === z)
    ``≡`` { sym ``GS 3.14`` }
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
    ``≡`` { sym ``≢ def`` }
    x === (y !== z)
  }

// GS 3.4 Disjunction

let ``∨ zero`` () =
  let excludedMiddle = eqLaws ``true theorem`` ``excluded middle``

  proof () {
    Theorem("∨ zero", x <||> True === True)
    x <||> True

    ``≡`` { excludedMiddle }

    x <||> (x <||> !x)

    ``≡`` {
      sym ``∨ assoc``
      ``∨ idempotency``
    }

    x <||> !x
    ``≡`` { sym excludedMiddle }
    True
  }

let ``∨ identity`` () =
  let assocSymEqIdent =
    proof () {
      Theorem("assoc sym ≡ ident", True === x === x)
      withLaws { ``≡ ident`` }
      x === x === True

      ``≡`` {
        ``≡ sym``
        sym ``≡ assoc``
      }

      True === x === x
    }

  proof () {
    Theorem("∨ identity", x <||> False === x)
    withLaws { ``excluded middle`` }
    x <||> False === x
    ``≡`` { sym ``∨ idempotency`` }
    x <||> False === (x <||> x)
    ``≡`` { sym ``∨ over ≡`` }
    x <||> (False === x)
    ``≡`` { ``false def`` }
    x <||> (!True === x)
    ``≡`` { sym ``¬ over ≡`` }
    x <||> !(True === x)
    ``≡`` { assocSymEqIdent }
    x <||> !x
  }

let ``∨ over ∨`` () =
  proof () {
    Theorem("∨ over ∨", x <||> (y <||> z) === (x <||> y <||> (x <||> z)))
    x <||> y <||> (x <||> z)
    ``≡`` { sym ``∨ assoc`` }
    x <||> y <||> x <||> z
    ``≡`` { ``∨ sym`` }
    y <||> x <||> x <||> z
    ``≡`` { ``∨ assoc`` }
    y <||> (x <||> x) <||> z
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
    ``≡`` { sym ``∨ over ≡`` }
    x <||> (y === !y)
    ``≡`` { ``≡ sym`` }
    x <||> (!y === y)
    ``≡`` { sym ``¬ over ≡`` }
    x <||> !(y === y)
    ``≡`` { ``≡ ident`` }
    x <||> !True
    ``≡`` { sym ``false def`` }
    x <||> False
    ``≡`` { ``∨ identity`` }
    x
  }
