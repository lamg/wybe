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

    withLaws {
      ``true theorem``
      ``≡ sym``
    }

    !x === y === (x === !y)

    ``≡`` { ``¬ over ≡`` }

    !(x === y) === (x === !y)

    ``≡`` {
      ``≡ sym``
      ``¬ over ≡``
      ``≡ sym``
    }

    !(x === y) === !(x === y)
    ``≡`` { ``≡ ident`` }

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

    withLaws {
      ``false def``
      ``≡ sym``
    }

    !False === True

    ``≡`` {
      ``¬ over ≡``
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
  let secondHalf =
    proof () {
      Theorem("lemma for proving associativity of ≢ ", x !== (y !== z) === (x === (y === z)))
      withLaws { ``≡ sym`` }
      x !== (y !== z)
      ``≡`` { twice ``GS 3.14`` }
      !x === (!y === z)
      ``≡`` { twice ``¬ over ≡`` }
      !(x === !(y === z))

      ``≡`` {
        ``≡ sym``
        ``¬ over ≡``
      }

      !(!(y === z === x))

      ``≡`` {
        ``double negation``
        ``≡ sym``
      }

      x === (y === z)
    }

  proof () {
    Theorem("associativity of ≢", x !== y !== z === (x !== (y !== z)))
    withLaws { ``≡ sym`` }
    x !== y !== z

    ``≡`` { twice ``GS 3.14`` }

    !(!x === y) === z

    ``≡`` {
      ``¬ over ≡``
      ``double negation``
      ``≡ assoc``
    }

    x === (y === z)
    ``≡`` { secondHalf }
    x !== (y !== z)
  }

let ``mutual associativity`` () =
  proof () {
    Theorem("mutual associativity", x !== y === z === (x !== (y === z)))
    withLaws { ``≡ sym`` }
    x !== y === z

    ``≡`` {
      ``GS 3.14``
      ``≡ assoc``
    }

    !x === (y === z)
    ``≡`` { ``GS 3.14`` }
    x !== (y === z)
  }

let ``mutual interchangeability`` () =
  proof () {
    Theorem("mutual interchangeability", x !== y === z === (x === (y !== z)))
    withLaws { ``≡ sym`` }
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
  let excludedMiddle = eqLaws ``true theorem`` ``excluded middle``

  proof () {
    Theorem("∨ zero", x <||> True === True)
    withLaws { ``≡ sym`` }
    x <||> True

    ``≡`` { excludedMiddle }

    x <||> (x <||> !x)

    ``≡`` {
      ``∨ assoc``
      ``∨ idempotency``
    }

    x <||> !x
    ``≡`` { excludedMiddle }
    True
  }

let ``∨ identity`` () =
  proof () {
    Theorem("∨ identity", x <||> False === x)

    withLaws {
      ``excluded middle``
      ``≡ sym``
      ``≡ sym``
      ``≡ assoc``
    }

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
    withLaws { ``≡ sym`` }
    x <||> y <||> (x <||> z)
    ``≡`` { ``∨ assoc`` }
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
    withLaws { ``≡ sym`` }
    x <||> y === (x <||> !y)
    ``≡`` { ``∨ over ≡`` }
    x <||> (y === !y)
    ``≡`` { ``≡ sym`` }
    x <||> (!y === y)
    ``≡`` { ``¬ over ≡`` }
    x <||> !(y === y)
    ``≡`` { ``≡ ident`` }
    x <||> !True
    ``≡`` { ``false def`` }
    x <||> False
    ``≡`` { ``∨ identity`` }
    x
  }
