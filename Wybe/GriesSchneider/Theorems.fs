module GriesSchneider.Theorems

open CalculationCE
open Axioms
open TypedExpression

let trueTheorem =
  let p, q = Var "p", Var "q"

  proof () {
    Theorem("True", True)
    WithLaws [ ``≡ sym`` ]
    (p === q) === (q === p)

    ``≡`` {
      ``≡ sym``
      ``≡ ident``
    }

    True
  }


// GS = "A Logical Approach to Discrete Math, by David Gries and Fred B. Schneider"
let ``GS 3.11`` =
  proof () {
    Theorem("GS 3.11", (!x === y) === (x === !y))
    WithLaws [ trueTheorem ]

    (!x === y) === (x === !y)

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

let ``double negation`` =
  proof () {
    Theorem("double negation", !(!x) === x)
    WithLaws [ trueTheorem ]
    !(!x) === x
    ``≡`` { ``GS 3.11`` }
    !x === !x
    ``≡`` { ``≡ ident`` }
    True
  }

let ``negation of false`` =
  proof () {
    Theorem("negation of false", !False === True)
    WithLaws [ ``false def`` ]
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

let ``GS 3.14`` =
  proof () {
    Theorem("GS 3.14", (x !== y) === (!x === y))
    x !== y
    ``≡`` { ``≢ def`` }
    !(x === y)
    ``≡`` { ``¬ over ≡`` }
    !x === y
  }


let ``symmetry of ≢`` =
  proof () {
    Theorem("symmetry of ≢", (x !== y) === (y !== x))
    WithLaws [ trueTheorem ]
    (x !== y) === (y !== x)

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


let ``associativity of ≢`` =
  proof () {
    Theorem("associativity of ≢", ((x !== y) !== z) === (x !== (y !== z)))
    (x !== y) !== z

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

let ``mutual associativity`` =
  proof () {
    Theorem("mutual associativity", ((x !== y) === z) === (x !== (y === z)))
    (x !== y) === z

    ``≡`` {
      ``GS 3.14``
      ``≡ assoc``
    }

    !x === (y === z)
    ``≡`` { sym ``GS 3.14`` }
    x !== (y === z)
  }

let ``mutual interchangeability`` =
  proof () {
    Theorem("mutual interchangeability", ((x !== y) === z) === (x === (y !== z)))
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
