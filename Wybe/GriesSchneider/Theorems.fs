module GriesSchneider.Theorems

open Z3
open Axioms

let ``true theorem`` () =
  let p, q = Var "p", Var "q"

  proof () {
    Theorem("true theorem", True)
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

// GS 3.5 conjuction

let ``∧ sym`` () =
  proof () {
    Theorem("∧ sym", x <&&> y === (y <&&> x))
    x <&&> y
    ``≡`` { ``golden rule`` }
    x === y === (x <||> y)

    ``≡`` {
      ``≡ sym``
      ``∨ sym``
    }

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

    ``≡`` { ``∨ sym`` }

    x === y === (x <||> y) === z === (z <||> (x === y === (x <||> y)))


    ``≡`` {
      twice ``∨ over ≡``
      ``∨ over ≡``
    }

    x
    === y
    === (x <||> y)
    === z
    === (z <||> x === (z <||> y) === (z <||> (x <||> y)))

    ``≡`` {
      ``≡ assoc``
      ``≡ sym``
    }

    x
    === y
    === (z === (x <||> y))
    === (z <||> x === (z <||> y) === (z <||> (x <||> y)))

    ``≡`` { ``≡ assoc`` }

    (x === y === z === (x <||> y))
    === (z <||> x === (z <||> y) === (z <||> (x <||> y)))


    ``≡`` { ``≡ assoc`` }


    (x === y === z)
    === ((x <||> y) === (z <||> x === (z <||> y) === (z <||> (x <||> y))))

    ``≡`` { twice ``∨ sym`` }

    (x === y === z)
    === ((x <||> y) === (x <||> z === (y <||> z) === (z <||> (x <||> y))))

    ``≡`` { ``≡ sym`` }

    (x === y === z)
    === ((x <||> y) === (y <||> z === (x <||> z) === (z <||> (x <||> y))))


    ``≡`` { ``≡ assoc`` }

    (x === y === z)
    === ((x <||> y) === (y <||> z === ((x <||> z) === (z <||> (x <||> y)))))

    ``≡`` { ``≡ assoc`` }

    (x === y === z)
    === ((x <||> y) === (y <||> z) === (((x <||> z) === (z <||> (x <||> y)))))

    ``≡`` { ``≡ sym`` }

    (x === y === z)
    === ((y <||> z) === (x <||> y) === (((x <||> z) === (z <||> (x <||> y)))))

    ``≡`` { ``≡ assoc`` }

    (x === y === z)
    === ((y <||> z) === ((x <||> y) === (((x <||> z) === (z <||> (x <||> y))))))

    ``≡`` { ``≡ assoc`` }

    (x === y === z)
    === (y <||> z)
    === (((x <||> y) === (((x <||> z) === (z <||> (x <||> y))))))

    ``≡`` { twice ``≡ assoc`` }

    x
    === (y === z === (y <||> z))
    === (x <||> y === (x <||> z === (z <||> (x <||> y))))

    ``≡`` { ``≡ assoc`` }

    x
    === (y === z === (y <||> z))
    === (x <||> y === (x <||> z) === (z <||> (x <||> y)))

    ``≡`` { ``∨ sym`` }

    x
    === (y === z === (y <||> z))
    === (x <||> y === (x <||> z) === (z <||> (y <||> x)))

    ``≡`` { ``∨ assoc`` }

    x
    === (y === z === (y <||> z))
    === (x <||> y === (x <||> z) === ((z <||> y) <||> x))

    ``≡`` { twice ``∨ sym`` }

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
