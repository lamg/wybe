module PredicateCalculusTest

open Xunit
open GriesSchneider
open Inspect

[<Fact>]
let ``check all theorems`` () =
  [ ``associativity of ≢``
    ``double negation``
    ``GS 3.11``
    ``GS 3.14``
    ``mutual associativity``
    ``mutual interchangeability``
    ``negation of false``
    ``symmetry of ≢``
    ``true theorem``
    ``∨ zero``
    ``∨ identity``
    ``∨ over ∨``
    ``GS 3.32``
    ``∧ assoc``
    ``∧ idempotency``
    ``∧ zero``
    ``∧ over ∧``
    contradiction
    ``∧ ∨ absorption``
    ``∨ ∧ absorption`` ]
  |> findFailingProof
