module SequenceTest

open Xunit
open GriesSchneider.Sequences

[<Fact>]
let ``check all theorems`` () =
  Inspect.findFailingProof [ ``GS 13.7`` ]
