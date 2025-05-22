module IntegerTests

open Xunit
open Core
open GriesSchneider.Integers

[<Fact>]
let ``check integer theorems`` () =
  [ ``× zero``
    ``+ cancellation``
    ``GS 15.23``
    ``GS 15.34``
    ``GS 15.35``
    monotonicity ]
  |> Inspect.findFailingProof
