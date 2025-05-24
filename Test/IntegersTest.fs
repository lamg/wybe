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



[<Fact>]
let ``integer string representation`` () =
  [ x + y, "x + y"
    -x, "-x"
    x - y, "x - y"
    x * y, "x × y"
    x / y, "x ÷ y"
    IsDivisor(x, y), "x ∣ y"
    Exceeds(x, y), "x > y"
    AtLeast(x, y), "x ≥ y"
    LessThan(x, y), "x < y"
    AtMost(x, y), "x ≤ y" ]
  |> List.iter (fun (x, s) -> Assert.Equal(s, x.ToString()))
