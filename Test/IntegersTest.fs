module IntegerTests

open Xunit
open Core
open GriesSchneider

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
  [ n + m, "n + m"
    -n, "-n"
    n - m, "n - m"
    n * m, "n × m"
    n / m, "n ÷ m"
    IsDivisor(n, m), "n ∣ m"
    Exceeds(n, m), "n > m"
    AtLeast(n, m), "n ≥ m"
    LessThan(n, m), "n < m"
    AtMost(n, m), "n ≤ m" ]
  |> List.iter (fun (n, s) -> Assert.Equal(s, n.ToString()))
