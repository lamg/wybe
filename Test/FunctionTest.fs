module FunctionTest

open Xunit
open Core
open Inspect
open GriesSchneider.Functions
open GriesSchneider.Integers

[<Fact>]
let ``test fibonacci function`` () =
  let two = Integer 2

  proof {
    lemma (fib two = fib one + fib zero)

    fib two
    ``==`` { fibProp }
    fib one + fib zero
  }
  |> inspect
  |> ignore
//|> failIfNotProved

[<Fact>]
let ``test fibonacci invariant`` () =
  let i, a, b = mkIntVar "i", mkIntVar "a", mkIntVar "b"

  // a = fibonacci (i - 1) ∧ b = fibonacci i ⇒ a + b = fibonacci (i + 1)
  proof { lemma (a = fib (i - one) <&&> (b = fib i) ==> (a + b = fib (i + one))) }
  |> inspect
  |> calculationError
  |> print

[<Fact>]
let ``test factorial invariant`` () =
  // result = factorial i ⇒ result * i = factorial (i + 1)
  let i = mkIntVar "i"
  let result = mkIntVar "result"

  // result = factorial i ⇒ result * i = factorial (i + 1)
  proof { lemma (result = fact i ==> (result * i = fact (i + one))) }
  |> inspect
  |> calculationError
  |> print
