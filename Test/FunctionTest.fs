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
  |> failIfNotProved

[<Fact>]
let ``test fibonacci invariant`` () =
  let i, a, b = mkIntVar "i", mkIntVar "a", mkIntVar "b"

  // a = fibonacci (i - 1) ∧ b = fibonacci i ⇒ a + b = fibonacci (i + 1)
  // TODO shouldn't this proof fail because there's no i > 0 restriction?
  proof {
    lemma ((a = fib (i - 1)) <&&> (b = fib i) ==> (a + b = fib (i + 1)))
    a = fib (i - 1) <&&> (b = fib i)
    ``⇒`` { fibProp }
    a + b = fib (i + 1)
  }
  |> inspect
  |> failIfNotProved

[<Fact>]
let ``test factorial invariant`` () =
  let i = mkIntVar "i"
  let result = mkIntVar "result"

  proof {
    lemma (result = fact i ==> (result * i = fact (i + one)))
    result = fact i
    ``⇒`` { factProp }
    result * i = fact (i + 1)
  }
  |> inspect
  |> failIfNotProved

[<Fact>]
let ``print functions`` () =
  let ackermann (x, y) =
    let decl = Fn("ackermann", [ WInt; WInt; WInt ])
    ExtInteger(App(decl, [ x; y ]))

  [ fib zero, "fib(0)"
    fib (n + 1), "fib(n + 1)"
    ackermann (zero, zero), "ackermann(0, 0)"
    ackermann (n + 1, n + 1), "ackermann(n + 1, n + 1)" ]
  |> List.iter (fun (f, r) -> Assert.Equal(f.ToString(), r))
