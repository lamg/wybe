module Z3Test

open Xunit
open FsUnit
open Core
open GriesSchneider


[<Fact>]
let ``check implication`` () =
  let ctx = new Microsoft.Z3.Context()

  [ False, CheckResult.Refuted "false"
    True ==> False, CheckResult.Refuted "false" ]
  |> List.iter (fun (pred, expected) ->
    let res = checkAssuming ctx [] pred
    should equal res expected)

[<Fact>]
let ``double negation with Z3`` () =
  let ``GS 3.11`` = !x === y === (x === !y)
  let ``≡ ident`` = x === x === True

  let calcRes =
    proof {
      theorem "double negation" (!(!x) === x)

      !(!x) === x
      ``≡`` { ``GS 3.11`` }
      !x === !x
      ``≡`` { ``≡ ident`` }
      True
    }

  Assert.True calcRes.Error.IsNone


[<Fact>]
let ``simple integer proof`` () =
  let x = mkIntVar "x"

  proof {
    lemma (x + x + x = Integer 3 * x)
    x + x + x
    ``==`` { }
    Integer 2 * x + x
    ``==`` { }
    Integer 3 * x
  }
  |> Inspect.inspect
  |> Inspect.summary
  |> ignore
