module Z3Test

open Xunit
open FsUnit
open Core

[<Fact>]
let ``check implication`` () =
  let ctx = new Microsoft.Z3.Context()

  [ False, Refuted "false"; True ==> False, Refuted "false" ]
  |> List.iter (fun (pred, expected) ->
    let res = checkPredicate ctx pred
    should equal res expected)

[<Fact>]
let ``double negation with Z3`` () =
  let x, y = Var "x", Var "y"

  let ``GS 3.11`` = !x === y === (x === !y)
  let ``≡ ident`` = x === x === True

  let calcRes =
    proof () {
      Theorem("double negation", !(!x) === x)

      !(!x) === x
      ``≡`` { ``GS 3.11`` }
      !x === !x
      ``≡`` { ``≡ ident`` }
      True
    }

  Assert.True calcRes.error.IsNone
