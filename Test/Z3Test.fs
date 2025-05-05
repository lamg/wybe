module Z3Test

open Xunit
open FsUnit
open Core

let x, y, z = Bool(Var "x"), Bool(Var "y"), Bool(Var "z")
let True = Bool True
let False = Bool False


[<Fact>]
let ``check implication`` () =
  let ctx = new Microsoft.Z3.Context()

  [ False, Refuted "false"; True ==> False, Refuted "false" ]
  |> List.iter (fun (pred, expected) ->
    let res = checkPredicate ctx pred
    should equal res expected)

[<Fact>]
let ``double negation with Z3`` () =
  let ``GS 3.11`` = !x === y === (x === !y)
  let ``≡ ident`` = x === x === True

  let calcRes =
    proof {
      Theorem("double negation", !(!x) === x)

      !(!x) === x
      ``≡`` { ``GS 3.11`` }
      !x === !x
      ``≡`` { ``≡ ident`` }
      True
    }

  Assert.True calcRes.error.IsNone
