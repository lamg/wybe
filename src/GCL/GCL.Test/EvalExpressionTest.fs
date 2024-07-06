module EvalExpressionTest

open Xunit
open GCL.Language
open GCL.Interpreter

let emptyCtx = {values = Map.empty; expr = Literal (Uint64 0UL); error = None}
let vEqOne = ["v", Uint64 1UL ] |> Map.ofList
let onePlusTwo = Binary(Plus, Literal (Uint64 1UL), Literal(Uint64 2UL))
let vPlusTwo = Binary(Plus, Variable "v", Literal(Uint64 2UL))

[<Fact>]
let ``1 + 2`` () =
  let ctx = { emptyCtx with expr = onePlusTwo }
  let r = evaluate ctx
  Assert.Equal(Literal (Uint64 3UL), r.expr)
  
[<Fact>]
let ``v + 2`` () =
  let ctx = { emptyCtx with expr = vPlusTwo; values = vEqOne }
  let r = evaluate ctx
  Assert.Equal(Literal (Uint64 3UL), r.expr)
