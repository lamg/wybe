module EvalExpressionTest

open Xunit
open GCL.Language
open GCL.Interpreter

let emptyCtx = { varValues = Map.empty }

let vEqOne = [ "v", Uint64 1UL ] |> Map.ofList
let onePlusTwo = Binary(Plus, Literal(Uint64 1UL), Literal(Uint64 2UL))
let vPlusTwo = Binary(Plus, Variable "v", Literal(Uint64 2UL))

[<Fact>]
let ``1 + 2`` () =
  let r = evaluate emptyCtx onePlusTwo
  Assert.Equal(Literal(Uint64 3UL), r)

[<Fact>]
let ``v + 2`` () =
  let ctx = { emptyCtx with varValues = vEqOne }

  let r = evaluate ctx vPlusTwo
  Assert.Equal(Literal(Uint64 3UL), r)

[<Fact>]
let ``x = 1 && y = x`` () =
  let xEq1 = Binary(Equal, Variable "x", Literal(Uint64 1UL))
  let xEqY = Binary(Equal, Variable "y", Variable "x")
  let yEq1 = Binary(Equal, Variable "y", Literal(Uint64 1UL))
  let expr = Binary(And, xEq1, Binary(And, xEqY, yEq1))

  let r = evaluate emptyCtx expr
  Assert.Equal(expr, r)

[<Fact>]
let ``x = 1 && x = y`` () =
  let xEq1 = Binary(Equal, Variable "x", Literal(Uint64 1UL))
  let xEqY = Binary(Equal, Variable "x", Variable "y")
  let expr = Binary(And, xEq1, xEqY)

  let ctx =
    { emptyCtx with
        varValues = [ "y", Uint64 2UL ] |> Map.ofList }

  let xEq2 = Binary(Equal, Variable "x", Literal(Uint64 2UL))
  let expected = Binary(And, xEq1, xEq2)
  let r = evaluate ctx expr

  Assert.Equal(expected, r)

[<Fact>]
let ``true = 1`` () =
  let l, r = Literal(Bool true), Literal(Uint64 1UL)
  let expr = Binary(Equal, l, r)

  try
    evaluate emptyCtx expr |> ignore
    Assert.Fail "should have raised an exception"
  with
  | EvalErrorEx(CannotApplyBinOp(Equal, Bool true, Uint64 1UL)) -> ()
  | e -> Assert.Fail e.Message
