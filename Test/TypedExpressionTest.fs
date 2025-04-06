module TypedExpressionTest

open ExpressionMatch
open FsToolkit.ErrorHandling
open Xunit
open TypedExpression

[<RequireQualifiedAccess>]
type IntValue =
  | Int of int
  | Var of string

  interface ITypedExpr with
    member this.toTypedExpr() : TypingResult =
      (match this with
       | Int n ->
         { node =
             { symbol = Symbol.Fixed(n.ToString())
               signature = TypeId "int" }
           subtrees = [] }
       | Var s ->
         { node =
             { symbol = Symbol.Free s
               signature = TypeId "int" }
           subtrees = [] })
      |> Ok

let trueSymbol =
  { symbol = Fixed "true"
    signature = boolId }

let xSymbol =
  { symbol = Free "x"
    signature = boolId }

let trueExpr = { node = trueSymbol; subtrees = [] }

[<Fact>]
let ``check typed expression`` () =
  [ True :> ITypedExpr, Ok boolId
    Var "x" :> ITypedExpr, Ok boolId
    Not True :> ITypedExpr, Ok boolId
    And((Var "x"), True) :> ITypedExpr, Ok boolId ]
  |> List.iteri (fun i (expr, expected) ->
    let actual = expr.toTypedExpr () |> Result.map _.node.signature

    match expected, actual with
    | _, _ when expected = actual -> ()
    | _ ->
      DiffObject.diffAndPrint expected actual
      Assert.Fail $"failed at {i}")


[<Fact>]
let ``match typed expression`` () =
  [ And(Var "x", True) :> ITypedExpr, And(True, True) :> ITypedExpr, Ok [ xSymbol, trueExpr; trueSymbol, trueExpr ]
    Var "x" :> ITypedExpr, IntValue.Var "x" :> ITypedExpr, Ok [] ]
  |> List.iteri (fun i (matcher, target, expected) ->
    let r =
      result {
        let! matcher = matcher |> _.toTypedExpr()
        let! target = target |> _.toTypedExpr()
        return matchTree matchSymbol matcher target
      }

    if expected <> r then
      DiffObject.diffObjects expected r |> Array.iter (printfn "%s")
      Assert.Fail $"Failed case {i}")
