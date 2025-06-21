module WybeTest

open Xunit
open FsUnitTyped
open LanguageServices.Wybe
open AST
open Semantics

[<Fact>]
let ``typing x div y`` () =
  let vars = [ "x", WybeType.Integer; "y", WybeType.Integer ] |> Map.ofList
  let divVars = Binary(Var "x", WybeOp.Div, Var "y")
  let r = extractSemantics vars divVars
  shouldEqual "x ÷ y" (r.Expr |> exprToTree |> string)
  shouldEqual (Some WybeType.Integer) r.SemanticResult.Type
  Assert.True r.SemanticResult.Domain.IsSome
  let domain = r.SemanticResult.Domain.Value
  shouldEqual (Some WybeType.Boolean) domain.SemanticResult.Type
  shouldEqual "y ≠ 0" (domain.Expr |> exprToTree |> string)


[<Fact>]
let ``failed typing x div y`` () =
  let vars = [ "x", WybeType.Integer; "y", WybeType.Boolean ] |> Map.ofList
  let divVars = Binary(Var "x", WybeOp.Div, Var "y")
  let r = extractSemantics vars divVars
  Assert.True r.SemanticResult.Domain.IsNone
  shouldEqual
    (Expecting
      [ { expected = WybeType.Integer
          got = Typed WybeType.Boolean
          atChild = 1 } ])
    r.SemanticResult
