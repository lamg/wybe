module WybeLangTest

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

[<Fact>]
let ``typing array literal and string representation`` () =
  [ Array [ Lit(Int 0); Lit(Int 1); Lit(Int 2) ], "[ 0, 1, 2 ]", Some(WybeType.Array WybeType.Integer), []
    Array [], "[]", None, []
    Array [ Lit(Bool true) ], "[ true ]", Some(WybeType.Array WybeType.Boolean), []
    Array [ Lit(Bool true); Lit(Int 1) ],
    "[ true, 1 ]",
    None,
    [ { expected = WybeType.Boolean
        got = Typed WybeType.Integer
        atChild = 1 } ] ]
  |> List.iter (fun (x, expectedString, expectedType, mismatchedTypes) ->
    let s = x |> exprToTree |> string

    shouldEqual expectedString s
    let r = extractSemantics Map.empty x
    Assert.True r.SemanticResult.Domain.IsNone
    shouldEqual expectedType r.SemanticResult.Type
    shouldEqual mismatchedTypes r.SemanticResult.MismatchedTypes)

[<Fact>]
let ``typing array element access`` () =
  let vars =
    [ "xs", WybeType.Array WybeType.Integer; "i", WybeType.Integer ] |> Map.ofList

  let indexExpr = Binary(Var "i", WybeOp.Plus, Lit(Int 1))
  let r = extractSemantics vars (ArrayElem("xs", indexExpr))

  shouldEqual (Some WybeType.Integer) r.SemanticResult.Type

  let expectedDomain =
    Binary(
      Binary(Lit(Int 0), WybeOp.AtMost, indexExpr),
      WybeOp.And,
      Binary(indexExpr, WybeOp.LessThan, Unary(WybeOp.Length, Var "xs"))
    )
    |> extractSemantics vars

  shouldEqual (Some expectedDomain) r.SemanticResult.Domain
