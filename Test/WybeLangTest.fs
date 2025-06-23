module WybeLangTest

open Xunit
open FsUnitTyped
open LanguageServices.Wybe
open AST
open Semantics

[<Fact>]
let ``typing x div y`` () =
  let vars = [ "x", Type.Integer; "y", Type.Integer ] |> Map.ofList
  let divVars = Binary(Var "x", Op.Div, Var "y")
  let r = extractTypeAndDomain vars divVars
  shouldEqual "x ÷ y" (r.Expr |> exprToTree |> string)
  shouldEqual (Some Type.Integer) r.SemanticResult.Type
  Assert.True r.SemanticResult.Domain.IsSome
  let domain = r.SemanticResult.Domain.Value
  shouldEqual (Some Type.Boolean) domain.SemanticResult.Type
  shouldEqual "y ≠ 0" (domain.Expr |> exprToTree |> string)


[<Fact>]
let ``failed typing x div y`` () =
  let vars = [ "x", Type.Integer; "y", Type.Boolean ] |> Map.ofList
  let divVars = Binary(Var "x", Op.Div, Var "y")
  let r = extractTypeAndDomain vars divVars
  Assert.True r.SemanticResult.Domain.IsNone

  shouldEqual
    (Expecting
      [ { expected = Type.Integer
          got = Typed Type.Boolean
          atChild = 1 } ])
    r.SemanticResult

[<Fact>]
let ``typing array literal and string representation`` () =
  [ Array [ Lit(Int 0); Lit(Int 1); Lit(Int 2) ], "[ 0, 1, 2 ]", Some(Type.Array Type.Integer), []
    Array [], "[]", None, []
    Array [ Lit(Bool true) ], "[ true ]", Some(Type.Array Type.Boolean), []
    Array [ Lit(Bool true); Lit(Int 1) ],
    "[ true, 1 ]",
    None,
    [ { expected = Type.Boolean
        got = Typed Type.Integer
        atChild = 1 } ] ]
  |> List.iter (fun (x, expectedString, expectedType, mismatchedTypes) ->
    let s = x |> exprToTree |> string

    shouldEqual expectedString s
    let r = extractTypeAndDomain Map.empty x
    Assert.True r.SemanticResult.Domain.IsNone
    shouldEqual expectedType r.SemanticResult.Type
    shouldEqual mismatchedTypes r.SemanticResult.MismatchedTypes)

[<Fact>]
let ``typing array element access`` () =
  let vars = [ "xs", Type.Array Type.Integer; "i", Type.Integer ] |> Map.ofList

  let indexExpr = Binary(Var "i", Op.Plus, Lit(Int 1))
  let r = extractTypeAndDomain vars (ArrayElem("xs", indexExpr))

  shouldEqual (Some Type.Integer) r.SemanticResult.Type

  let expectedDomain =
    Binary(Binary(Lit(Int 0), Op.AtMost, indexExpr), Op.And, Binary(indexExpr, Op.LessThan, Unary(Op.Length, Var "xs")))
    |> extractTypeAndDomain vars

  shouldEqual (Some expectedDomain) r.SemanticResult.Domain

[<Fact>]
let ``domain conjunction`` () =
  let vars =
    [ "xs", Type.Array Type.Integer; "i", Type.Integer; "j", Type.Integer ]
    |> Map.ofList

  let indexExpr = Binary(Var "i", Op.Div, Var "j")
  let r = extractTypeAndDomain vars (ArrayElem("xs", indexExpr))
  shouldEqual "xs[ i ÷ j ]" (r.Expr |> exprToTree |> string)
  shouldEqual (Some Type.Integer) r.SemanticResult.Type

  let arrayDomain =
    Binary(Binary(Lit(Int 0), Op.AtMost, indexExpr), Op.And, Binary(indexExpr, Op.LessThan, Unary(Op.Length, Var "xs")))

  let divDomain = Binary(Var "j", Op.Differs, Lit(Int 0))

  let expectedDomain =
    Binary(divDomain, Op.And, arrayDomain)
    |> extractTypeAndDomain vars
    |> _.Expr
    |> exprToTree
    |> string

  shouldEqual "j ≠ 0 ∧ 0 ≤ i ÷ j ∧ i ÷ j < #xs" expectedDomain
  let actualDomain = exprToTree (r.SemanticResult.Domain.Value.Expr) |> string

  shouldEqual expectedDomain actualDomain

open GriesSchneider

[<Fact>]
let ``Expr to WExpr`` () =
  let x, y = mkBoolVar "x", mkBoolVar "y"
  let n, m = mkIntVar "n", mkIntVar "m"

  let vars =
    [ "n", Type.Integer; "m", Type.Integer; "x", Type.Boolean; "y", Type.Boolean ]
    |> Map.ofList

  [ Binary(Expr.Var "n", Op.Plus, Expr.Var "m"), n + m :> Core.WExpr
    Binary(Expr.Var "x", Op.And, Expr.Var "y"), x <&&> y ]
  |> List.iter (fun (expr, expected) ->
    let e = extractTypeAndDomain vars expr
    let r = semanticExprToWExpr e
    Assert.True(r.IsSome, $"{collectSemanticTreeInfo e}")
    shouldEqual expected r.Value.Expr)
