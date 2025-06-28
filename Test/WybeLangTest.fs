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

  let iDivJ = Binary(Var "i", Op.Div, Var "j")

  [ ArrayElem("xs", iDivJ), Some Type.Integer, "xs[ i ÷ j ]", "j ≠ 0 ∧ 0 ≤ i ÷ j ∧ i ÷ j < #xs"
    Binary(iDivJ, Op.Exceeds, Lit(Int 0)), Some Type.Boolean, "i ÷ j > 0", "j ≠ 0" ]
  |> List.iter (fun (expr, expectedType, representation, domain) ->
    let r = extractTypeAndDomain vars expr
    shouldEqual representation (r.Expr |> exprToTree |> string)
    shouldEqual expectedType r.SemanticResult.Type
    Assert.True(r.SemanticResult.Domain.IsSome, $"No domain at {representation}")
    let actualDomain = exprToTree r.SemanticResult.Domain.Value.Expr |> string

    shouldEqual domain actualDomain)

open GriesSchneider

let vars =
  [ "n", Type.Integer; "m", Type.Integer; "x", Type.Boolean; "y", Type.Boolean ]
  |> Map.ofList

[<Fact>]
let ``Expr to WExpr`` () =

  [ Binary(Expr.Var "n", Op.Plus, Expr.Var "m"), n + m :> Core.WExpr
    Binary(Expr.Var "x", Op.And, Expr.Var "y"), x <&&> y ]
  |> List.iter (fun (expr, expected) ->
    let e = extractTypeAndDomain vars expr
    let r = semanticExprToWExpr e
    shouldEqual expected r.Expr)

[<Fact>]
let ``wp assignment`` () =
  let nExceeds0 = n > zero

  [ "n", DomainWExpr(None, n + 1), nExceeds0, n + 1 > zero
    "n", DomainWExpr(Some(m != zero), n / m), nExceeds0, m != zero <&&> (n / m > zero) ]
  |> List.iter (fun (var, expr, postcondition, wp) ->
    let r = wpAssignment [ var, expr ] postcondition
    shouldEqual wp r)

[<Fact>]
let ``wp composition`` () =
  [ Becomes [ "n", DomainWExpr(None, n + 1) ], Becomes [ "n", DomainWExpr(None, n * 2) ], n > zero, (n + 1) * 2 > zero ]
  |> List.iter (fun (s, t, postcondition, expected) ->
    let wp = wpComposition (s, t) postcondition
    shouldEqual expected wp)

[<Fact>]
let ``wp alternative`` () =
  [ [ Guard(Core.Equals(n, zero), Becomes [ "n", DomainWExpr(None, n + 1) ])
      Guard(n > zero, Skip)
      Guard(n < zero, Becomes [ "n", DomainWExpr(None, n * -1) ]) ],
    n > zero,
    (n = zero <||> (n > zero) <||> (n < zero))
    <&&> (n = zero ==> (n + 1 > zero))
    <&&> (n > zero ==> (n > zero))
    <&&> (n < zero ==> (n * -1 > zero)) ]
  |> List.iter (fun (guards, postcondition, expected) ->
    let wp = wpAlternative guards postcondition
    shouldEqual $"{expected}" $"{wp}")

[<Fact>]
let ``wlp repetition`` () =
  [ [ Guard(n > zero, Becomes [ "n", DomainWExpr(None, n - 1) ]) ],
    n >= zero,
    (n > zero <&&> (n >= zero) ==> (n - 1 >= zero)) ]
  |> List.iter (fun (guards, postcondition, expected) ->
    let wp = wlpRepetition guards postcondition
    shouldEqual expected wp)

[<Fact>]
let ``ast to semantic block`` () =
  let m, n, zero = Expr.Var "m", Expr.Var "n", Lit(Int 0)
  let exceeds x y = Binary(x, Op.Exceeds, y)

  let diff x y = Binary(x, Op.Differs, y)

  let andOp x y = Binary(x, Op.And, y)
  let minus x y = Binary(x, Op.Minus, y)
  let equals x y = Binary(x, Op.Equals, y)
  let branch0 = AST.Guard(exceeds m n, AST.Becomes([ "m" ], [ minus m n ]))
  let branch1 = AST.Guard(exceeds n m, AST.Becomes([ "n" ], [ minus n m ]))

  let vars, errs, statement =
    [ VarDecl [ [ "m"; "n" ], Type.Integer ]
      AST.Assert(andOp (exceeds m zero) (exceeds n zero))
      AST.Do [ AST.Guard(diff m n, AST.If [ branch0; branch1 ]) ]
      AST.Assert(equals m n) ]
    |> astBlockToSemantic

  shouldBeEmpty errs
  shouldEqual (Map.ofList [ "m", Type.Integer; "n", Type.Integer ]) vars
  let m, n, zero = GriesSchneider.m, GriesSchneider.n, GriesSchneider.zero
  let assertMN = Assert(m > zero <&&> (n > zero))

  let ifBody =
    If
      [ Guard(m > n, Becomes [ "m", DomainWExpr(None, m - n) ])
        Guard(n > m, Becomes [ "n", DomainWExpr(None, n - m) ]) ]

  let doMeqN = Do [ Guard(m != n, ifBody) ]

  let expected = Compose(assertMN, Compose(doMeqN, Assert((m = n))))

  shouldEqual $"{expected}" $"{statement}"

[<Fact>]
let ``Euclid algorithm semantics`` () =
  let a, b = mkIntVar "a", mkIntVar "b"
  let originalVars = Becomes [ "n", DomainWExpr(None, a); "m", DomainWExpr(None, b) ]

  let ifBody =
    If
      [ Guard(m > n, Becomes [ "m", DomainWExpr(None, m - n) ])
        Guard(n > m, Becomes [ "n", DomainWExpr(None, n - m) ]) ]

  let doMeqN = Do [ Guard(m != n, ifBody) ]
  let initDo = Compose(originalVars, doMeqN)
  let r = wpStatement initDo (m = n <&&> (gcd m n = gcd a b))
  printfn $"r {r}"
