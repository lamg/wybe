module InferenceTest

open System
open System.Diagnostics
open FSharpPlus
open Xunit

open ExpressionMatch
open StepExpansion
open TypedExpression
open Inference
open GriesSchneider.Axioms

let equal (x: 'a) (y: 'a) = Assert.Equal<'a>(x, y)

let getLeibnizRewriters (op: TypedSymbol) laws =
  let leibniz = [ makeLeibnizRule ``≡ leibniz`` |> Result.get ]
  laws |> List.collect (fun y -> leibniz |> List.choose (fun l -> l op y))

let limits =
  { maxAlternatives = 1
    maxAlternativeLength = 7 }

let timeFunction (f: unit -> 'a) : TimeSpan =
  let stopwatch = Stopwatch.StartNew()
  f () |> ignore
  stopwatch.Stop()
  stopwatch.Elapsed

[<Fact>]
let ``make leibniz from ≡-assoc `` () =
  let r =
    makeLeibnizRule ``≡ leibniz``
    |> Result.get
    |> (fun f -> f equivSymbol ``≡ assoc``)

  Assert.True r.IsSome
  let lhs = getTypedExpr ((x === y) === z)
  let rhs = getTypedExpr (x === (y === z))

  Assert.Equal(lhs, r.Value.lhs)
  Assert.Equal(rhs, r.Value.rhs)

[<Fact>]
let ``count fits of a matcher expression in a target`` () =
  let p, q = Var "p", Var "q"

  [ (p === q) === (q === p), (x === y) === z, 1
    (p === q) === (q === p), x === x, 2 ]
  |> List.iter (fun (target, matcher, expected) ->
    let m = getTypedExpr matcher
    let t = getTypedExpr target
    countFits m t |> equal expected)


[<Fact>]
let ``apply rewriters and mark path to solution`` () =
  let p, q = Var "p", Var "q"

  let rewriters =
    [ ``≡ assoc``; sym ``≡ assoc``; ``≡ sym``; ``≡ ident`` ]
    |> getLeibnizRewriters equivSymbol

  let step0 =
    { expr = getTypedExpr ((p === q) === (q === p))
      rewriters = [ rewriters ]
      limits = limits }

  let step1 =
    { expr = getTypedExpr True
      rewriters = []
      limits = limits }

  let res = applyRewritersAndMarkPathToSolution [| step0; step1 |]

  Assert.True (Seq.head res[0]).expansion.node.path.IsSome

[<Fact>]
let ``transitive reduction`` () =
  let p, q = Var "p", Var "q"

  let steps =
    [| p === q === (q === p), Some equivSymbol; True, None |]
    |> Array.map (fun (p, op) ->
      { step =
          { expr = getTypedExpr p
            rewriters = []
            limits = limits }
        op = op })

  let transitivity = [ makeTransitivityRule ``≡ transitivity`` |> Result.get ]
  let ok, (n, s) = transitiveReduction transitivity steps
  let expected = p === q === (q === p) === True |> getTypedExpr

  Assert.Equal(expected, s)
  Assert.True ok
  Assert.Equal(0, n)
