module InferenceTest

open System
open System.Diagnostics
open FSharpPlus
open Xunit
open FsUnit

open ExpressionMatch
open StepExpansion
open TypedExpression
open Inference
open GriesSchneider.Axioms

let equal (x: 'a) (y: 'a) = Assert.Equal<'a>(x, y)
let leibniz = makeLeibnizRule ``≡ leibniz`` |> Result.get

let getLeibnizRewriters (op: TypedSymbol) laws =
  laws
  |> Seq.collect (fun y -> [ leibniz ] |> List.choose (fun l -> l.apply(op, y).leibniz))

let limits =
  { maxAlternatives = 1
    maxAlternativeLength = 7 }

let timeFunction (f: unit -> 'a) : TimeSpan =
  let stopwatch = Stopwatch.StartNew()
  f () |> ignore
  stopwatch.Stop()
  stopwatch.Elapsed

let hintEquivSymbol =
  { symbol = Fixed "≡"
    signature = boolId }

[<Fact>]
let ``make leibniz from ≡-assoc `` () =
  let r = leibniz.apply (hintEquivSymbol, ``≡ assoc``)

  Assert.True r.leibniz.IsSome
  let lhs = getTypedExpr (x === y === z)
  let rhs = getTypedExpr (x === (y === z))

  Assert.Equal(lhs, r.leibniz.Value.lhs)
  Assert.Equal(rhs, r.leibniz.Value.rhs)

[<Fact>]
let ``apply rewriters and mark solution path`` () =
  let p, q = Var "p", Var "q"

  let rewriters = [ ``≡ sym``; ``≡ ident`` ] |> getLeibnizRewriters hintEquivSymbol

  let step0 =
    { expr = getTypedExpr (p === q === (q === p))
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
  let r = checkTransitivity transitivity steps |> Seq.last
  assert r.resultExpr.IsSome
  assert r.checkResult.errors.IsEmpty
  assert r.checkResult.warnings.IsEmpty
  let expected = p === q === (q === p) === True |> getTypedExpr

  Assert.Equal(expected, r.resultExpr.Value)

[<Fact>]
let ``generate additional rewriters from context laws and hint`` () =
  // this feature is important because it's common to use
  // a theorem that is not exactly as stated, but a symmetric
  // or associative rewrite of the original
  // explicitly writing beforehand those slightly different
  // versions would make the library bloated. Instead they
  // are generated at runtime.

  let ctx =
    { issues = []
      rules = [ leibniz ]
      contextLaws = [ ``≡ assoc``; ``≡ sym`` ] }

  let generated = seq { seq { ``≡ ident`` } }
  let rss = expandGeneratedLaws ctx hintEquivSymbol generated

  let lawSet = rss |> Seq.concat |> Set
  // are these all permutations of context laws applied with the original at the beginning?
  let expected =
    [ x === x === True
      x === (x === True) // `≡ assoc` applied to `≡ ident`
      x === (True === x) // `≡ assoc`, `≡ sym` applied to `≡ ident`
      True === (x === x) // `≡ sym` applied to `≡ ident`
      x === True === x ] // `≡ sym` applied to `≡ ident`
    |> List.map (fun x ->
      { id = ``≡ ident``.id
        expr = getTypedExpr x })
    |> Set

  Assert.Equal<Set<Law>>(lawSet, expected)

  let ctx = { ctx with contextLaws = [ ``≡ sym`` ] }

  let generated =
    seq {
      seq {
        ``≡ sym``
        ``≡ ident``
      }
    }

  let rss = expandGeneratedLaws ctx hintEquivSymbol generated

  // rss
  // |> Seq.iter (fun rs -> rs |> Seq.map (_.expr >> printTypedExpr) |> String.concat "," |> printfn "%s")

  let actual = rss |> Seq.map (Seq.map _.expr >> Seq.toList) |> Seq.toList

  let expected =
    [ [ x === y === (y === x); x === x === True ]
      [ x === y === (x === y); x === x === True ]
      [ y === x === (x === y); x === x === True ]
      [ y === x === (y === x); x === x === True ]
      [ x === y === (y === x); True === (x === x) ] ]
    |> List.map (fun xs -> xs |> List.map getTypedExpr)

  should equalSeq expected actual
