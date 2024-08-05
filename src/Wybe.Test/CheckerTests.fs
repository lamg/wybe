module Checker.Test.CheckerTests

open Xunit
open Checker

let boolT = ResultType "bool"
let boolVar x = Leaf(Identifier x, boolT)
let freeA = Identifier "a", boolT
let freeB = Identifier "b", boolT
let a = boolVar "a"
let b = boolVar "b"

let x = boolVar "x"
let y = boolVar "y"
let z = boolVar "z"
let w = boolVar "w"
let andOp = TypedOperator("∧", boolT)
let eqOp = TypedOperator("≡", boolT)

let op o x y : TypedExpr =
  Branch { value = o; children = [ x; y ] }

[<Fact>]
let ``full match a with x ∧ y`` () =
  let target = op andOp x y

  let expected = [ fst freeA, target ]

  let r = matchByType a target
  Assert.Equal<Binding list>(expected, r)
  matchFree [freeA] a target |> Assert.True

[<Fact>]
let ``full match a ∧ b with (x ≡ y) ∧ (z ≡ w)`` () =
  let matcher = op andOp a b

  let xEqY = op eqOp x y
  let zEqW = op eqOp z w
  let target = op andOp xEqY zEqW

  let expectedBounds = [ fst freeA, xEqY; fst freeB, zEqW ]

  let rs = matchByType matcher target

  Assert.Equal<Binding list>(expectedBounds, rs)

  matchFree [ freeA; freeB ] matcher target |> Assert.True

[<Fact>]
let ``a ∧ a matches (x ≡ y) ∧ (z ≡ w) by type, but binding has conflicts`` () =
  let matcher = op andOp a a

  let xEqY = op eqOp x y
  let zEqW = op eqOp z w
  let target = op andOp xEqY zEqW

  let expectedBounds = [ fst freeA, xEqY; fst freeA, zEqW ]

  let rs = matchByType matcher target

  Assert.Equal<Binding list>(expectedBounds, rs)

  let free, nonFree = splitMatched [ freeA ] rs

  Assert.Equal<Binding list>([ fst freeA, xEqY; fst freeA, zEqW ], free)
  Assert.Empty nonFree

  okFree [ freeA ] free |> Assert.False
  okNonFree nonFree |> Assert.True
