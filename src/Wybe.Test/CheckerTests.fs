module Checker.Test.CheckerTests

open Xunit
open Checker

let boolT = ResultType "bool"
let boolVar x = Leaf(Identifier x, boolT)
let trueConst = boolVar "true"
let falseConst = boolVar "false"
let trueIdent = Identifier "true"
let falseIdent = Identifier "false"
let aIdent = Identifier "a"
let bIdent = Identifier "b"
let freeA = aIdent, boolT
let freeB = bIdent, boolT
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

  let expected = [ aIdent, target ]

  let r = matchByType a target
  Assert.Equal<Binding list>(expected, r)
  matchFree [ freeA ] a target |> Assert.True

[<Fact>]
let ``full match a ∧ b with (x ≡ y) ∧ (z ≡ w)`` () =
  let matcher = op andOp a b

  let xEqY = op eqOp x y
  let zEqW = op eqOp z w
  let target = op andOp xEqY zEqW

  let expectedBindings = [ aIdent, xEqY; bIdent, zEqW ]

  let rs = matchByType matcher target

  Assert.Equal<Binding list>(expectedBindings, rs)

  matchFree [ freeA; freeB ] matcher target |> Assert.True

[<Fact>]
let ``a ∧ a matches (x ≡ y) ∧ (z ≡ w) by type, but binding has conflicts`` () =
  let matcher = op andOp a a

  let xEqY = op eqOp x y
  let zEqW = op eqOp z w
  let target = op andOp xEqY zEqW

  let expectedBindings = [ aIdent, xEqY; aIdent, zEqW ]

  let rs = matchByType matcher target

  Assert.Equal<Binding list>(expectedBindings, rs)

  let free, nonFree = splitMatched [ freeA ] rs

  Assert.Equal<Binding list>([ aIdent, xEqY; aIdent, zEqW ], free)
  Assert.Empty nonFree

  okFree [ freeA ] free |> Assert.False
  okNonFree nonFree |> Assert.True

[<Fact>]
let ``full match a ∧ true with x ∧ true`` () =
  let matcher = op andOp a trueConst
  let target = op andOp x trueConst
  let expectedBindings = [ aIdent, x; trueIdent, trueConst ]
  let rs = matchByType matcher target
  Assert.Equal<Binding list>(expectedBindings, rs)

  let free, nonFree = splitMatched [ freeA ] rs
  Assert.Equal<Binding list>([ aIdent, x ], free)
  Assert.Equal<Binding list>([ trueIdent, trueConst ], nonFree)
  okFree [ freeA ] free |> Assert.True
  okNonFree nonFree |> Assert.True

[<Fact>]
let ``a ∧ true matches x ∧ false, but binding has a conflict in true ≔ false`` () =
  let matcher = op andOp a trueConst
  let target = op andOp x falseConst
  let expectedBindings = [ aIdent, x; trueIdent, falseConst ]
  let rs = matchByType matcher target
  Assert.Equal<Binding list>(expectedBindings, rs)

  let free, nonFree = splitMatched [ freeA ] rs
  Assert.Equal<Binding list>([ aIdent, x ], free)
  Assert.Equal<Binding list>([ trueIdent, falseConst ], nonFree)
  okFree [ freeA ] free |> Assert.True
  okNonFree nonFree |> Assert.False
