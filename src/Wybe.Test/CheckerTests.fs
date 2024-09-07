module Checker.Test.CheckerTests

open Xunit
open Checker
open Tree

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
let orOp = TypedOperator("∨", boolT)
let eqOp = TypedOperator("≡", boolT)

let op o x y : TypedExpr =
  Branch { value = o; children = [| x; y |] }

let andIdempotency =
  { name = "idempotency of ∧"
    freeVars = [ freeA ]
    lhs = op andOp a a
    rhs = a }

[<Fact>]
let ``full match a with x ∧ y`` () =
  let target = op andOp x y

  let expected = [ aIdent, target ]

  let r = matchByType a target
  Assert.Equal<Binding list>(expected, r)

  bindByTypeAtRoot { freeVars = [ freeA ]; expr = a } target
  |> _.free.conflicts
  |> Assert.Empty

[<Fact>]
let ``full match a ∧ b with (x ≡ y) ∧ (z ≡ w)`` () =
  let matcher = op andOp a b

  let xEqY = op eqOp x y
  let zEqW = op eqOp z w
  let target = op andOp xEqY zEqW

  let expectedBindings = [ aIdent, xEqY; bIdent, zEqW ]

  let rs = matchByType matcher target

  Assert.Equal<Binding list>(expectedBindings, rs)

  target
  |> bindByTypeAtRoot
    { freeVars = [ freeA; freeB ]
      expr = matcher }
  |> _.free.conflicts
  |> Assert.Empty

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

  let { valid = valid; conflicts = conflicts } = splitFreeConflicts free

  valid |> Assert.Empty
  Assert.Equal<Binding list>(expectedBindings, conflicts)
  splitNonFreeConflicts nonFree |> _.conflicts |> Assert.Empty

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
  let { conflicts = conflicts } = splitFreeConflicts free
  conflicts |> Assert.Empty
  splitNonFreeConflicts nonFree |> _.conflicts |> Assert.Empty

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
  splitFreeConflicts free |> _.conflicts |> Assert.Empty
  splitNonFreeConflicts nonFree |> _.conflicts |> Assert.NotEmpty

[<Fact>]
let ``rewrite `a ∧ a` with binding `a, x ∨ y` `` () =
  let xOrY = op orOp x y
  let target = op andOp a a

  [ [ aIdent, xOrY; aIdent, xOrY ], op andOp xOrY xOrY
    [ aIdent, z ], op andOp z z ]
  |> List.iter (fun (bindings, expected) ->
    let r = rewriteWith target bindings

    match diffTrees (expected, r) with
    | None -> ()
    | Some d -> Assert.Fail $"{exprToString expected}  ≠  {exprToString r}\n{d}")

[<Fact>]
let ``all roots`` () =
  let xEqY = op eqOp x y
  let target = op andOp z (op andOp xEqY xEqY)

  let expected =
    [ target, []
      z, [ 0 ]
      op andOp xEqY xEqY, [ 1 ]
      xEqY, [ 1; 0 ]
      x, [ 1; 0; 0 ]
      y, [ 1; 0; 1 ]
      xEqY, [ 1; 1 ]
      x, [ 1; 1; 0 ]
      y, [ 1; 1; 1 ] ]

  let xs = roots target |> Seq.toList
  // xs
  // |> Seq.iter (fun (r, path) ->
  //   printfn $"path {path}"
  //   printfn $"{printTree typedExprStringer r}")

  Assert.Equal<(TypedExpr * int list) list>(expected, xs)

[<Fact>]
let ``replace at path`` () =
  let xEqY = op eqOp x y
  let target = op andOp z (op andOp xEqY xEqY)

  let r = replaceAt target (z, [ 1 ])
  //printfn $"{printTree typedExprStringer r}"
  let expected = op andOp z z
  Assert.Equal<TypedExpr>(expected, r)

[<Fact>]
let ``transform z ∧ (x ≡ y) ∧ (x ≡ y)`` () =
  let xEqY = op eqOp x y
  let target = op andOp z (op andOp xEqY xEqY)

  let rs = transformations target andIdempotency |> Seq.toList

  Assert.NotEmpty rs

  let expected =
    [ { bindings = [ aIdent, xEqY; aIdent, xEqY ]
        transformResult = op andOp z xEqY } ]

  Assert.Equal<BindingsTR list>(expected, rs)

//  rs
//  |> Seq.iter (fun r ->
//  printfn $"{printBindings r.bindings}"
//
//
//  printfn $"{exprToString r.transformResult}")

[<Fact>]
let ``transformations sequence`` () =
  let andZ = op andOp z z
  let target = op andOp z andZ

  let r = transformationTree target [ andIdempotency; andIdempotency ]
  // printfn $"{printTree bindingsTrStringer r}"
  let a =
    { bindings = []
      transformResult = target },
    andIdempotency

  let b =
    { bindings = [ aIdent, z; aIdent, z ]
      transformResult = andZ },
    andIdempotency

  let c =
    { bindings = [ aIdent, z; aIdent, z ]
      transformResult = z }

  let expected =
    Branch
      { value = a

        children = [| Branch { value = b; children = [| Leaf c |] } |] }

  Assert.Equal<Tree<BindingsTR * Transformer, BindingsTR>>(expected, r)

[<Fact>]
let ``check expression and collect intermediate transformations`` () =
  let andZ = op andOp z z
  let target = op andOp z andZ
  let paths = checkExpression (target, z) [ andIdempotency; andIdempotency ]

  let a =
    { bindings = []
      transformResult = target },
    andIdempotency

  let b =
    { bindings = [ aIdent, z; aIdent, z ]
      transformResult = andZ },
    andIdempotency

  let c =
    { bindings = [ aIdent, z; aIdent, z ]
      transformResult = z }

  let expected = [ [ Left a; Left b; Right c ] ]

  // printfn $"{printTransformationChain expected}"
  // printfn $"{printTransformationChain paths}"
  // FIXME seq of children in expression vs list of children
  Assert.Equal<TransformPath list>(expected, paths)
