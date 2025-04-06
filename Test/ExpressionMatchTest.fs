module ExpressionMatchTest

open Xunit
open ExpressionMatch

type Predicate =
  | True
  | False
  | And
  | Or
  | Var of string

let opExp op x y = { node = op; subtrees = [ x; y ] }

let var x = { node = Var x; subtrees = [] }

let falseP = { node = False; subtrees = [] }
let trueP = { node = True; subtrees = [] }

let andVar x y = opExp And (var x) (var y)
let andExp x y = opExp And x y
let orExp x y = opExp Or x y
let orVar x y = opExp Or (var x) (var y)

let isPredicateMatch x y =
  match x, y with
  | Var _, _ -> true
  | _ -> x = y

[<Fact>]
let ``simple tree match`` () =
  let cases =
    [ var "x", trueP, [ Var "x", trueP ]
      var "x", var "y", [ Var "x", var "y" ]
      andVar "x" "y", orVar "x" "y", []
      trueP, var "x", []
      andVar "x" "y", andExp trueP falseP, [ Var "x", trueP; Var "y", falseP ]
      andVar "x" "x", andExp trueP falseP, [] ]

  cases
  |> List.iter (fun (pattern, target, expected) ->

    let r = matchTree isPredicateMatch pattern target

    Assert.Equal<(Predicate * Tree<Predicate>) list>(expected, r))

[<Fact>]
let ``simple tree rewrite`` () =
  let cases =
    [ [ Var "x", trueP ], andVar "x" "x", andExp trueP trueP
      [ Var "x", trueP; Var "y", falseP ], andVar "x" "y", andExp trueP falseP ]

  cases
  |> List.iter (fun (matches, rhs, expected) ->
    let r = rewrite matches rhs
    Assert.Equal(expected, r))

[<Fact>]
let ``choose rewrites`` () =
  let andIdempotency =
    { isNodeMatch = isPredicateMatch
      lhs = andVar "x" "x"
      rhs = var "x"
      id = "∧-idempotency" }

  let andTrueTrue = andExp trueP trueP
  let andxx = andVar "x" "x"

  let cases =
    [ andTrueTrue, [ trueP ]
      andExp andxx andTrueTrue, [ andExp (var "x") andTrueTrue; andExp andxx trueP ]
      andExp andxx andxx, [ andxx; andExp (var "x") andxx; andExp andxx (var "x") ] ]

  cases
  |> List.iter (fun (target, expected) ->
    let r = yieldRewrites andIdempotency target
    Assert.Equal<Tree<Predicate> list>(expected, r))

[<Fact>]
let ``check rewrite consistency`` () =
  // check there's no confusion between a bound and a free variables of the same name when doing
  // a rewrite
  // renaming rules
  // in  replacement  result
  // x            (x, y)       y
  // z            (x, y)       z                                    when z ≠ x
  // (t u)        (x, y)      (rename t (x,y)) (rename u (x,y))
  // (fun x -> t) (x, y)      (fun x -> t)
  // (fun y -> t) (x, y)      (fun x -> rename t (x,y))
  // (fun z -> t) (x, y)      (fun z -> rename t (x,y))             when z ≠ x and z ≠ y
  // in the context of Leibniz a = b ⇒ f.a = f.b
  // in an expression E, finding a match of `a` determines a surrounding context which is then
  // considered the definition of `f`
  // at that point the rules of lambda calculus
  // failwith "not implemented"
  ()
