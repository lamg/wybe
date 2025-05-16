module GriesSchneider.Functions

open Core
open Integers

let declFib = Fn("fib", [ WInt; WInt ])
let fib (x: WExpr) = ExtInteger(App(declFib, [ x ]))

let fibProp =
  let n = mkIntVar "n"

  ``∀``
    [ n ]
    (n >= zero
     <&&> (fib n + fib (n + one) = fib (n + Integer 2))
     <&&> (fib zero = zero)
     <&&> (fib one = one))

let declFact = Fn("fact", [ WInt; WInt ])
let fact (x: WExpr) = ExtInteger(App(declFact, [ x ]))

let factProp =
  let n = mkIntVar "n"
  ``∀`` [ n ] (n >= zero <&&> (fact (n + one) = fact n * (n + one)) <&&> (fact zero = one))
