module GriesSchneider.Functions

open Core
open Integers

let fib (x: WExpr) =
  let declFib = Fn("fib", [ WInt; WInt ])
  ExtInteger(App(declFib, [ x ]))

let n = mkIntVar "n"
let fibProp = ``∀`` [ n ] (n >= zero <&&> (fib (n + 2) = fib n + fib (n + 1)))

let declFact = Fn("fact", [ WInt; WInt ])
let fact (x: WExpr) = ExtInteger(App(declFact, [ x ]))

let factProp =
  ``∀`` [ n ] (n >= zero <&&> (fact (n + 1) = fact n * (n + 1)) <&&> (fact zero = one))
