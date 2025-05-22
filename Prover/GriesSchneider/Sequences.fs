module GriesSchneider.Sequences

open Core

let a = ExtSeq(Var("a", WVarSort "a"))
let b = ExtSeq(Var("b", WVarSort "a"))
let w = ExtSeq(Var("x", WSeq))
let x = ExtSeq(Var("x", WSeq))
let y = ExtSeq(Var("y", WSeq))
let z = ExtSeq(Var("y", WSeq))

let ``ϵ`` = Empty

let prepend = Cons(a, ``ϵ``) != ``ϵ`` |> axiom "prepend"

let equality = Cons(a, x) = Cons(b, y) === (a = b <&&> (x = y)) |> axiom "equality"

let ``GS 13.7`` () =
  proof { theorem "GS 13.7" (Cons(a, x) != x) }
