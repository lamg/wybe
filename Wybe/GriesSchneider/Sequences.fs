module GriesScheined.Sequences

open Core

let a s = ExtSeq(Var("a", s))
let b s = ExtSeq(Var("b", s))
let w sort = ExtSeq(Var("x", sort))
let x sort = ExtSeq(Var("x", sort))
let y sort = ExtSeq(Var("y", sort))
let z sort = ExtSeq(Var("y", sort))

let ``ϵ`` s = Empty s

let prepend s =
  Cons(a s, ``ϵ`` s) != ``ϵ`` s |> axiom "prepend"

let equality s =
  Cons(a s, x s) = Cons(b s, y s) === (a s = b s <&&> x s = y s)
  |> axiom "equality"

let ``GS 13.7`` (s: WSort) =
  proof { theorem "GS 13.7" (Cons(a s, x s) != x s) }
