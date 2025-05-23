module GriesSchneider.Sequences

open Core
open GriesSchneider.Integers

let mkSeqElem a = ExtSeq(Var(a, WVarSort "a"))
let mkSeq x = ExtSeq(Var(x, WSeq))

let a, b = mkSeqElem "a", mkSeqElem "b"

let w, x, y, z = mkSeq "w", mkSeq "x", mkSeq "y", mkSeq "z"

let ``ϵ`` = Empty

let prepend = Cons(a, ``ϵ``) != ``ϵ`` |> axiom "prepend"

let equality = Cons(a, x) = Cons(b, y) === (a = b <&&> (x = y)) |> axiom "equality"

let ``GS 13.7`` () =
  proof { theorem "GS 13.7" (Cons(a, x) != x) }


let ``length of ϵ`` = Length ``ϵ`` = zero |> axiom "length of ϵ"

let ``length of cons`` =
  ExtInteger(Length(Cons(a, x))) = one + ExtInteger(Length x)
  |> axiom "length of cons"

let ``length of concat`` () =
  proof { theorem "length of concat" (ExtInteger(Length(Concat(x, y))) = ExtInteger(Length x) + ExtInteger(Length y)) }
