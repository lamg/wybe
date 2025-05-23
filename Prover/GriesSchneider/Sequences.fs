module GriesSchneider.Sequences

open Core
open GriesSchneider.Integers

let mkSeqElem a = ExtSeq(Var(a, WVarSort "a"))
let mkSeq x = ExtSeq(Var(x, WSeq))

let a, b = mkSeqElem "a", mkSeqElem "b"

let w, x, y, z = mkSeq "w", mkSeq "x", mkSeq "y", mkSeq "z"

let ``ϵ`` = Empty

let (.|) x y = Cons(x, y)
let (++) x y = Concat(x, y)

let len x = ExtInteger(Length x)

let prepend = a .| ``ϵ`` != ``ϵ`` |> axiom "prepend"

let ``non empty`` = a .| x != ``ϵ``

let equality = a .| x = (b .| y) === (a = b <&&> (x = y)) |> axiom "equality"

let ``GS 13.7`` () =
  proof { theorem "GS 13.7" (a .| x != x) }


let ``length of ϵ`` = len ``ϵ`` = zero |> axiom "length of ϵ"

let ``length of cons`` = len (a .| x) = one + len x |> axiom "length of cons"

let ``length of concat`` () =
  proof { theorem "length of concat" (len (x ++ y) = len x + len y) }
