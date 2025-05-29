module SequenceTest

open Xunit
open Core
open Inspect
open GriesSchneider.Integers
open GriesSchneider.Sequences

[<Fact>]
let ``sequence theorems`` () =
  Inspect.findFailingProof [ ``GS 13.7``; ``length of concat`` ]

[<Fact>]
let ``length of ϵ`` () =
  let p () = proof { lemma (Length ``ϵ`` = zero) }
  Inspect.findFailingProof [ p ]

[<Fact>]
let ``length basic tests`` () =
  let xs = Cons(a, Cons(a, ``ϵ``))
  let p () = proof { lemma (Length xs = one + one) }
  Inspect.findFailingProof [ p ]

[<Fact>]
let ``sequence head`` () =
  let xs = Cons(a, Cons(b, ``ϵ``))
  proof { lemma (Head xs = a) } |> inspect |> failIfNotProved

[<Fact>]
let ``sequence tail`` () =
  let xs = Cons(a, Cons(b, ``ϵ``))
  proof { lemma (Tail xs = Cons(b, ``ϵ``)) } |> inspect |> failIfNotProved

[<Fact>]
let ``sequences string representation`` () =

  [ Cons(a, Cons(a, ``ϵ``)), "a :: a :: ϵ" // Latex \epsilon
    Length x, "#x"
    Prefix(a, x), "a ◁ x" // Latex \triangleleft
    Suffix(a, x), "a ▷ x" // Latex \triangleright
    Concat(x, y), "x ++ y"
    Tail x, "tail(x)"
    Head x, "head(x)" ]
  |> List.iter (fun (x, s) -> Assert.Equal(s, x.ToString()))
