module SequenceTest

open Xunit
open Core
open Inspect
open GriesSchneider

[<Fact>]
let ``sequence theorems`` () =
  Inspect.checkAll [ ``GS 13.7``; ``length of concat`` ]

[<Fact>]
let ``length of ϵ`` () =
  let p () = proof { lemma (Length ``ϵ`` = zero) }
  Inspect.checkAll [ p ]

[<Fact>]
let ``length basic tests`` () =
  let xs = Cons(a, Cons(a, ``ϵ``))
  let p () = proof { lemma (Length xs = one + one) }
  Inspect.checkAll [ p ]

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
    Length xs, "#xs"
    Prefix(a, xs), "a ◁ xs" // Latex \triangleleft
    Suffix(a, xs), "a ▷ xs" // Latex \triangleright
    Concat(xs, ys), "xs ++ ys"
    Tail xs, "tail(xs)"
    Head xs, "head(xs)" ]
  |> List.iter (fun (x, s) -> Assert.Equal(s, x.ToString()))
