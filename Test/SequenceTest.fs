module SequenceTest

open Xunit
open Core
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
