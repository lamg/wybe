module CheckAllTheorems

open Xunit
open GriesSchneider
open Inspect.Inspect

[<Fact>]
let ``check all theorems`` () =
  [ Theorems.``associativity of ≢``
    Theorems.``double negation``
    Theorems.``GS 3.11``
    Theorems.``GS 3.14``
    Theorems.``mutual associativity``
    Theorems.``mutual interchangeability``
    Theorems.``negation of false``
    Theorems.``symmetry of ≢``
    Theorems.``true theorem`` ]
  |> List.map CalculationCE.extractLaw
  |> ignore

[<Fact>]
let ``inspect theorems`` () =
  Theorems.``mutual associativity`` |> inspect |> stepAt 0 |> summary |> ignore
