module CheckAllTheorems

open Xunit
open GriesSchneider

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
    Theorems.trueTheorem ]
  |> List.map CalculationCE.extractLaw
  |> ignore
