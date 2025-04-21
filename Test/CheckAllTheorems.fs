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
    Theorems.``true theorem``
    Theorems.``∨ zero``
    Theorems.``∨ identity``
    Theorems.``∨ over ∨``
    Theorems.``GS 3.32`` ]
  |> List.map (fun th -> th () |> CalculationCE.extractLaw)
  |> ignore

[<Fact>]
let ``building law from equivalent laws`` () =
  let actual =
    Axioms.eqLaws Theorems.``true theorem`` Axioms.``excluded middle``
    |> _.expr
    |> TypedExpression.printTypedExpr

  Assert.Equal("true ≡ (x ∨ ¬x)", actual)

[<Fact>]
let ``inspect theorems`` () =
  Theorems.``∨ over ∨`` () |> inspect |> stepAt 0 |> summary |> ignore
