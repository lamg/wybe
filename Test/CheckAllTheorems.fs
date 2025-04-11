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
    Theorems.``∨ identity`` ]
  |> List.map (fun th -> th () |> CalculationCE.extractLaw)
  |> ignore

[<Fact>]
let ``building law from equivalent laws`` () =
  let actual =
    Axioms.eqLaws Theorems.``true theorem`` Axioms.``excluded middle``
    |> _.expr
    |> TypedExpression.printTypedExpr

  Assert.Equal("true ≡ (x ∨ ¬x)", actual)

// TODO use names like `∨-over-≡` instead of `∨ over ≡`, since it's getting confusing when formatting proofs
// should it be done in the formatter without interfering with the rest of the code
// or all names changed for consistency?

[<Fact>]
let ``inspect theorems`` () =
  Theorems.``∨ identity`` () |> inspect |> summary |> ignore
