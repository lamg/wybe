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
    Theorems.``GS 3.32``
    Theorems.``∧ assoc`` ]
  |> List.iter (fun th ->
    match th () with
    | { error = None } -> ()
    | c ->
      let msg = c |> inspect |> summary |> _.accumulated |> String.concat "\n"
      failwith msg)
