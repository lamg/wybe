module CheckAllTheorems

open Xunit
open GriesSchneider.PredicateCalculus
open Inspect

[<Fact>]
let ``check all theorems`` () =
  [ ``associativity of ≢``
    ``double negation``
    ``GS 3.11``
    ``GS 3.14``
    ``mutual associativity``
    ``mutual interchangeability``
    ``negation of false``
    ``symmetry of ≢``
    ``true theorem``
    ``∨ zero``
    ``∨ identity``
    ``∨ over ∨``
    ``GS 3.32``
    ``∧ assoc``
    ``∧ idempotency``
    ``∧ zero``
    ``∧ over ∧``
    contradiction
    ``∧ ∨ absorption``
    ``∨ ∧ absorption``
    GriesSchneider.Integers.``× zero``
    GriesSchneider.Integers.``+ cancellation``
    fun _ -> GriesSchneider.Sequences.``GS 13.7`` Core.WBool ]
  |> List.iter (fun th ->
    match th () with
    | { error = None } -> ()
    | c ->
      let msg = c |> inspect |> summary |> _.accumulated |> String.concat "\n"
      failwith msg)
