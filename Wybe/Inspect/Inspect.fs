module Inspect.Inspect

open Z3
open Formatters
open ColorMessages
open FSharpPlus

type Inspection<'a when 'a: equality and 'a :> IZ3Bool> =
  { accumulated: string list
    calc: CheckedCalculation<'a> }

let inspect (r: CheckedCalculation<'a>) = { accumulated = []; calc = r }

let private addLines (n: Inspection<'a>) xs =
  { n with
      accumulated = List.append n.accumulated xs }

let calculation (n: Inspection<'a>) =
  n.calc.calculation
  |> printCalculation
  |> List.append [ section "calculation" ]
  |> addLines n

let stepAt (i: int) (n: Inspection<'a>) =
  match List.tryItem i n.calc.calculation.steps with
  | Some s -> printStep s |> addLines n
  | None ->
    [ sectionBody "step at" "19"
      error "out of range" $"0 ≤ {i} < {n.calc.calculation.steps.Length}" ]
    |> addLines n

let hintAt (step: int) (n: Inspection<'a>) =
  let hint =
    n.calc.calculation.steps
    |> List.tryItem step
    |> function
      | Some s -> sectionBody $"hint at {step}" (printHint s)
      | None -> error $"hint at {step}" "None"

  addLines n [ hint ]

let print (n: Inspection<'a>) =
  n.accumulated |> List.iter (printfn "%s")
  n

let printAndClear (n: Inspection<'a>) =
  n.accumulated |> List.iter (printfn "%s")
  { n with accumulated = [] }

let printToResult (n: Inspection<'a>) = n |> print |> _.calc |> Ok

let calculationSummary (calc: CheckedCalculation<'a>) =
  let theoremName = calc.calculation.name

  let failed =
    calc.error
    |> Option.map (function
      | FailedSteps xs -> xs |> List.map (fun (i, _, _) -> $"{i}") |> String.concat ", "
      | FailedParsing e -> $"{e}"
      | WrongEvidence(premise, consequence) ->
        $"calculation reduces to: {printPredicate premise}, but does not implies {printPredicate consequence}")
    |> Option.map (fun s -> error "failed" s)
    |> Option.toList

  let ok = if calc.error.IsNone then "✅" else "❌"

  let calculation = section "summary" :: printCalculation calc.calculation

  calculation @ [ info $"{ok} theorem" theoremName ] @ failed

let summary (n: Inspection<'a>) =
  n.calc |> calculationSummary |> addLines n
