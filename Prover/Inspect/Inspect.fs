module Inspect

open Formatters
open ColorMessages

type Inspection =
  { accumulated: string list
    calc: Core.CheckedCalculation }

let inspect (r: Core.CheckedCalculation) = { accumulated = []; calc = r }

let private addLines (n: Inspection) xs =
  { n with
      accumulated = List.append n.accumulated xs }

let calculation (n: Inspection) =
  n.calc.calculation
  |> printCalculation
  |> List.append [ section "calculation" ]
  |> addLines n

let stepAt (i: int) (n: Inspection) =
  match List.tryItem i n.calc.calculation.steps with
  | Some s -> printStep s |> addLines n
  | None ->
    [ sectionBody "step at" "19"
      error "out of range" $"0 ≤ {i} < {n.calc.calculation.steps.Length}" ]
    |> addLines n

let hintAt (step: int) (n: Inspection) =
  let hint =
    n.calc.calculation.steps
    |> List.tryItem step
    |> function
      | Some s -> sectionBody $"hint at {step}" (printHint s)
      | None -> error $"hint at {step}" "None"

  addLines n [ hint ]

let print (n: Inspection) =
  n.accumulated |> List.iter (printfn "%s")
  n

let printAndClear (n: Inspection) =
  n.accumulated |> List.iter (printfn "%s")
  { n with accumulated = [] }

let printToResult (n: Inspection) = n |> print |> _.calc |> Ok

let calculationSummary (calc: Core.CheckedCalculation) =
  let theoremName = calc.calculation.demonstrandum.identifier

  let failed =
    calc.error
    |> Option.map (function
      | Core.FailedSteps xs -> xs |> List.map (fun (i, _, _) -> $"{i}") |> String.concat ", "
      | Core.FailedParsing e -> $"{e}"
      | Core.WrongEvidence(premise, consequence) ->
        $"calculation reduces to: {premise}, but does not implies {consequence}"
      | Core.InsufficientEvidence demonstrandum -> $"insufficient evidence for: {demonstrandum}"
      | Core.InvalidFormula demonstrandum -> $"invalid formula {demonstrandum}")
    |> Option.map (fun s -> error "failed" s)
    |> Option.toList

  let ok = if calc.error.IsNone then "✅" else "❌"

  let calculation = section "summary" :: printCheckedCalculation calc

  calculation @ [ info $"{ok} theorem" theoremName ] @ failed

let summary (n: Inspection) =
  n.calc |> calculationSummary |> addLines n

let calculationError (n: Inspection) =
  n.calc |> printCalculationError |> addLines n

let printCalculationResult (r: Core.CheckedCalculation) =
  let n = inspect r

  match printCalculationError n.calc with
  | [] -> [ $"✅ {n.calc.calculation.demonstrandum.identifier}" ]
  | xs -> xs
  |> addLines n
  |> print
  |> ignore

let checkTheorems (xs: list<unit -> Core.CheckedCalculation>) =
  xs
  |> List.iter (fun th ->
    match th () with
    | { error = None } -> ()
    | c -> c |> inspect |> summary |> print |> ignore)
