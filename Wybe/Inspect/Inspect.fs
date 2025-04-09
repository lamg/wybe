module Inspect.Inspect

open Inference
open Formatters
open ExpressionMatch
open TypedExpression
open ColorMessages
open FSharpPlus

type Inspection =
  { accumulated: string array
    calc: CheckedCalculation }

let inspect (r: Result<CheckedCalculation, 'a>) =
  match r with
  | Ok calc -> { accumulated = [||]; calc = calc }
  | Error e -> failwith $"failed to build calculation: {e}"

let private addLines (n: Inspection) xs =
  { n with
      accumulated = Array.append n.accumulated xs }

let calculation (n: Inspection) =
  n.calc.calculation
  |> printCalculation
  |> Array.append [| section "calculation" |]
  |> addLines n

let private mapStepExpansion
  (sectionName: string)
  (f: StepExpansion.StepExpansion<TypedSymbol> -> array<string>)
  (step: int)
  (n: Inspection)
  =
  let withHeader = [| sectionBody sectionName $"{step}" |] |> addLines n

  n.calc.check.expandedSteps
  |> function
    | steps when 0 >= step && step < steps.Length ->
      let xs = steps[step] |> f

      match true with
      | _ when Seq.isEmpty xs -> [| error $"expansion_{step}" "None" |]
      | _ -> xs
    | _ -> [| error $"step_{step}" "None" |]
  |> addLines withHeader

let expansionsAt = mapStepExpansion "expansions at" expansionToStrList
let rewritersAt = mapStepExpansion "rewriters at" rewritersToStrList

let stepAt = mapStepExpansion "step at" alternativesToStrList

let hintAt (step: int) (n: Inspection) =
  let hint =
    n.calc.calculation.steps
    |> Array.tryItem step
    |> function
      | Some s -> [| sectionBody "hint at" $"{step}"; printHint s.hint |]
      | None -> [| error $"hint at {step}" "None" |]

  addLines n hint

let alternativeAt (step: int) (alt: int) (n: Inspection) =
  let f (xs: StepExpansion.StepExpansion<TypedSymbol>) =
    xs
    |> Seq.tryItem alt
    |> function
      | Some x ->
        [| [| info $"alternative_{alt}" "" |]
           rewritersToStrList [ x ]
           expansionToStrList [ x ] |]
        |> Array.concat
      | _ -> [| colorizeString BrightRed $"No alternative {alt}" |]

  mapStepExpansion "alternatives at" f step n

let print (n: Inspection) =
  n.accumulated |> Array.iter (printfn "%s")
  n

let printAndClear (n: Inspection) =
  n.accumulated |> Array.iter (printfn "%s")
  { n with accumulated = [||] }

let printToResult (n: Inspection) = n |> print |> _.calc |> Ok

let calculationSummary (calc: CheckedCalculation) =
  let theoremName = calc.calculation.demonstrandum.id

  let boolMessage ok item =
    if ok then
      info item (ok.ToString())
    else
      error item (ok.ToString())

  let failedSteps =
    if not calc.check.okSteps then
      calc.check.expandedSteps
      |> Array.choosei (fun i xs ->
        let notOk = xs |> Seq.exists (fun x -> x.expansion.node.path.IsNone)
        if notOk then Some i else None)
    else
      [||]

  let calculation =
    Array.append [| section "summary" |] (printCalculation calc.calculation)

  [ info "theorem" theoremName
    boolMessage calc.check.isOk "ok proof"
    boolMessage calc.check.okSteps "ok steps"
    if failedSteps.Length <> 0 then
      error "failed steps" (failedSteps |> Array.map _.ToString() |> String.concat ", ")
    else
      ()
    boolMessage calc.check.okReduction "ok transitivity"
    boolMessage calc.check.evidence.IsSome "ok evidence"
    if calc.check.expandedSteps.Length = 0 then
      boolMessage false "non-empty proof"
    else
      () ]
  |> List.toArray
  |> Array.append calculation

let summary (n: Inspection) =
  n.calc |> calculationSummary |> addLines n
