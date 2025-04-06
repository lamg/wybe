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

let inspect (calc: Calculation) =
  match check calc with
  | Ok calc -> { accumulated = [||]; calc = calc }
  | Error e ->
    { accumulated = [| e.ToString() |]
      calc =
        { calculation = calc
          check =
            { transitiveReduction =
                0,
                { node =
                    { symbol = Fixed ""
                      signature = boolId }
                  subtrees = [] }
              expandedSteps = [||]
              evidence = None
              okReduction = false
              okSteps = false
              isOk = false } } }

let private addLines (n: Inspection) xs =
  { n with
      accumulated = Array.append n.accumulated xs }

let calculation (n: Inspection) =
  n.calc.calculation |> printCalculation |> addLines n

let private mapStepExpansion
  (f: StepExpansion.StepExpansion<TypedSymbol> -> array<string>)
  (step: int)
  (n: Inspection)
  =
  let withHeader = [| info "step" $"{step}" |] |> addLines n

  n.calc.check.expandedSteps
  |> function
    | steps when 0 >= step && step < steps.Length ->
      let xs = steps[step] |> f

      match true with
      | _ when Seq.isEmpty xs -> [| error $"expansion_{step}" "None" |]
      | _ -> xs
    | _ -> [| error $"step_{step}" "None" |]
  |> addLines withHeader

let expansionsAt = mapStepExpansion expansionToStrList
let rewritersAt = mapStepExpansion rewritersToStrList

let stepAt = mapStepExpansion alternativesToStrList

let hintAt (step: int) (n: Inspection) =
  let hint =
    n.calc.calculation.steps
    |> Array.tryItem step
    |> function
      | Some s -> [| info $"hint_{step}" (printHint s.hint) |]
      | None -> [| error $"hint_{step}" "None" |]

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

  mapStepExpansion f step n

let print (n: Inspection) =
  n.accumulated |> Array.iter (printfn "%s")
  n

let printAndClear (n: Inspection) =
  n.accumulated |> Array.iter (printfn "%s")
  { n with accumulated = [||] }

let summary (n: Inspection) =
  let theorem = n.calc.calculation.demonstrandum.expr |> printTypedExpr

  let boolMessage ok item =
    if ok then
      info item (ok.ToString())
    else
      error item (ok.ToString())

  let failedSteps =
    if not n.calc.check.okSteps then
      n.calc.check.expandedSteps
      |> Array.choosei (fun i xs ->
        let notOk = xs |> Seq.exists (fun x -> x.expansion.node.path.IsNone)
        if notOk then Some i else None)
    else
      [||]


  [ info "theorem" theorem
    boolMessage n.calc.check.isOk "ok proof"
    boolMessage n.calc.check.okSteps "ok steps"
    if failedSteps.Length <> 0 then
      error "failed steps" (failedSteps |> Array.map _.ToString() |> String.concat ", ")
    else
      ()
    boolMessage n.calc.check.okReduction "ok transitivity"
    boolMessage n.calc.check.evidence.IsSome "ok evidence"
    if n.calc.check.expandedSteps.Length = 0 then
      boolMessage false "non-empty proof"
    else
      () ]
  |> List.toArray
  |> addLines n
