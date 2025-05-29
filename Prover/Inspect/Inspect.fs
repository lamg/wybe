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
  (match List.tryItem i n.calc.calculation.steps with
   | Some s -> printStep s
   | None ->
     [ sectionBody "step at" $"{i}"
       error "out of range" $"0 ≤ {i} < {n.calc.calculation.steps.Length}" ])
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
  let failed = printCalculationError calc
  let calculation = printCheckedCalculation calc
  calculation @ failed

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
  xs |> List.iter (fun th -> th () |> printCalculationResult)

let findFailingProof (xs: list<unit -> Core.CheckedCalculation>) =
  xs
  |> List.iter (fun th ->
    match th () with
    | { error = None } -> ()
    | c ->
      let msg = c |> inspect |> summary |> _.accumulated |> String.concat "\n"
      failwith msg)

let failIfNotProved (x: Inspection) =
  match x.calc.error with
  | Some(Core.WrongEvidence(counterExample, p, c)) -> failwith $"Counter-example found {counterExample}: {p} doesn't imply {c}"
  | Some e -> failwith $"{e}"
  | None -> ()

let stepPropAt (i: int) (n: Inspection) =
  (match List.tryItem i n.calc.calculation.steps with
   | Some s ->
     [ sectionBody "step proposition at" $"{i}"
       (Core.stepToProposition s).ToString() ]
   | None ->
     [ sectionBody "step at" $"{i}"
       error "out of range" $"0 ≤ {i} < {n.calc.calculation.steps.Length}" ])
  |> addLines n
