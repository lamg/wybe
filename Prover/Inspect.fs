module Inspect

open Core

// ColorMessages

type Color =
  | BrightRed
  | BrightGreen
  | BrightYellow
  | BrightBlue
  | BrightMagenta

let ansiColor =
  function
  | BrightRed -> "\x1b[91m"
  | BrightGreen -> "\x1b[92m"
  | BrightYellow -> "\x1b[93m"
  | BrightBlue -> "\x1b[94m"
  | BrightMagenta -> "\x1b[95m"


let colorizeString color s =
  let c = ansiColor color
  let ansiReset = "\x1b[0m"
  $"%s{c}%s{s}%s{ansiReset}"

let message (c: Color) (head: string) (body: string) = $"{colorizeString c head}: {body}"

let info head body = message BrightBlue head body
let error head body = message BrightRed head body

let section head = $"{colorizeString BrightYellow head}"
let sectionBody head body = message BrightYellow head body

// Formatters

let internal printOperator =
  function
  | StepOperator.Equiv -> "≡"
  | StepOperator.Implies -> "⇒"
  | StepOperator.Follows -> "⇐"
  | StepOperator.Equals -> "="

let printLaws (xs: Law list) =
  xs |> List.map _.identifier |> String.concat ", " |> sprintf "{ %s }"

let printHint (x: Step) =
  $"{printOperator x.stepOp} {printLaws x.laws}"

let printStep (x: Step) =
  [ $"  {x.fromExp}"; printHint x; $"  {x.toExp}" ]

let printCalculation (calc: Calculation) =
  let header = info "demonstrandum" (calc.demonstrandum.body.ToString())

  match calc.steps with
  | [] -> failwith "List is empty"
  | x :: xs ->
    let first = printStep x

    let nextSteps = xs |> List.collect (fun x -> [ printHint x; $"  {x.toExp}" ])

    let lastStep = [ "▢" ] // \squoval character

    header :: (first @ nextSteps @ lastStep)

let printCheckedCalculation (calc: CheckedCalculation) =
  let c = calc.calculation
  let header = section "proof"
  let ok = if calc.error.IsNone then "✅" else "❌"
  let theorem = info "  theorem" $"{c.demonstrandum.body} {ok}"

  match c.steps with
  | [] -> [ header; theorem; section "▢" ]
  | x :: xs ->
    let first = printStep x

    let nextSteps = xs |> List.collect (fun x -> [ printHint x; $"  {x.toExp}" ])

    let lastStep = [ section "▢" ]

    header :: theorem :: (first @ nextSteps @ lastStep)

let printCalculationError (calc: CheckedCalculation) =
  match calc.error with
  | Some(FailedSteps xs) -> error "failed steps" "" :: (xs |> List.map (fun (i, p, r) -> $"{i}: {p} | {r}"))
  | Some(WrongEvidence(counterExample, premise, conclusion)) ->
    let implication = premise |> List.map (_.ToString()) |> String.concat ", "

    [ error "invalid evidence" ""
      $"❌ counter-example found: {counterExample}"
      $"assuming: {implication}"
      $"to conclude: {conclusion}" ]
  | Some(FailedParsing e) -> [ $"failed parsing: {e}" ]
  | Some(InsufficientEvidence(assumptions, d)) ->
    [ error "insufficient evidence" ""
      $"assumptions {assumptions}"
      $"conclusion {d}" ]
  | Some(RefutedFormula d) -> [ error $"❌ refuted formula" $"{d}" ]
  | None -> []

// Inspect external interface

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

let checkAll (xs: list<unit -> Core.CheckedCalculation>) =
  xs
  |> List.iter (fun th ->
    match th () with
    | { error = None } -> ()
    | c ->
      let msg = c |> inspect |> summary |> _.accumulated |> String.concat "\n"
      failwith msg)

let failIfNotProved (x: Inspection) =
  match x.calc.error with
  | Some(Core.WrongEvidence(counterExample, p, c)) ->
    failwith $"Counter-example found {counterExample}: {p} doesn't imply {c}"
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
