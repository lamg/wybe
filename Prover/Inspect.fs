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
  xs |> List.map _.Identifier |> String.concat ", " |> sprintf "{ %s }"

let printHint (x: Step) =
  $"{printOperator x.StepOp} {printLaws x.Laws}"

let printStep (x: Step) =
  [ $"  {x.FromExpr}"; printHint x; $"  {x.ToExpr}" ]

let printCalculation (calc: Calculation) =
  let header = info "demonstrandum" (calc.Demonstrandum.Body.ToString())

  match calc.Steps with
  | [] -> failwith "List is empty"
  | x :: xs ->
    let first = printStep x

    let nextSteps = xs |> List.collect (fun x -> [ printHint x; $"  {x.ToExpr}" ])

    let lastStep = [ "▢" ] // \squoval character

    header :: (first @ nextSteps @ lastStep)

let printCheckedCalculation (calc: CheckedCalculation) =
  let c = calc.Calculation
  let header = section "proof"
  let ok = if calc.Error.IsNone then "✅" else "❌"
  let theorem = info "  theorem" $"{c.Demonstrandum.Body} {ok}"

  match c.Steps with
  | [] -> [ header; theorem; section "▢" ]
  | x :: xs ->
    let first = printStep x

    let nextSteps = xs |> List.collect (fun x -> [ printHint x; $"  {x.ToExpr}" ])

    let lastStep = [ section "▢" ]

    header :: theorem :: (first @ nextSteps @ lastStep)

let printCalculationError (calc: CheckedCalculation) =
  match calc.Error with
  | Some(FailedSteps xs) -> error "failed steps" "" :: (xs |> List.map (fun (i, p, r) -> $"{i}: {p} | {r}"))
  | Some(WrongEvidence(counterExample, premise, conclusion)) ->
    let implication = premise |> List.map (_.ToString()) |> String.concat ", "

    [ error "invalid evidence" ""
      $"❌ counter-example found: {counterExample}"
      $"assuming: {implication}"
      $"to conclude: {conclusion}" ]
  | Some(FailedParsing(lineNo, _lines, _expected)) -> [ $"failed parsing: line {lineNo}" ]
  | Some(InsufficientEvidence(assumptions, d)) ->
    [ error "insufficient evidence" ""
      $"assumptions {assumptions}"
      $"conclusion {d}" ]
  | Some(RefutedFormula d) -> [ error $"❌ refuted formula" $"{d}" ]
  | _ -> []

// Inspect external interface

type Inspection =
  | Inspection of accumulated: string list * calc: Core.CheckedCalculation

  member this.Accumulated =
    let (Inspection(accumulated, _)) = this
    accumulated

  member this.Calc =
    let (Inspection(_, calc)) = this
    calc

  member this.AddLines xs =
    Inspection(List.append this.Accumulated xs, this.Calc)

  member this.Clear() = Inspection([], this.Calc)

let inspect (r: Core.CheckedCalculation) = Inspection([], r)

let calculation (n: Inspection) =
  n.Calc.Calculation
  |> printCalculation
  |> List.append [ section "calculation" ]
  |> n.AddLines

let stepAt (i: int) (n: Inspection) =
  (match List.tryItem i n.Calc.Calculation.Steps with
   | Some s -> printStep s
   | None ->
     [ sectionBody "step at" $"{i}"
       error "out of range" $"0 ≤ {i} < {n.Calc.Calculation.Steps.Length}" ])
  |> n.AddLines

let hintAt (step: int) (n: Inspection) =
  let hint =
    n.Calc.Calculation.Steps
    |> List.tryItem step
    |> function
      | Some s -> sectionBody $"hint at {step}" (printHint s)
      | None -> error $"hint at {step}" "None"

  n.AddLines [ hint ]

let print (n: Inspection) =
  n.Accumulated |> List.iter (printfn "%s")
  n

let printAndClear (n: Inspection) =
  n.Accumulated |> List.iter (printfn "%s")
  n.Clear()

let printToResult (n: Inspection) = n |> print |> _.Calc |> Ok

let calculationSummary (calc: Core.CheckedCalculation) =
  let failed = printCalculationError calc
  let calculation = printCheckedCalculation calc
  calculation @ failed

let summary (n: Inspection) =
  n.Calc |> calculationSummary |> n.AddLines

let calculationError (n: Inspection) =
  n.Calc |> printCalculationError |> n.AddLines

let printCalculationResult (r: Core.CheckedCalculation) =
  let n = inspect r

  match printCalculationError n.Calc with
  | [] -> [ $"✅ {n.Calc.Calculation.Demonstrandum.Identifier}" ]
  | xs -> xs
  |> n.AddLines
  |> print
  |> ignore

let checkTheorems (xs: list<unit -> Core.CheckedCalculation>) =
  xs |> List.iter (fun th -> th () |> printCalculationResult)

let checkAll (xs: list<unit -> Core.CheckedCalculation>) =
  xs
  |> List.iter (fun th ->
    match th () with
    | CheckedCalculation(error = None) -> ()
    | c ->
      let msg = c |> inspect |> summary |> _.Accumulated |> String.concat "\n"
      failwith msg)

let failIfNotProved (x: Inspection) =
  match x.Calc.Error with
  | Some(Core.WrongEvidence(counterExample, p, c)) ->
    failwith $"Counter-example found {counterExample}: {p} doesn't imply {c}"
  | Some e -> failwith $"{e}"
  | None -> ()

let stepPropAt (i: int) (n: Inspection) =
  (match List.tryItem i n.Calc.Calculation.Steps with
   | Some s ->
     [ sectionBody "step proposition at" $"{i}"
       (Core.stepToProposition s).ToString() ]
   | None ->
     [ sectionBody "step at" $"{i}"
       error "out of range" $"0 ≤ {i} < {n.Calc.Calculation.Steps.Length}" ])
  |> n.AddLines

let printSemanticInfo (moduleSemantics: Map<string, Proposition array>) =
  moduleSemantics
  |> Map.fold
    (fun acc k ps ->
      let props = ps |> Array.mapi (fun i x -> info $"[{i}]" $"{x}") |> String.concat "\n"
      section k :: props :: acc)
    []
  |> List.iter (printfn "%s")
