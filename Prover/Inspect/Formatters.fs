module internal Formatters

open Core
open ColorMessages

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

    let lastStep = [ "▢" ]

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
