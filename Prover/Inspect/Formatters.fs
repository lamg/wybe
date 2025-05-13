module Inspect.Formatters

open Core
open ColorMessages

let printOperator =
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

  let header = info "demonstrandum" (c.demonstrandum.body.ToString())

  match c.steps with
  | [] -> [ "▢" ]
  | x :: xs ->
    let first = printStep x

    let nextSteps = xs |> List.collect (fun x -> [ printHint x; $"  {x.toExp}" ])

    let lastStep = [ "▢" ]

    header :: (first @ nextSteps @ lastStep)

let printCalculationError (calc: CheckedCalculation) =
  match calc.error with
  | Some(FailedSteps xs) -> error "failed steps" "" :: (xs |> List.map (fun (i, p, _) -> $"{i}: {p}"))
  | Some(WrongEvidence(premise, conclusion)) ->
    let implication = premise ==> conclusion

    [ error "invalid evidence" ""
      $"calculation reduces to: {premise}"
      $"❌ implication does not hold: {implication}" ]
  | Some(FailedParsing e) -> [ $"failed parsing: {e}" ]
  | Some(InsufficientEvidence d) -> [ error "insufficient evidence" $"{d}" ]
  | Some(InvalidFormula d) -> [ error $"invalid formula {d}" "" ]
  | None -> []
