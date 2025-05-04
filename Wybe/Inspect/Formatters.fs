module Inspect.Formatters

open Core
open ColorMessages

let indentLine n line = String.replicate n " " + line


let printPredicate (p: Pred<'a>) =
  let parenthesize
    (parentBindingPower: int)
    (parentOperator: string)
    (childBindingPower: int)
    (childOperator: string option)
    (child: string)
    =
    if childBindingPower >= parentBindingPower then
      if
        childBindingPower = parentBindingPower
        && childOperator.IsSome
        && childOperator.Value <> parentOperator

      then
        $"({child})"
      else
        child
    else
      $"({child})"

  let rec binaryOpFormat (pred: int) (symbol: string) (left: Pred<'a>) (right: Pred<'a>) =
    let l, symLeft, predLeft = loop left
    let r, symRight, predRight = loop right

    let x = parenthesize pred symbol predLeft symLeft l
    let y = parenthesize pred symbol predRight symRight r

    $"{x} {symbol} {y}", Some symbol, pred

  and loop (p: Pred<'a>) =
    match p with
    | True -> "true", None, 4
    | False -> "false", None, 4
    | Var v -> v, None, 4
    | Not p ->
      let notPred = 3
      let r, _, childOpBindingPower = loop p

      let t =
        if childOpBindingPower >= notPred then
          $"¬{r}"
        else
          $"¬({r})"

      t, Some "¬", notPred
    | And(left, right) -> binaryOpFormat 2 "∧" left right

    | Or(left, right) -> binaryOpFormat 2 "∨" left right
    | Implies(left, right) -> binaryOpFormat 1 "⇒" left right

    | Follows(left, right) -> binaryOpFormat 1 "⇐" left right
    | Bool _ -> failwith "Not Implemented"
    | Equiv(left, right) -> binaryOpFormat 0 "≡" left right
    | Differs(left, right) -> binaryOpFormat 0 "≢" left right

  let r, _, _ = loop p
  r

let printOperator =
  function
  | StepOperator.Equiv -> "≡"
  | StepOperator.Implies -> "⇒"
  | StepOperator.Follows -> "⇐"

let printLaws (xs: Pred<'a> list) =
  xs |> List.map printPredicate |> String.concat ", " |> sprintf "{ %s }"

let printHint (x: Step<'a>) =
  $"{printOperator x.stepOp} {printLaws x.laws}"

let printStep (x: Step<'a>) =
  [ $"  {printPredicate x.fromExp}"; printHint x; $"  {printPredicate x.toExp}" ]

let printCalculation (calc: Calculation<'a>) =
  let header = info "demonstrandum" (calc.demonstrandum |> printPredicate)

  match calc.steps with
  | [] -> failwith "List is empty"
  | x :: xs ->
    let first = printStep x

    let nextSteps =
      xs |> List.collect (fun x -> [ printHint x; $"  {printPredicate x.toExp}" ])

    let lastStep = [ "▢" ]

    header :: (first @ nextSteps @ lastStep)

let printCheckedCalculation (calc: CheckedCalculation<'a>) =
  let error =
    match calc.error with
    | Some(FailedSteps xs) -> ""
    | Some(WrongEvidence _) -> ""
    | Some(FailedParsing _) -> failwith "Not Implemented"
    | None -> ""

  let c = calc.calculation

  let header = info "demonstrandum" (c.demonstrandum |> printPredicate)

  match c.steps with
  | [] -> failwith "List is empty"
  | x :: xs ->
    let first = printStep x

    let nextSteps =
      xs |> List.collect (fun x -> [ printHint x; $"  {printPredicate x.toExp}" ])

    let lastStep = [ "▢" ]

    header :: (first @ nextSteps @ lastStep)

let printCalculationError (calc: CheckedCalculation<'a>) =
  match calc.error with
  | Some(FailedSteps xs) ->
    error "failed steps" ""
    :: (xs |> List.map (fun (i, p, _) -> $"{i}: {printPredicate p}"))
  | Some(WrongEvidence(premise, conclusion)) ->
    let implication = premise ==> conclusion |> printPredicate
    let premise = printPredicate premise

    [ error "invalid evidence" ""
      $"calculation reduces to: {premise}"
      $"❌ implication does not hold: {implication}" ]
  | Some(FailedParsing e) -> [ $"failed parsing: {e}" ]
  | None -> []
