module Inspect.Formatters

open Core
open ColorMessages

let indentLine n line = String.replicate n " " + line


let printPredicate (p: Pred) =
  let parenthesize
    (parentBindingPower: int)
    (parentOperator: string)
    (childBindingPower: int)
    (childOperator: string option)
    (child: string)
    =
    if childBindingPower >= parentBindingPower then
      match childOperator with
      | Some childOp when childBindingPower = parentBindingPower && childOp <> parentOperator ->
        let mutualAssocOps = [ "≡"; "≢" ]
        let haveMutualAssoc = Set [ childOp; parentOperator ] = Set mutualAssocOps

        if not haveMutualAssoc then $"({child})" else child
      | _ -> child
    else
      $"({child})"

  let rec binaryOpFormat (pred: int) (symbol: string) (left: Pred) (right: Pred) =
    let l, symLeft, predLeft = loop left
    let r, symRight, predRight = loop right

    let x = parenthesize pred symbol predLeft symLeft l
    let y = parenthesize pred symbol predRight symRight r

    $"{x} {symbol} {y}", Some symbol, pred

  and loop (p: Pred) =
    match p with
    | Bool x -> $"{x}", None, 4
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
    | Equiv(left, right) -> binaryOpFormat 0 "≡" left right
    | Differs(left, right) -> binaryOpFormat 0 "≢" left right
    | Forall _ -> failwith "not implemented"
    | Exists(_, _) -> failwith "Not Implemented"

  let r, _, _ = loop p
  r

let printOperator =
  function
  | StepOperator.Equiv -> "≡"
  | StepOperator.Implies -> "⇒"
  | StepOperator.Follows -> "⇐"

let printLaws (xs: Pred list) =
  xs |> List.map printPredicate |> String.concat ", " |> sprintf "{ %s }"

let printHint (x: Step) =
  $"{printOperator x.stepOp} {printLaws x.laws}"

let printStep (x: Step) =
  [ $"  {printPredicate x.fromExp}"; printHint x; $"  {printPredicate x.toExp}" ]

let printCalculation (calc: Calculation) =
  let header = info "demonstrandum" (calc.demonstrandum |> printPredicate)

  match calc.steps with
  | [] -> failwith "List is empty"
  | x :: xs ->
    let first = printStep x

    let nextSteps =
      xs |> List.collect (fun x -> [ printHint x; $"  {printPredicate x.toExp}" ])

    let lastStep = [ "▢" ]

    header :: (first @ nextSteps @ lastStep)

let printCheckedCalculation (calc: CheckedCalculation) =
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

let printCalculationError (calc: CheckedCalculation) =
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
