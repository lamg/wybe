module Inspect.Formatters

open Core
open ColorMessages

let indentLine n line = String.replicate n " " + line


let printPredicate (p: Pred<'a>) =
  let parenthesize
    (parentPrecedence: int)
    (parentOperator: string)
    (childPrecedence: int)
    (childOperator: string option)
    (child: string)
    =
    if childPrecedence >= parentPrecedence then
      if
        childPrecedence = parentPrecedence
        && childOperator.IsSome
        && childOperator.Value <> parentOperator

      then
        $"({child})"
      else
        child
    else
      child

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
      let r, _, childOpPrecedence = loop p
      let t = if childOpPrecedence >= notPred then $"¬{r}" else $"¬({r})"
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

let printCalculation (c: Calculation<'a>) =
  let header = info "demonstrandum" (c.demonstrandum |> printPredicate)

  match c.steps with
  | [] -> failwith "List is empty"
  | x :: xs ->
    let first = printStep x

    let nextSteps =
      xs |> List.collect (fun x -> [ printHint x; $"  {printPredicate x.toExp}" ])

    let lastStep = [ "▢" ]

    header :: (first @ nextSteps @ lastStep)


let prepend (xs: 'a array) (x: 'a) = Array.append [| x |] xs
