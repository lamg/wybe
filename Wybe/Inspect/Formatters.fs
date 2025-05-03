module Inspect.Formatters

open Z3
open ColorMessages

let indentLine n line = String.replicate n " " + line


let printPredicate (p: Pred<'a>) =
  let rec binaryOpFormat (pred: int) (symbol: string) (left: Pred<'a>) (right: Pred<'a>) =
    let l, predLeft = loop left
    let r, predRight = loop right

    let x = if predLeft >= pred then l else $"({l})"
    let y = if predRight >= pred then r else $"({r})"
    $"{x} {symbol} {y}", pred

  and loop (p: Pred<'a>) =
    match p with
    | Pred.True -> "true", 4
    | Pred.False -> "false", 4
    | Pred.Not p ->
      let notPred = 3
      let r, childOpPrecedence = loop p
      let t = if childOpPrecedence > notPred then $"¬{r}" else $"¬({r})"
      t, notPred
    | Pred.And(left, right) -> binaryOpFormat 2 "∧" left right

    | Pred.Or(left, right) -> binaryOpFormat 2 "∨" left right
    | Pred.Implies(left, right) -> binaryOpFormat 1 "⇒" left right

    | Pred.Follows(left, right) -> binaryOpFormat 1 "⇐" left right
    | Pred.Var v -> v, 4
    | Pred.Bool _ -> failwith "Not Implemented"
    | Pred.Equiv(left, right) -> binaryOpFormat 0 "≡" left right
    | Pred.Differs(left, right) -> binaryOpFormat 0 "≢" left right

  loop p |> fst

//"▢"
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
