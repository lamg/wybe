module Core

open Microsoft.Z3

type IZ3Bool =
  abstract member toZ3Bool: Context -> BoolExpr

and Pred<'a when 'a: equality and 'a :> IZ3Bool> =
  | True
  | False
  | Var of string
  | Bool of 'a
  | Not of right: Pred<'a>
  | And of left: Pred<'a> * right: Pred<'a>
  | Or of left: Pred<'a> * right: Pred<'a>
  | Equiv of left: Pred<'a> * right: Pred<'a>
  | Differs of left: Pred<'a> * right: Pred<'a>
  | Implies of left: Pred<'a> * right: Pred<'a>
  | Follows of left: Pred<'a> * right: Pred<'a>

  interface IZ3Bool with
    member this.toZ3Bool(ctx: Context) : BoolExpr =
      let toExp (p: IZ3Bool) = p.toZ3Bool ctx

      match this with
      | True -> ctx.MkBool true
      | False -> ctx.MkBool false
      | Var v -> ctx.MkBoolConst v
      | Bool b -> b.toZ3Bool ctx
      | Not right -> ctx.MkNot(toExp right)
      | And(left, right) -> ctx.MkAnd(toExp left, toExp right)
      | Or(left, right) -> ctx.MkOr(toExp left, toExp right)
      | Equiv(left, right) -> ctx.MkEq(toExp left, toExp right)
      | Differs(left, right) -> Not(Equiv(left, right)) |> toExp
      | Implies(left, right) -> ctx.MkImplies(toExp left, toExp right)
      | Follows(left, right) -> ctx.MkImplies(toExp right, toExp left)

[<RequireQualifiedAccess>]
type StepOperator =
  | Equiv
  | Implies
  | Follows

type Step<'a when 'a: equality and 'a :> IZ3Bool> =
  { fromExp: Pred<'a>
    toExp: Pred<'a>
    stepOp: StepOperator
    laws: Pred<'a> list }

let stepToPred (s: Step<'a>) =
  match s.stepOp with
  | StepOperator.Equiv -> Equiv(s.fromExp, s.toExp)
  | StepOperator.Follows -> Follows(s.fromExp, s.toExp)
  | StepOperator.Implies -> Implies(s.fromExp, s.toExp)

let stepToImplication (s: Step<'a>) =
  let ls = s.laws |> List.fold (fun acc x -> And(acc, x)) True
  let step = stepToPred s

  match ls with
  | True -> step
  | _ -> Implies(ls, step)

type CheckResult =
  | Proved
  | Refuted of string
  | Unknown

let checkPredicate (ctx: Context) (p: Pred<'a>) =
  let solver = ctx.MkSolver()
  let zp = p :> IZ3Bool
  let exp = zp.toZ3Bool ctx
  solver.Add(ctx.MkNot exp)

  match solver.Check() with
  | Status.SATISFIABLE -> Refuted(solver.Model.Evaluate(exp).ToString())
  | Status.UNSATISFIABLE -> Proved
  | Status.UNKNOWN -> Unknown
  | v -> failwith $"unexpected enum value {v}"

type Expected =
  | ExpectingStep
  | ExpectingHint
  | ExpectingTheorem

type ParseError = { expected: Expected }

type CalcError<'a when 'a: equality and 'a :> IZ3Bool> =
  | FailedParsing of ParseError
  | FailedSteps of list<int * Pred<'a> * CheckResult>
  | WrongEvidence of premise: Pred<'a> * consequence: Pred<'a>

let checkStepsImpliesDemonstrandum (ctx: Context) (steps: Step<'a> list) (demonstrandum: Pred<'a>) =
  match steps with
  | [] ->
    match checkPredicate ctx demonstrandum with
    | Proved -> Ok()
    | _ -> Error(WrongEvidence(True, demonstrandum))
  | x :: xs ->
    let r = xs |> List.fold (fun acc x -> And(acc, stepToPred x)) (stepToPred x)
    let evidence = Implies(r, demonstrandum)

    match checkPredicate ctx evidence with
    | Proved -> Ok()
    | _ -> Error(WrongEvidence(r, demonstrandum))

open FsToolkit.ErrorHandling

type LawHint<'a when 'a: equality and 'a :> IZ3Bool> =
  | End
  | Laws of Pred<'a> list

type ProofLine<'a when 'a: equality and 'a :> IZ3Bool> =
  | Hint of StepOperator * Pred<'a> list
  | Pred of Pred<'a>
  | Theorem of string * Pred<'a>
  | Name of string

type Calculation<'a when 'a: equality and 'a :> IZ3Bool> =
  { demonstrandum: Pred<'a>
    name: string
    steps: Step<'a> list }

let buildBasic (lines: ProofLine<'a> list) =
  let rec fixedPoint (f: 'b -> 'b option) (state: 'b) =
    match f state with
    | Some x -> fixedPoint f x
    | None -> state

  // syntax of lines: theorem (expr hint)* expr
  result {
    let! (name, theorem), lines =
      match lines with
      | [] -> Error { expected = ExpectingTheorem }
      | Theorem(name, t) :: lines -> Ok((name, t), lines)
      | l :: _ -> Error { expected = ExpectingTheorem }

    let steps, lines =
      fixedPoint
        (function
        | steps, lines ->
          match lines with
          | [ Pred f; Hint(op, laws); Pred t ] ->
            Some(
              { fromExp = f
                toExp = t
                stepOp = op
                laws = laws }
              :: steps,
              []
            )
          | Pred f :: Hint(op, laws) :: Pred t :: lines ->
            Some(
              { fromExp = f
                toExp = t
                stepOp = op
                laws = laws }
              :: steps,
              Pred t :: lines
            )
          | _ -> None)
        ([], lines)

    do!
      match lines with
      | [] -> Ok()
      | Pred _ :: _ -> Error { expected = ExpectingHint }
      | _ :: _ -> Error { expected = ExpectingStep }

    return
      { demonstrandum = theorem
        steps = steps |> List.rev
        name = name }
  }

type CheckedCalculation<'a when 'a: equality and 'a :> IZ3Bool> =
  { calculation: Calculation<'a>
    error: CalcError<'a> option }

type CalculationCE<'a when 'a: equality and 'a :> IZ3Bool>() =
  member _.Bind(l: ProofLine<'a>, f: ProofLine<'a> -> ProofLine<'a> list) = f l

  member _.Zero() = []

  member _.Yield(s: ProofLine<'a>) = [ s ]
  member _.Yield(s: Pred<'a>) = [ Pred s ]

  member _.Return(x: ProofLine<'a>) = [ x ]

  member _.ReturnFrom(l: ProofLine<'a> list) = l

  member _.Combine(l1: ProofLine<'a> list, l2: ProofLine<'a> list) = l1 @ l2

  member _.Delay(f: unit -> ProofLine<'a> list) = f ()

  member _.Run(xs: ProofLine<'a> list) =
    match buildBasic xs with
    | Ok calc ->
      let ctx = new Context()

      let failed =
        calc.steps
        |> List.mapi (fun i s ->
          let p = stepToPred s

          match checkPredicate ctx p with
          | Proved -> []
          | e -> [ i, p, e ])
        |> List.concat

      let error =
        match failed with
        | [] ->
          match checkStepsImpliesDemonstrandum ctx calc.steps calc.demonstrandum with
          | Ok() -> None
          | Error e -> Some e
        | _ -> Some(FailedSteps failed)

      { calculation = calc; error = error }
    | Error e ->
      { calculation =
          { demonstrandum = False
            name = ""
            steps = [] }
        error = Some(FailedParsing e) }


let proof () = CalculationCE()

type LawsCE(op: StepOperator) =
  member _.Yield(x: Pred<'a>) = [ x ]
  member _.Yield(xs: Pred<'a> list) = xs

  member _.Yield(x: CheckedCalculation<'a>) =
    match x.error with
    | None -> [ x.calculation.demonstrandum ]
    | Some e -> failwith $"cannot extract law from failed proof {e}"

  member this.Yield(xs: CheckedCalculation<'a> list) = xs |> List.collect this.Yield

  member this.Yield(xs: (unit -> CheckedCalculation<'a>) list) =
    xs |> List.collect (fun f -> f () |> this.Yield)

  member this.Yield(x: unit -> CheckedCalculation<'a>) = x () |> this.Yield

  member _.Combine(xs: Pred<'a> list, ys: Pred<'a> list) = xs @ ys
  member _.Run(xs: Pred<'a> list) = Hint(op, xs)
  member _.Zero() = []
  member _.Return(x: Pred<'a>) = [ x ]
  member _.Delay(f: unit -> Pred<'a> list) = f ()

let ``≡`` = LawsCE StepOperator.Equiv

let ``⇒`` = LawsCE StepOperator.Implies

let ``⇐`` = LawsCE StepOperator.Follows

let (!) x = Not x
let (===) x y = Equiv(x, y)
let (!==) x y = Differs(x, y)
let (==>) x y = Implies(x, y)
let (<&&>) x y = And(x, y)
let (<||>) x y = Or(x, y)

let axiom name pred =
  { calculation =
      { demonstrandum = pred
        steps = []
        name = name }
    error = None }
