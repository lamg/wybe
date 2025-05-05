module Core

open Microsoft.Z3

type IZ3Var =
  abstract member toZ3Var: Context -> Expr

type IZ3Bool =
  abstract member toZ3Bool: Context -> BoolExpr

and Integer =
  | Integer of int64
  | Var of string
  | Eq of Integer * Integer // =
  | Exceeds of Integer * Integer // >
  | Lt of Integer * Integer // <
  | AtLeast of Integer * Integer // ≥
  | AtMost of Integer * Integer // ≤

  interface IZ3Bool with
    member this.toZ3Bool(ctx: Context) : BoolExpr =
      match this with
      | Eq _ -> failwith ""
      | Exceeds(_, _) -> failwith "Not Implemented"
      | Lt(_, _) -> failwith "Not Implemented"
      | AtLeast(_, _) -> failwith "Not Implemented"
      | AtMost(_, _) -> failwith "Not Implemented"
      | _ -> failwith $"cannot make {this} a boolean expression"

  interface IZ3Var with
    member this.toZ3Var(ctx: Context) : Expr =
      match this with
      | Var s -> ctx.MkIntConst s
      | _ -> failwith $"cannot make {this} a var"


and Bool =
  | True
  | False
  | Var of string

  override this.ToString() =
    match this with
    | True -> "true"
    | False -> "false"
    | Var v -> v

  interface IZ3Bool with

    member this.toZ3Bool(ctx: Context) : BoolExpr =
      match this with
      | True -> ctx.MkBool true
      | False -> ctx.MkBool false
      | Var v -> ctx.MkBoolConst v

  interface IZ3Var with
    member this.toZ3Var(ctx: Context) : Expr =
      match this with
      | Var v -> ctx.MkBoolConst v
      | _ -> failwith $"cannot make {this} a var"

and Pred =
  | Bool of IZ3Bool
  | Not of right: Pred
  | And of left: Pred * right: Pred
  | Or of left: Pred * right: Pred
  | Equiv of left: Pred * right: Pred
  | Differs of left: Pred * right: Pred
  | Implies of left: Pred * right: Pred
  | Follows of left: Pred * right: Pred
  | Forall of IZ3Var list * Pred
  | Exists of IZ3Var list * Pred

  interface IZ3Var with
    member _.toZ3Var(_: Context) : Expr =
      raise (System.NotImplementedException())

  interface IZ3Bool with

    member this.toZ3Bool(ctx: Context) : BoolExpr =
      let toExp (p: IZ3Bool) = p.toZ3Bool ctx

      match this with
      | Bool b -> b.toZ3Bool ctx
      | Not right -> ctx.MkNot(toExp right)
      | And(left, right) -> ctx.MkAnd(toExp left, toExp right)
      | Or(left, right) -> ctx.MkOr(toExp left, toExp right)
      | Equiv(left, right) -> ctx.MkEq(toExp left, toExp right)
      | Differs(left, right) -> Not(Equiv(left, right)) |> toExp
      | Implies(left, right) -> ctx.MkImplies(toExp left, toExp right)
      | Follows(left, right) -> ctx.MkImplies(toExp right, toExp left)
      | Forall(vars, body) ->
        let body = (body :> IZ3Bool).toZ3Bool ctx
        let vars = vars |> List.map (fun x -> x.toZ3Var ctx) |> List.toArray
        ctx.MkForall(vars, body)
      | Exists(vars, body) ->
        let body = (body :> IZ3Bool).toZ3Bool ctx
        let vars = vars |> List.map (fun x -> x.toZ3Var ctx) |> List.toArray
        ctx.MkExists(vars, body)

[<RequireQualifiedAccess>]
type StepOperator =
  | Equiv
  | Implies
  | Follows

type Step =
  { fromExp: Pred
    toExp: Pred
    stepOp: StepOperator
    laws: Pred list }

let stepToPred (s: Step) =
  match s.stepOp with
  | StepOperator.Equiv -> Equiv(s.fromExp, s.toExp)
  | StepOperator.Follows -> Follows(s.fromExp, s.toExp)
  | StepOperator.Implies -> Implies(s.fromExp, s.toExp)

let stepToImplication (s: Step) =
  match s.laws with
  | [] -> stepToPred s
  | x :: xs ->
    let ls = xs |> List.fold (fun acc x -> And(acc, x)) x
    let step = stepToPred s
    Implies(ls, step)

type CheckResult =
  | Proved
  | Refuted of string
  | Unknown

let checkPredicate (ctx: Context) (p: Pred) =
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

type CalcError =
  | FailedParsing of ParseError
  | FailedSteps of list<int * Pred * CheckResult>
  | WrongEvidence of premise: Pred * consequence: Pred

let checkStepsImpliesDemonstrandum (ctx: Context) (steps: Step list) (demonstrandum: Pred) =
  match steps with
  | [] ->
    match checkPredicate ctx demonstrandum with
    | Proved -> Ok()
    | _ -> Error(WrongEvidence(demonstrandum, demonstrandum))
  | x :: xs ->
    let r = xs |> List.fold (fun acc x -> And(acc, stepToPred x)) (stepToPred x)
    let evidence = Implies(r, demonstrandum)

    match checkPredicate ctx evidence with
    | Proved -> Ok()
    | _ -> Error(WrongEvidence(r, demonstrandum))

open FsToolkit.ErrorHandling

type LawHint =
  | End
  | Laws of Pred list

type ProofLine =
  | Hint of StepOperator * Pred list
  | Pred of Pred
  | Theorem of string * Pred
  | Name of string

type Calculation =
  { demonstrandum: Pred
    name: string
    steps: Step list }

let buildBasic (lines: ProofLine list) =
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

type CheckedCalculation =
  { calculation: Calculation
    error: CalcError option }

type CalculationCE() =
  member _.Bind(l: ProofLine, f: ProofLine -> ProofLine list) = f l

  member _.Zero() = []

  member _.Yield(s: ProofLine) = [ s ]
  member _.Yield(s: Pred) = [ Pred s ]

  member _.Return(x: ProofLine) = [ x ]

  member _.ReturnFrom(l: ProofLine list) = l

  member _.Combine(l1: ProofLine list, l2: ProofLine list) = l1 @ l2

  member _.Delay(f: unit -> ProofLine list) = f ()

  member _.Run(xs: ProofLine list) =
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
    | Error e -> failwith $"{e}"


let proof = CalculationCE()

type LawsCE(op: StepOperator) =
  member _.Yield(x: Pred) = [ x ]
  member _.Yield(xs: Pred list) = xs

  member _.Yield(x: CheckedCalculation) =
    match x.error with
    | None -> [ x.calculation.demonstrandum ]
    | Some e -> failwith $"cannot extract law from failed proof {e}"

  member this.Yield(xs: CheckedCalculation list) = xs |> List.collect this.Yield

  member this.Yield(xs: (unit -> CheckedCalculation) list) =
    xs |> List.collect (fun f -> f () |> this.Yield)

  member this.Yield(x: unit -> CheckedCalculation) = x () |> this.Yield

  member _.Combine(xs: Pred list, ys: Pred list) = xs @ ys
  member _.Run(xs: Pred list) = Hint(op, xs)
  member _.Zero() = []
  member _.Return(x: Pred) = [ x ]
  member _.Delay(f: unit -> Pred list) = f ()

let ``≡`` = LawsCE StepOperator.Equiv

let ``⇒`` = LawsCE StepOperator.Implies

let ``⇐`` = LawsCE StepOperator.Follows

let (!) x = Not x
let (===) x y = Equiv(x, y)
let (!==) x y = Differs(x, y)
let (==>) x y = Implies(x, y)
let (<&&>) x y = And(x, y)
let (<||>) x y = Or(x, y)
let ``∀`` vars body = Forall(vars, body)
let ``∃`` vars body = Exists(vars, body)

let axiom name pred =
  { calculation =
      { demonstrandum = pred
        steps = []
        name = name }
    error = None }
