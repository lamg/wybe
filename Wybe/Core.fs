module Core

open Microsoft.Z3
#nowarn 86

type IZ3Expr =
  abstract member toZ3Bool: Context -> BoolExpr
  abstract member toZ3Var: Context -> Expr
  abstract member toZ3Expr: Context -> Expr

and Integer =
  | Integer of int64
  | Var of string
  | Plus of Integer * Integer
  | Minus of Integer * Integer
  | Times of Integer * Integer
  | Div of Integer * Integer
  // this terminology comes from https://www.cs.utexas.edu/~EWD/ewd07xx/EWD768.PDF
  | Exceeds of Integer * Integer // >
  | LessThan of Integer * Integer // <
  | AtLeast of Integer * Integer // ≥
  | AtMost of Integer * Integer // ≤

  override this.ToString() : string =
    match this with
    | Integer n -> n.ToString()
    | Var v -> v
    | Plus(x, y) -> $"{x} + {y}"
    | Minus(x, y) -> $"{x} - {y}"
    | Times(x, y) -> $"{x} × {y}"
    | Div(x, y) -> $"{x} / {y}"
    | Exceeds(x, y) -> $"{x} > {y}"
    | LessThan(x, y) -> $"{x} < {y}"
    | AtLeast(x, y) -> $"{x} ≥ {y}"
    | AtMost(x, y) -> $"{x} ≤ {y}"

  static member (~-)(x: Integer) =
    match x with
    | Integer n -> Integer(-n)
    | _ -> Minus(Integer 0, x)

  static member (+)(x: Integer, y: Integer) = Plus(x, y)
  static member (-)(x: Integer, y: Integer) = Minus(x, y)
  static member (*)(x: Integer, y: Integer) = Times(x, y)
  static member (/)(x: Integer, y: Integer) = Div(x, y)


  interface IZ3Expr with
    member this.toZ3Bool(ctx: Context) : BoolExpr =
      match this with
      | Exceeds(Integer n, Integer m) -> ctx.MkGt(ctx.MkInt n, ctx.MkInt m)
      | LessThan(Integer n, Integer m) -> ctx.MkLt(ctx.MkInt n, ctx.MkInt m)
      | AtLeast(Integer n, Integer m) -> ctx.MkGe(ctx.MkInt n, ctx.MkInt m)
      | AtMost(Integer n, Integer m) -> ctx.MkLe(ctx.MkInt n, ctx.MkInt m)
      | _ -> failwith $"cannot make {this} a boolean expression"

    member this.toZ3Var(ctx: Context) : Expr =
      match this with
      | Var s -> ctx.MkIntConst s
      | _ -> failwith $"cannot make a variable from expression {this}"

    member this.toZ3Expr(ctx: Context) : Expr =
      let toExp n =
        (n :> IZ3Expr).toZ3Expr ctx :?> ArithExpr

      match this with
      | Integer n -> ctx.MkInt n
      | Var v -> ctx.MkIntConst v
      | Plus(x, y) -> ctx.MkAdd(toExp x, toExp y)
      | Minus(x, y) -> ctx.MkSub(toExp x, toExp y)
      | Times(x, y) -> ctx.MkMul(toExp x, toExp y)
      | Div(x, y) -> ctx.MkDiv(toExp x, toExp y)
      | _ -> (this :> IZ3Expr).toZ3Bool ctx

and Bool =
  | True
  | False
  | Var of string

  override this.ToString() =
    match this with
    | True -> "true"
    | False -> "false"
    | Var v -> v

  interface IZ3Expr with

    member this.toZ3Bool(ctx: Context) : BoolExpr =
      match this with
      | True -> ctx.MkBool true
      | False -> ctx.MkBool false
      | Var v -> ctx.MkBoolConst v

    member this.toZ3Var(ctx: Context) : Expr =
      match this with
      | Var v -> ctx.MkBoolConst v
      | _ -> failwith $"cannot make a variable from expression {this}"

    member this.toZ3Expr(arg: Context) : Expr = (this :> IZ3Expr).toZ3Bool arg

and Pred =
  | Bool of IZ3Expr
  | Equals of IZ3Expr * IZ3Expr
  | Differs of IZ3Expr * IZ3Expr
  | Not of right: Pred
  | And of left: Pred * right: Pred
  | Or of left: Pred * right: Pred
  | Equiv of left: Pred * right: Pred
  | Inequiv of left: Pred * right: Pred
  | Implies of left: Pred * right: Pred
  | Follows of left: Pred * right: Pred
  | Forall of IZ3Expr list * Pred
  | Exists of IZ3Expr list * Pred

  override this.ToString() : string =
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
      | Equals(x, y) -> $"{x} = {y}", None, 4
      | Differs(x, y) -> $"{x} ≠ {y}", None, 4
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
      | Inequiv(left, right) -> binaryOpFormat 0 "≢" left right
      | Forall(vars, body) ->
        let vs = vars |> List.map (fun v -> v.ToString()) |> String.concat ","
        let p, _, _ = loop body
        $"⟨∀{vs} → {p}⟩", None, 5
      | Exists(vars, body) ->
        let vs = vars |> List.map (fun v -> v.ToString()) |> String.concat ","
        let p, _, _ = loop body
        $"⟨∃{vs} → {p}⟩", None, 5

    let r, _, _ = loop this
    r

  interface IZ3Expr with
    member this.toZ3Bool(ctx: Context) : BoolExpr =
      let toExp (p: IZ3Expr) = p.toZ3Bool ctx

      match this with
      | Bool b -> b.toZ3Bool ctx
      | Equals(n, m) -> ctx.MkEq(n.toZ3Expr ctx, m.toZ3Expr ctx)
      | Differs(n, m) -> ctx.MkNot(Equals(n, m) |> toExp)
      | Not right -> ctx.MkNot(toExp right)
      | And(left, right) -> ctx.MkAnd(toExp left, toExp right)
      | Or(left, right) -> ctx.MkOr(toExp left, toExp right)
      | Equiv(left, right) -> ctx.MkEq(toExp left, toExp right)
      | Inequiv(left, right) -> Not(Equiv(left, right)) |> toExp
      | Implies(left, right) -> ctx.MkImplies(toExp left, toExp right)
      | Follows(left, right) -> ctx.MkImplies(toExp right, toExp left)
      | Forall(vars, body) ->
        let z3Body = (body :> IZ3Expr).toZ3Bool ctx
        let z3Vars = vars |> List.map (fun v -> v.toZ3Var ctx) |> List.toArray
        ctx.MkForall(z3Vars, z3Body)
      | Exists(vars, body) ->
        let z3Body = (body :> IZ3Expr).toZ3Bool ctx
        let z3Vars = vars |> List.map (fun v -> v.toZ3Var ctx) |> List.toArray
        ctx.MkExists(z3Vars, z3Body)

    member this.toZ3Var(ctx: Context) : Expr =
      match this with
      | Bool b -> b.toZ3Var ctx
      | _ -> failwith $"cannot make a variable from expression {this}"

    member this.toZ3Expr(ctx: Context) : Expr = (this :> IZ3Expr).toZ3Bool ctx

type Calculation =
  { demonstrandum: Law; steps: Step list }

and CheckedCalculation =
  { calculation: Calculation
    error: CalcError option }

and Law = { identifier: string; body: Pred }

and [<RequireQualifiedAccess>] StepOperator =
  | Equiv
  | Implies
  | Follows
  | Equals

and Step =
  { fromExp: IZ3Expr
    toExp: IZ3Expr
    stepOp: StepOperator
    laws: Law list }

and Expected =
  | ExpectingStep
  | ExpectingHint
  | ExpectingTheorem

and ParseError = { expected: Expected }

and CheckResult =
  | Proved
  | Refuted of string
  | Unknown

and CalcError =
  | FailedParsing of ParseError
  | FailedSteps of list<int * Pred * CheckResult>
  | WrongEvidence of premise: Pred * consequence: Pred
  | InsufficientEvidence of demonstrandum: Pred
  | InvalidFormula of demonstrandum: Pred

let stepToPred (s: Step) =
  match s.stepOp with
  | StepOperator.Equiv -> Equiv(s.fromExp :?> Pred, s.toExp :?> Pred)
  | StepOperator.Follows -> Follows(s.fromExp :?> Pred, s.toExp :?> Pred)
  | StepOperator.Implies -> Implies(s.fromExp :?> Pred, s.toExp :?> Pred)
  | StepOperator.Equals -> Equals(s.fromExp, s.toExp)


let checkPredicate (ctx: Context) (p: Pred) =

  let solver = ctx.MkSolver()
  let zp = p :> IZ3Expr
  let exp = zp.toZ3Bool ctx
  solver.Add(ctx.MkNot exp)

  match solver.Check() with
  | Status.SATISFIABLE -> Refuted(solver.Model.Evaluate(exp).ToString())
  | Status.UNSATISFIABLE -> Proved
  | Status.UNKNOWN -> Unknown
  | v -> failwith $"unexpected enum value {v}"

let checkStepsImpliesDemonstrandum (ctx: Context) (steps: Step list) (demonstrandum: Pred) =
  match steps with
  | [] ->
    match checkPredicate ctx demonstrandum with
    | Proved -> Ok()
    | Unknown -> Error(InsufficientEvidence demonstrandum)
    | Refuted _ -> Error(InvalidFormula demonstrandum)
  | x :: xs ->
    let r = xs |> List.fold (fun acc x -> And(acc, stepToPred x)) (stepToPred x)
    let evidence = Implies(r, demonstrandum)

    match checkPredicate ctx evidence with
    | Proved -> Ok()
    | _ -> Error(WrongEvidence(r, demonstrandum))

open FsToolkit.ErrorHandling

type ProofLine =
  | Hint of StepOperator * Law list
  | WybeExpr of IZ3Expr
  | Theorem of Law
  | Name of string

let buildBasic (lines: ProofLine list) =
  let rec fixedPoint (f: 'b -> 'b option) (state: 'b) =
    match f state with
    | Some x -> fixedPoint f x
    | None -> state

  // syntax of lines: theorem (expr hint expr)*
  result {
    let! theorem, lines =
      match lines with
      | [] -> Error { expected = ExpectingTheorem }
      | Theorem t :: lines -> Ok(t, lines)
      | l :: _ -> Error { expected = ExpectingTheorem } // TODO pass a parameter to ExpectingTheorem to
    // make easier to find the invalid line

    let steps, lines =
      fixedPoint
        (function
        | steps, lines ->
          match lines with
          | [ WybeExpr f; Hint(op, laws); WybeExpr t ] ->

            Some(
              { fromExp = f
                toExp = t
                stepOp = op
                laws = laws }
              :: steps,
              []
            )
          | WybeExpr f :: Hint(op, laws) :: WybeExpr t :: lines ->
            Some(
              { fromExp = f
                toExp = t
                stepOp = op
                laws = laws }
              :: steps,
              WybeExpr t :: lines
            )
          | _ -> None)
        ([], lines)

    do!
      match lines with
      | [] -> Ok()
      | WybeExpr _ :: _ -> Error { expected = ExpectingHint }
      | _ :: _ -> Error { expected = ExpectingStep }

    return
      { demonstrandum = theorem
        steps = steps |> List.rev }
  }

type CalculationCE() =
  member _.Bind(l: ProofLine, f: ProofLine -> ProofLine list) = f l

  member _.Zero() = []

  member _.Yield(s: ProofLine) = [ s ]
  member _.Yield(s: IZ3Expr) = [ WybeExpr s ]

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
          match checkStepsImpliesDemonstrandum ctx calc.steps calc.demonstrandum.body with
          | Ok() -> None
          | Error e -> Some e
        | _ -> Some(FailedSteps failed)

      { calculation = calc; error = error }
    | Error e -> failwith $"{e}"


let proof = CalculationCE()

type LawsCE(op: StepOperator) =
  member _.Yield(x: Pred) =
    [ { identifier = x.ToString(); body = x } ]

  member _.Yield(x: Law) = [ x ]
  member _.Yield(xs: Law list) = xs

  member _.Yield(x: CheckedCalculation) =
    match x.error with
    | None -> [ x.calculation.demonstrandum ]
    | Some e -> failwith $"cannot extract law from failed proof {e}"

  member this.Yield(xs: CheckedCalculation list) = xs |> List.collect this.Yield

  member this.Yield(xs: (unit -> CheckedCalculation) list) =
    xs |> List.collect (fun f -> f () |> this.Yield)

  member this.Yield(x: unit -> CheckedCalculation) = x () |> this.Yield

  member _.Combine(xs: Law list, ys: Law list) = xs @ ys
  member _.Run(xs: Law list) = Hint(op, xs)
  member _.Zero() = []
  member _.Return(x: Law) = [ x ]
  member _.Delay(f: unit -> Law list) = f ()

let ``≡`` = LawsCE StepOperator.Equiv

let ``⇒`` = LawsCE StepOperator.Implies

let ``⇐`` = LawsCE StepOperator.Follows

let (!) x = Not x
let (===) x y = Equiv(x, y)
let (!==) x y = Inequiv(x, y)
let (==>) x y = Implies(x, y)
let (<==) x y = Follows(x, y)
let (<&&>) x y = And(x, y)
let (<||>) x y = Or(x, y)
let ``∀`` vars f = Forall(vars, f)
let ``∃`` vars f = Exists(vars, f)

let axiom name (pred: Pred) = { identifier = name; body = pred }
