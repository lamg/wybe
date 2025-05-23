module Core

open Microsoft.Z3
#nowarn 86

type WExpr =
  abstract member toZ3Expr: Context -> Expr

and Integer =
  | ExtInteger of WExpr
  | Integer of int64
  | Plus of Integer * Integer
  | Minus of Integer * Integer
  | Times of Integer * Integer
  | Divide of Integer * Integer
  // this terminology comes from https://www.cs.utexas.edu/~EWD/ewd07xx/EWD768.PDF
  | Exceeds of Integer * Integer // >
  | LessThan of Integer * Integer // <
  | AtLeast of Integer * Integer // ≥
  | AtMost of Integer * Integer // ≤
  | IsDivisor of Integer * Integer // ∣

  override this.ToString() : string =
    match this with
    | ExtInteger e -> e.ToString()
    | Integer n -> n.ToString()
    | Plus(x, y) -> $"{x} + {y}"
    | Minus(x, y) -> $"{x} - {y}"
    | Times(x, y) -> $"{x} × {y}"
    | Divide(x, y) -> $"{x} / {y}"
    | Exceeds(x, y) -> $"{x} > {y}"
    | LessThan(x, y) -> $"{x} < {y}"
    | AtLeast(x, y) -> $"{x} ≥ {y}"
    | AtMost(x, y) -> $"{x} ≤ {y}"
    | IsDivisor(x, y) -> $"{x} ∣ {y}"

  static member (~-)(x: Integer) =
    match x with
    | Integer n -> Integer(-n)
    | _ -> Minus(Integer 0, x)

  static member (+)(x: Integer, y: Integer) = Plus(x, y)
  static member (-)(x: Integer, y: Integer) = Minus(x, y)
  static member (*)(x: Integer, y: Integer) = Times(x, y)
  static member (/)(x: Integer, y: Integer) = Divide(x, y)

  interface WExpr with
    member this.toZ3Expr(ctx: Context) : Expr =
      let toExp n = (n :> WExpr).toZ3Expr ctx :?> ArithExpr

      match this with
      | ExtInteger e -> e.toZ3Expr ctx
      | Integer n -> ctx.MkInt n
      | Plus(x, y) -> ctx.MkAdd(toExp x, toExp y)
      | Minus(x, y) -> ctx.MkSub(toExp x, toExp y)
      | Times(x, y) -> ctx.MkMul(toExp x, toExp y)
      | Divide(x, y) -> ctx.MkDiv(toExp x, toExp y)
      | Exceeds(n, m) ->
        let p, q = toExp n, toExp m
        ctx.MkGt(p, q)
      | LessThan(n, m) ->
        let p, q = toExp n, toExp m
        ctx.MkLt(p, q)
      | AtLeast(n, m) ->
        let p, q = toExp n, toExp m
        ctx.MkGe(p, q)
      | AtMost(n, m) ->
        let p, q = toExp n, toExp m
        ctx.MkLe(p, q)
      | IsDivisor(n, m) ->
        // exists x such n*x = m
        let x = ctx.MkIntConst "x" // TODO could this cause a name colision
        let p, q = toExp n, toExp m
        ctx.MkExists([| x |], ctx.MkEq(ctx.MkMul(p, x), q))

and Predicate = WExpr list * Proposition

and Proposition =
  | ExtBoolOp of WExpr // used for wrapping other operators that return booleans besides Equals and Differs (variables, >, <, etc.)
  | True
  | False
  | Equals of WExpr * WExpr
  | Differs of WExpr * WExpr
  | Not of right: Proposition
  | And of left: Proposition * right: Proposition
  | Or of left: Proposition * right: Proposition
  | Equiv of left: Proposition * right: Proposition
  | Inequiv of left: Proposition * right: Proposition
  | Implies of left: Proposition * right: Proposition
  | Follows of left: Proposition * right: Proposition
  | Forall of Predicate
  | Exists of Predicate

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

    let rec binaryOpFormat (pred: int) (symbol: string) (left: Proposition) (right: Proposition) =
      let l, symLeft, predLeft = loop left
      let r, symRight, predRight = loop right

      let x = parenthesize pred symbol predLeft symLeft l
      let y = parenthesize pred symbol predRight symRight r

      $"{x} {symbol} {y}", Some symbol, pred

    and loop (p: Proposition) =
      match p with
      | True -> "true", None, 4
      | False -> "false", None, 4
      | ExtBoolOp x -> $"{x}", None, 4
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

  interface WExpr with
    member this.toZ3Expr(ctx: Context) : Expr =
      let toExp (p: WExpr) = p.toZ3Expr ctx :?> BoolExpr

      let toZ3Pred (vars: List<WExpr>, body) =
        let z3Body = (body :> WExpr).toZ3Expr ctx
        let z3Vars = vars |> List.map (fun v -> v.toZ3Expr ctx) |> List.toArray
        z3Vars, z3Body

      match this with
      | True -> ctx.MkBool true
      | False -> ctx.MkBool false
      | ExtBoolOp b -> b.toZ3Expr ctx
      | Equals(n, m) -> ctx.MkEq(n.toZ3Expr ctx, m.toZ3Expr ctx)
      | Differs(n, m) -> ctx.MkNot(Equals(n, m) |> toExp)
      | Not right -> ctx.MkNot(toExp right)
      | And(left, right) -> ctx.MkAnd(toExp left, toExp right)
      | Or(left, right) -> ctx.MkOr(toExp left, toExp right)
      | Equiv(left, right) -> ctx.MkEq(toExp left, toExp right)
      | Inequiv(left, right) -> toExp (Not(Equiv(left, right)))
      | Implies(left, right) -> ctx.MkImplies(toExp left, toExp right)
      | Follows(left, right) -> ctx.MkImplies(toExp right, toExp left)
      | Forall(vars, body) ->
        let z3Vars, z3Body = toZ3Pred (vars, body)
        ctx.MkForall(z3Vars, z3Body)
      | Exists(vars, body) ->
        let z3Vars, z3Body = toZ3Pred (vars, body)
        ctx.MkExists(z3Vars, z3Body)

and Sequence =
  | Empty
  | ExtSeq of WExpr
  | Cons of WExpr * Sequence
  | Concat of Sequence * Sequence
  | Prefix of Sequence * Sequence
  | Suffix of Sequence * Sequence
  | Length of Sequence

  interface WExpr with
    member this.toZ3Expr(ctx: Context) : Expr =
      let toSeqExpr (x: WExpr) = x.toZ3Expr ctx :?> SeqExpr

      match this with
      | Empty ->
        // Create an empty sequence sort over the uninterpreted element sort "a"
        let elemSort = ctx.MkUninterpretedSort "a"
        let seqSort = ctx.MkSeqSort elemSort
        ctx.MkEmptySeq seqSort
      | ExtSeq e -> e.toZ3Expr ctx
      | Cons(x, xs) ->
        let x = ctx.MkUnit(x.toZ3Expr ctx)
        ctx.MkConcat(x, toSeqExpr xs)
      | Concat(xs, ys) -> ctx.MkConcat(toSeqExpr xs, toSeqExpr ys)
      | Suffix(xs, ys) -> ctx.MkSuffixOf(toSeqExpr xs, toSeqExpr ys)
      | Prefix(xs, ys) -> ctx.MkPrefixOf(toSeqExpr xs, toSeqExpr ys)
      | Length xs -> ctx.MkLength(toSeqExpr xs)


and WSort =
  | WInt
  | WBool
  | WSeq
  | WVarSort of string

  member this.toZ3Sort(ctx: Context) =
    let rec mkSort sort =
      match sort with
      | WInt -> ctx.IntSort :> Sort
      | WBool -> ctx.BoolSort
      | WSeq -> ctx.MkSeqSort(ctx.MkUninterpretedSort "a")
      | WVarSort s -> ctx.MkSeqSort(ctx.MkUninterpretedSort s)

    mkSort this

and Var =
  | Var of string * WSort

  override this.ToString() : string =
    let (Var(v, _)) = this
    v

  interface WExpr with
    member this.toZ3Expr(ctx: Context) =
      let (Var(v, sort)) = this

      let rec mkSort sort =
        match sort with
        | WInt -> ctx.IntSort :> Sort
        | WBool -> ctx.BoolSort
        | WSeq -> ctx.MkSeqSort(ctx.MkUninterpretedSort "a")
        | WVarSort v -> ctx.MkUninterpretedSort v

      ctx.MkConst(v, mkSort sort)

and Function =
  | Fn of string * (WSort list)

  member this.toZ3FnDecl(ctx: Context) =
    let (Fn(name, signature)) = this

    signature
    |> List.map (fun s -> s.toZ3Sort ctx)
    |> function
      | [] -> failwith $"signature cannot be empty, at function {name}"
      | xs ->
        let rev = List.rev xs
        let args = List.tail rev |> List.rev |> List.toArray
        let result = List.head rev
        ctx.MkFuncDecl(name, args, result)

and FnApp =
  | App of Function * (WExpr list)

  interface WExpr with
    member this.toZ3Expr(ctx: Context) =
      let (App(f, args)) = this
      let z3Args = args |> List.map (fun v -> v.toZ3Expr ctx) |> List.toArray

      let funcDecl = f.toZ3FnDecl ctx
      funcDecl.Apply z3Args

  override this.ToString() : string =
    let (App(f, args)) = this
    let argsStr = args |> List.map (fun a -> a.ToString()) |> String.concat ", "

    match f with
    | Fn(name, _) -> $"{name}({argsStr})"

type Calculation =
  { demonstrandum: Law; steps: Step list }

and CheckedCalculation =
  { calculation: Calculation
    error: CalcError option }

and Law =
  { identifier: string
    body: Proposition }

and [<RequireQualifiedAccess>] StepOperator =
  | Equiv
  | Implies
  | Follows
  | Equals

and Step =
  { fromExp: WExpr
    toExp: WExpr
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
  | FailedSteps of list<int * Proposition * CheckResult>
  | WrongEvidence of premise: Proposition * consequence: Proposition
  | InsufficientEvidence of demonstrandum: Proposition
  | RefutedFormula of demonstrandum: Proposition

let private stepToPred (s: Step) =
  let boolStep (t: WExpr, u: WExpr) =
    try
      t :?> Proposition, u :?> Proposition
    with _ ->
      failwith $"not supported step operator for steps {t} and {u}"

  match s.stepOp with
  | StepOperator.Equiv -> (s.fromExp, s.toExp) |> boolStep |> Equiv
  | StepOperator.Follows -> (s.fromExp, s.toExp) |> boolStep |> Follows
  | StepOperator.Implies -> (s.fromExp, s.toExp) |> boolStep |> Implies
  | StepOperator.Equals -> Equals(s.fromExp, s.toExp)


let internal checkPredicate (ctx: Context) (p: Proposition) =
  let solver = ctx.MkSolver()
  let zp = p :> WExpr
  let exp = zp.toZ3Expr ctx :?> BoolExpr
  solver.Add(ctx.MkNot exp)

  match solver.Check() with
  | Status.SATISFIABLE ->
    let r = solver.Model.Evaluate exp
    Refuted(r.ToString())
  | Status.UNSATISFIABLE -> Proved
  | Status.UNKNOWN -> Unknown
  | v -> failwith $"unexpected enum value {v}"

let private checkStepsImpliesDemonstrandum (ctx: Context) (steps: Step list) (demonstrandum: Proposition) =
  match steps with
  | [] ->
    match checkPredicate ctx demonstrandum with
    | Proved -> Ok()
    | Unknown -> Error(InsufficientEvidence demonstrandum)
    | Refuted _ -> Error(RefutedFormula demonstrandum)
  | x :: xs ->
    let r = xs |> List.fold (fun acc x -> And(acc, stepToPred x)) (stepToPred x)
    let evidence = Implies(r, demonstrandum)

    match checkPredicate ctx evidence with
    | Proved -> Ok()
    | _ -> Error(WrongEvidence(r, demonstrandum))

open FsToolkit.ErrorHandling

type ProofLine =
  | Hint of StepOperator * Law list
  | WybeExpr of WExpr
  | Theorem of Law
  | Name of string

let private buildBasic (lines: ProofLine list) =
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
  member _.Yield(s: WExpr) = [ WybeExpr s ]

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
  member _.Yield(x: Proposition) =
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

let private toProposition (x: WExpr) =
  match x with
  | _ when (x :? Var) ->
    let (Var(_, t)) = x :?> Var

    match t with
    | WBool -> ExtBoolOp x
    | _ -> failwith $"expecting boolean variable {x}"
  | _ when (x :? Proposition) -> x :?> Proposition
  | _ -> failwith $"expecting proposition {x}"

let (!) x = Not(toProposition x)

let (===) (x: WExpr) (y: WExpr) = Equiv(toProposition x, toProposition y)

let (!==) x y =
  Inequiv(toProposition x, toProposition y)

let (==>) x y =
  Implies(toProposition x, toProposition y)

let (<==) x y =
  Follows(toProposition x, toProposition y)

let (<&&>) x y = And(toProposition x, toProposition y)
let (<||>) x y = Or(toProposition x, toProposition y)
let ``∀`` vars f = Forall(vars, f)
let ``∃`` vars f = Exists(vars, f)

let axiom name (pred: Proposition) = { identifier = name; body = pred }

let theorem name pred =
  Theorem { identifier = name; body = pred }

let lemma pred =
  Theorem
    { identifier = pred.ToString()
      body = pred }

/// NOTE: redefining the operator `=` in F# is not recommended, but for most Wybe scripts
/// this would make the proofs look closer to syntax we are used to
let (=) x y = Equals(x, y)
let (!=) x y = Differs(x, y)
let ``==`` = LawsCE StepOperator.Equals

let mkBoolVar n = ExtBoolOp(Var(n, WBool))
let mkIntVar x = ExtInteger(Var(x, WInt))
