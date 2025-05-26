module Core

open Microsoft.Z3
#nowarn 86

// precedence of operators
// 0: ≡ ≢
// 1: ⇒  ⇐
// 2: ∧ ∨
// 3: ¬
// 4: = ≠ > < ≤ ≥
// 5: + - × ÷
// 6: # :: ++ ◁ ▷
// 7: variables and other atoms like true, false, ∀, ∃, ϵ

type Symbol = { symbol: string; precedence: int }

type SymbolTree =
  { node: Symbol
    children: SymbolTree list }

  override this.ToString() =
    let parenthesise (parent: Symbol) (child: SymbolTree) =
      if parent.precedence > child.node.precedence then
        $"({child})"
      else
        let chainableOps = Set [ "≡"; "≢"; parent.symbol ]

        let areChainable =
          Set.isSubset (Set [ parent.symbol; child.node.symbol ]) chainableOps

        if not areChainable && parent.precedence = child.node.precedence then
          $"({child})"
        else
          child.ToString()

    match this with
    | { node = x; children = [ left; right ] } -> $"{parenthesise x left} {x.symbol} {parenthesise x right}"
    | { node = x; children = [ right ] } -> $"{x.symbol}{parenthesise x right}"
    | { node = x } -> x.symbol

type BoundVars = Map<string, Expr>

type WExpr =
  abstract member toZ3Expr: Context * BoundVars -> Expr
  abstract member toSymbolTree: unit -> SymbolTree

and Integer =
  | ExtInteger of WExpr
  | Integer of int64
  | UnaryMinus of Integer
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
    (this :> WExpr).toSymbolTree().ToString()

  static member (~-)(x: Integer) =
    match x with
    | Integer n -> Integer -n
    | _ -> UnaryMinus x

  static member (+)(x: Integer, y: Integer) = Plus(x, y)
  static member (-)(x: Integer, y: Integer) = Minus(x, y)
  static member (*)(x: Integer, y: Integer) = Times(x, y)
  static member (/)(x: Integer, y: Integer) = Divide(x, y)

  interface WExpr with
    member this.toSymbolTree() =
      match this with
      | ExtInteger e -> e.toSymbolTree ()
      | Integer i ->
        { node = { symbol = $"{i}"; precedence = 7 }
          children = [] }
      | UnaryMinus n ->
        { node = { symbol = "-"; precedence = 6 }
          children = [ (n :> WExpr).toSymbolTree () ] }
      | Plus(x, y) ->
        { node = { symbol = "+"; precedence = 5 }
          children = [ (x :> WExpr).toSymbolTree (); (y :> WExpr).toSymbolTree () ] }
      | Minus(x, y) ->
        { node = { symbol = "-"; precedence = 5 }
          children = [ (x :> WExpr).toSymbolTree (); (y :> WExpr).toSymbolTree () ] }
      | Times(x, y) ->
        { node = { symbol = "×"; precedence = 5 }
          children = [ (x :> WExpr).toSymbolTree (); (y :> WExpr).toSymbolTree () ] }
      | Divide(x, y) ->
        { node = { symbol = "÷"; precedence = 5 }
          children = [ (x :> WExpr).toSymbolTree (); (y :> WExpr).toSymbolTree () ] }
      | Exceeds(x, y) ->
        { node = { symbol = ">"; precedence = 5 }
          children = [ (x :> WExpr).toSymbolTree (); (y :> WExpr).toSymbolTree () ] }
      | LessThan(x, y) ->
        { node = { symbol = "<"; precedence = 5 }
          children = [ (x :> WExpr).toSymbolTree (); (y :> WExpr).toSymbolTree () ] }
      | AtLeast(x, y) ->
        { node = { symbol = "≥"; precedence = 5 }
          children = [ (x :> WExpr).toSymbolTree (); (y :> WExpr).toSymbolTree () ] }
      | AtMost(x, y) ->
        { node = { symbol = "≤"; precedence = 5 }
          children = [ (x :> WExpr).toSymbolTree (); (y :> WExpr).toSymbolTree () ] }
      | IsDivisor(x, y) ->
        { node = { symbol = "∣"; precedence = 5 }
          children = [ (x :> WExpr).toSymbolTree (); (y :> WExpr).toSymbolTree () ] }

    member this.toZ3Expr(ctx: Context, boundVars: BoundVars) : Expr =
      let toExp n =
        (n :> WExpr).toZ3Expr (ctx, boundVars) :?> ArithExpr

      match this with
      | ExtInteger e -> e.toZ3Expr (ctx, boundVars)
      | Integer n -> ctx.MkInt n
      | UnaryMinus n -> ctx.MkMul(ctx.MkInt -1, toExp n)
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

and Quantifier =
  | Forall
  | Exists

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
  | Quantifier of Quantifier * WExpr list * Proposition

  override this.ToString() : string =
    (this :> WExpr).toSymbolTree().ToString()

  static member extractPatternFromRecurrence(ctx: Context, boundVars: BoundVars, e: WExpr) =

    let rec loop (e: WExpr) =
      match e with
      | :? Proposition as p ->
        match p with
        | ExtBoolOp m -> loop m
        | True
        | False -> [], []
        | Equals(x, y) ->
          let rx = loop x
          let ry = loop y

          match rx, ry with
          | ([], [ _ ]), ([], rs) -> [ rs ], []
          | ([], rs), ([], [ _ ]) -> [ rs ], []
          | _ -> [], []
        | Differs(_, _) -> [], []
        | Not right -> loop right
        | And(left, right)
        | Or(left, right)
        | Equiv(left, right)
        | Inequiv(left, right)
        | Implies(left, right)
        | Follows(left, right) ->
          // I'm assuming here there are no recurrence relations with booleans
          // that recurrence relations are only going to happen with Integers, Sequences
          // and other "non-glue" types
          let l, _ = loop left
          let r, _ = loop right
          l @ r, []
        | Quantifier(_, _, body) -> loop body
      | :? Integer as p ->
        match p with
        | ExtInteger m -> loop m
        | Integer(_) -> [], []
        | UnaryMinus m -> loop m
        | Plus(x, y)
        | Minus(x, y)
        | Times(x, y)
        | Divide(x, y)
        | Exceeds(x, y)
        | LessThan(x, y)
        | AtLeast(x, y)
        | AtMost(x, y)
        | IsDivisor(x, y) ->
          let _, l = loop x
          let _, r = loop y
          [], l @ r
      | :? Sequence as p ->
        match p with
        | Empty -> [], []
        | ExtSeq m -> loop m
        | Length m -> loop m
        | Cons(l, r) ->
          let _, rl = loop l
          let _, rr = loop r
          [], rl @ rr
        | Concat(l, r)
        | Prefix(l, r)
        | Suffix(l, r) ->
          let _, rl = loop l
          let _, rr = loop r
          [], rl @ rr
      | :? FnApp as p ->
        let (App(Fn(f, signature), args)) = p

        let splitLast xs =
          match List.rev xs with
          | y :: ys -> List.rev ys, y
          | _ -> failwith "cannot split empty list"

        let signArgs, ret = splitLast signature
        let z3ArgSorts = signArgs |> List.map (fun a -> a.toZ3Sort ctx) |> List.toArray
        let z3Ret = ret.toZ3Sort ctx
        let decl = ctx.MkFuncDecl(f, z3ArgSorts, z3Ret)

        let exps =
          args |> List.map (fun arg -> arg.toZ3Expr (ctx, boundVars)) |> List.toArray

        [], [ decl.Apply exps ]
      | _ -> [], []

    loop e
    |> fst
    |> List.choose (function | [] -> None | ps -> Some (ctx.MkPattern(List.toArray ps)))
    |> List.toArray

  interface WExpr with
    member this.toSymbolTree() =
      match this with
      | True ->
        { node = { symbol = "true"; precedence = 7 }
          children = [] }
      | False ->
        { node = { symbol = "false"; precedence = 7 }
          children = [] }
      | ExtBoolOp x -> x.toSymbolTree ()
      | Equals(x, y) ->
        { node =
            { symbol = $"{x} = {y}"
              precedence = 4 }
          children = [] }
      | Differs(x, y) ->
        { node =
            { symbol = $"{x} ≠ {y}"
              precedence = 4 }
          children = [] }
      | Not right ->
        { node = { symbol = "¬"; precedence = 3 }
          children = [ (right :> WExpr).toSymbolTree () ] }
      | And(left, right) ->
        { node = { symbol = "∧"; precedence = 2 }
          children = [ (left :> WExpr).toSymbolTree (); (right :> WExpr).toSymbolTree () ] }
      | Or(left, right) ->
        { node = { symbol = "∨"; precedence = 2 }
          children = [ (left :> WExpr).toSymbolTree (); (right :> WExpr).toSymbolTree () ] }
      | Implies(left, right) ->
        { node = { symbol = "⇒"; precedence = 1 }
          children = [ (left :> WExpr).toSymbolTree (); (right :> WExpr).toSymbolTree () ] }
      | Follows(left, right) ->
        { node = { symbol = "⇐"; precedence = 1 }
          children = [ (left :> WExpr).toSymbolTree (); (right :> WExpr).toSymbolTree () ] }
      | Equiv(left, right) ->
        let l = (left :> WExpr).toSymbolTree ()
        let r = (right :> WExpr).toSymbolTree ()

        { node = { symbol = "≡"; precedence = 0 }
          children = [ l; r ] }
      | Inequiv(left, right) ->
        { node = { symbol = "≢"; precedence = 0 }
          children = [ (left :> WExpr).toSymbolTree (); (right :> WExpr).toSymbolTree () ] }
      | Quantifier(q, vars, body) ->
        let symbol =
          match q with
          | Forall -> "∀"
          | Exists -> "∃"

        let vs = vars |> List.map (fun v -> v.ToString()) |> String.concat ","
        let p = (body :> WExpr).toSymbolTree().ToString()

        { node =
            { symbol = $"⟨{symbol}{vs} → {p}⟩" // \langle \rangle ⟨⟩
              precedence = 7 }
          children = [] }


    member this.toZ3Expr(ctx: Context, boundVars: BoundVars) : Expr =
      let toExp (p: WExpr) =
        p.toZ3Expr (ctx, boundVars) :?> BoolExpr

      match this with
      | True -> ctx.MkBool true
      | False -> ctx.MkBool false
      | ExtBoolOp b -> b.toZ3Expr (ctx, boundVars)
      | Equals(n, m) -> ctx.MkEq(n.toZ3Expr (ctx, boundVars), m.toZ3Expr (ctx, boundVars))
      | Differs(n, m) -> ctx.MkNot(Equals(n, m) |> toExp)
      | Not right -> ctx.MkNot(toExp right)
      | And(left, right) -> ctx.MkAnd(toExp left, toExp right)
      | Or(left, right) -> ctx.MkOr(toExp left, toExp right)
      | Equiv(left, right) -> ctx.MkEq(toExp left, toExp right)
      | Inequiv(left, right) -> toExp (Not(Equiv(left, right)))
      | Implies(left, right) -> ctx.MkImplies(toExp left, toExp right)
      | Follows(left, right) -> ctx.MkImplies(toExp right, toExp left)
      | Quantifier(q, vars, body) ->
        let z3Body = (body :> WExpr).toZ3Expr (ctx, boundVars)
        let z3Vars = vars |> List.map (fun v -> v.toZ3Expr (ctx, boundVars)) |> List.toArray

        let rec mkBoundExpr i (v: WExpr) =
          match v with
          | :? Var as v ->
            let (Var(v, s)) = v
            v, ctx.MkBound(uint32 i, s.toZ3Sort ctx)
          | :? Proposition as p ->
            match p with
            | ExtBoolOp e -> mkBoundExpr i e
            | _ -> failwith $"only variables are allowed in quantifier variable section, got {p}"
          | :? Sequence as s ->
            match s with
            | ExtSeq e -> mkBoundExpr i e
            | _ -> failwith $"only variables are allowed in quantifier variable section, got {s}"
          | :? Integer as n ->
            match n with
            | ExtInteger e -> mkBoundExpr i e
            | _ -> failwith $"only variables are allowed in quantifier variable section, got {n}"
          | _ -> failwith $"only variables are allowed in quantifier variable section, got {v}"

        let boundVars =
          vars
          |> List.mapi mkBoundExpr
          |> List.fold (fun m (k, v) -> Map.add k v m) boundVars

        let patterns = Proposition.extractPatternFromRecurrence (ctx, boundVars, body)


        match q with
        | Forall -> ctx.MkForall(z3Vars, body = z3Body, patterns = patterns)
        | Exists -> ctx.MkExists(z3Vars, body = z3Body, patterns = patterns)

and Sequence =
  | Empty
  | ExtSeq of WExpr
  | Cons of WExpr * Sequence
  | Concat of Sequence * Sequence
  | Prefix of Sequence * Sequence
  | Suffix of Sequence * Sequence
  | Length of Sequence

  override this.ToString() : string =
    (this :> WExpr).toSymbolTree().ToString()

  interface WExpr with
    member this.toSymbolTree() : SymbolTree =
      match this with
      | Length x ->
        { node = { symbol = "#"; precedence = 6 }
          children = [ (x :> WExpr).toSymbolTree () ] }
      | Empty ->
        { node = { symbol = "ϵ"; precedence = 7 }
          children = [] }
      | ExtSeq x -> x.toSymbolTree ()
      | Cons(x, xs) ->
        { node = { symbol = "::"; precedence = 6 }
          children = [ x.toSymbolTree (); (xs :> WExpr).toSymbolTree () ] }
      | Concat(xs, ys) ->
        { node = { symbol = "++"; precedence = 6 }
          children = [ (xs :> WExpr).toSymbolTree (); (ys :> WExpr).toSymbolTree () ] }
      | Prefix(xs, ys) ->
        { node = { symbol = "◁"; precedence = 6 }
          children = [ (xs :> WExpr).toSymbolTree (); (ys :> WExpr).toSymbolTree () ] }
      | Suffix(xs, ys) ->
        { node = { symbol = "▷"; precedence = 6 }
          children = [ (xs :> WExpr).toSymbolTree (); (ys :> WExpr).toSymbolTree () ] }

    member this.toZ3Expr(ctx: Context, boundVars: BoundVars) : Expr =
      let toSeqExpr (x: WExpr) = x.toZ3Expr (ctx, boundVars) :?> SeqExpr

      match this with
      | Empty ->
        // Create an empty sequence sort over the uninterpreted element sort "a"
        let elemSort = ctx.MkUninterpretedSort "a"
        let seqSort = ctx.MkSeqSort elemSort
        ctx.MkEmptySeq seqSort
      | ExtSeq e -> e.toZ3Expr (ctx, boundVars)
      | Cons(x, xs) ->
        let x = ctx.MkUnit(x.toZ3Expr (ctx, boundVars))
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
    member this.toSymbolTree() : SymbolTree =
      let (Var(v, _)) = this

      { node = { symbol = v; precedence = 7 }
        children = [] }

    member this.toZ3Expr(ctx: Context, boundVars: BoundVars) =
      let (Var(v, sort)) = this

      let rec mkSort sort =
        match sort with
        | WInt -> ctx.IntSort :> Sort
        | WBool -> ctx.BoolSort
        | WSeq -> ctx.MkSeqSort(ctx.MkUninterpretedSort "a")
        | WVarSort v -> ctx.MkUninterpretedSort v

      match Map.tryFind v boundVars with
      | Some e -> e
      | None -> ctx.MkConst(v, mkSort sort)

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
    member this.toSymbolTree() : SymbolTree =
      let (App(Fn(f, _), args)) = this

      { node = { symbol = f; precedence = 7 }
        children = args |> List.map _.toSymbolTree() }

    member this.toZ3Expr(ctx: Context, boundVars: BoundVars) =
      let (App(f, args)) = this
      let z3Args = args |> List.map (fun v -> v.toZ3Expr (ctx, boundVars)) |> List.toArray

      let funcDecl = f.toZ3FnDecl ctx
      funcDecl.Apply z3Args

  override this.ToString() : string =
    let (App(f, args)) = this
    let argsStr = args |> List.map (fun a -> a.ToString()) |> String.concat ", "

    match f with
    | Fn(name, _) -> $"{name} {argsStr}"

and RecurrencePattern =
  { lhs: FnApp
    recursiveCalls: FnApp list }

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


  let stepProp =
    match s.stepOp with
    | StepOperator.Equiv -> (s.fromExp, s.toExp) |> boolStep |> Equiv
    | StepOperator.Follows -> (s.fromExp, s.toExp) |> boolStep |> Follows
    | StepOperator.Implies -> (s.fromExp, s.toExp) |> boolStep |> Implies
    | StepOperator.Equals -> Equals(s.fromExp, s.toExp)
  match s.laws with
  | [] -> stepProp
  | x::xs ->
    let lawsProp =
      xs |> List.map _.body |> List.fold (fun acc p -> And(acc, p)) x.body
    Implies(lawsProp, stepProp)


let internal checkPredicate (ctx: Context) (p: Proposition) =
  let solver = ctx.MkSolver()
  let zp = p :> WExpr
  let exp = zp.toZ3Expr (ctx, Map.empty) :?> BoolExpr
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
      | _ :: _ -> Error { expected = ExpectingTheorem } // TODO pass a parameter to ExpectingTheorem to
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
  | :? Var as x ->
    let (Var(_, t)) = x

    match t with
    | WBool -> ExtBoolOp x
    | _ -> failwith $"expecting boolean variable {x}"
  | :? Proposition as x -> x
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
let ``∀`` vars f = Quantifier(Forall, vars, f)
let ``∃`` vars f = Quantifier(Exists, vars, f)

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
