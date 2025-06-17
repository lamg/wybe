module Core

open Microsoft.Z3

// This module allows to write expressions made of boolean, integers, sequences and functions; also to write and check proofs made of those expressions.

// sections
// - Symbol Tree
// - WExpr
// - Calculation

// section Symbol Tree
//
// The SymbolTree type allows to build string representations of any WExpr instance
// precedence of operators used in string representations
// 0: ≡ ≢
// 1: ⇒  ⇐
// 2: ∧ ∨
// 3: ¬
// 4: = ≠ > < ≤ ≥
// 5: + - × ÷
// 6: - (unary minus) # :: ++ ◁ ▷
// 7: variables, function applications, and other atoms like true, false, ϵ, expressions inside parenthesis and angle brackets, like universal and existential quantifiers

[<RequireQualifiedAccess>]
type Symbol =
  | Op of symbol: string * precedence: int
  | Var of string
  | Const of string
  | Atom of string

  member this.Precedence =
    match this with
    | Op(_, p) -> p
    | _ -> 7

  member this.Symbol =
    match this with
    | Op(s, _) -> s
    | Var s
    | Atom s
    | Const s -> s

type SymbolTree =
  { node: Symbol
    children: SymbolTree list }

  override this.ToString() =
    let parenthesise (parent: Symbol) (child: SymbolTree) =
      if parent.Precedence > child.node.Precedence then
        $"({child})"
      else
        let chainableOps = Set [ "≡"; "≢"; parent.Symbol ]

        let areChainable =
          Set.isSubset (Set [ parent.Symbol; child.node.Symbol ]) chainableOps

        if not areChainable && parent.Precedence = child.node.Precedence then
          $"({child})"
        else
          child.ToString()

    match this with
    | { node = x; children = [ left; right ] } when x.Symbol = "," ->
      $"{parenthesise x left}{x.Symbol} {parenthesise x right}"
    | { node = x; children = [ left; right ] } -> $"{parenthesise x left} {x.Symbol} {parenthesise x right}"
    | { node = x; children = [ right ] } -> $"{x.Symbol}{parenthesise x right}"
    | { node = x } -> x.Symbol

  member this.existsNode(p: Symbol -> bool) =
    p this.node || this.children |> List.exists (fun c -> c.existsNode p)

// section WExpr (Wybe Expressions)
//
// In Wybe is possible to write formulas consisting of booleans, integeres, sequences and functions.
// Below there's a high level description of types used to represent those formulas
// - Proposition: expression of boolean values and logical operators, including universal and existential quantifiers
// - Integer: expression of integer values, arithmetic operators, and integer predicates (functions from integers to booleans)
// - Sequences: expression of sequence values, including the empty sequence, sequences as successive application of the cons operator; other functions like head, tail, length, isPrefix, isSuffix
// - Functions: declaration of functions as tuples of a name and a signature. Expression of function applications as a tuple of a function declaration and a list of arguments of type WExpr.

// Since Wybe expressions can consist of a mix of boolean operations and any other subexpression that evaluates to a boolean, which could be made of integers, sequences and functions; there is an union case desigend to take any type that implements WExpr. For the Proposition type this is `ExtBoolOp`.
//
// Since not every WExpr evaluates to a boolean some expressions might fail to build at runtime.

type BoundVars = Map<string, Expr>

type WExpr =
  // translates a Wybe expression to a Z3 expression, which is then used to check proofs
  abstract member ToZ3Expr: Context * BoundVars -> Expr
  // translatees a Wybe expression to a symbol tree, which is then used for creating a string representation
  abstract member ToSymbolTree: unit -> SymbolTree

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
    (this :> WExpr).ToSymbolTree().ToString()

  static member (~-)(x: Integer) =
    match x with
    | Integer n -> Integer -n
    | _ -> UnaryMinus x

  static member (+)(x: Integer, y: Integer) = Plus(x, y)
  static member (+)(x: Integer, y: int) = Plus(x, Integer y)
  static member (-)(x: Integer, y: Integer) = Minus(x, y)
  static member (-)(x: Integer, y: int) = Minus(x, Integer y)
  static member (*)(x: Integer, y: Integer) = Times(x, y)
  static member (*)(x: int, y: Integer) = Times(Integer x, y)
  static member (/)(x: Integer, y: Integer) = Divide(x, y)

  interface WExpr with
    member this.ToSymbolTree() =
      match this with
      | ExtInteger e -> e.ToSymbolTree()
      | Integer i ->
        { node = Symbol.Const $"{i}"
          children = [] }
      | UnaryMinus n ->
        { node = Symbol.Op("-", 6)
          children = [ (n :> WExpr).ToSymbolTree() ] }
      | Plus(x, y) ->
        { node = Symbol.Op("+", 5)
          children = [ (x :> WExpr).ToSymbolTree(); (y :> WExpr).ToSymbolTree() ] }
      | Minus(x, y) ->
        { node = Symbol.Op("-", 5)
          children = [ (x :> WExpr).ToSymbolTree(); (y :> WExpr).ToSymbolTree() ] }
      | Times(x, y) ->
        { node = Symbol.Op("×", 5)
          children = [ (x :> WExpr).ToSymbolTree(); (y :> WExpr).ToSymbolTree() ] }
      | Divide(x, y) ->
        { node = Symbol.Op("÷", 5)
          children = [ (x :> WExpr).ToSymbolTree(); (y :> WExpr).ToSymbolTree() ] }
      | Exceeds(x, y) ->
        { node = Symbol.Op(">", 5)
          children = [ (x :> WExpr).ToSymbolTree(); (y :> WExpr).ToSymbolTree() ] }
      | LessThan(x, y) ->
        { node = Symbol.Op("<", 5)
          children = [ (x :> WExpr).ToSymbolTree(); (y :> WExpr).ToSymbolTree() ] }
      | AtLeast(x, y) ->
        { node = Symbol.Op("≥", 5)
          children = [ (x :> WExpr).ToSymbolTree(); (y :> WExpr).ToSymbolTree() ] }
      | AtMost(x, y) ->
        { node = Symbol.Op("≤", 5)
          children = [ (x :> WExpr).ToSymbolTree(); (y :> WExpr).ToSymbolTree() ] }
      | IsDivisor(x, y) ->
        { node = Symbol.Op("∣", 5)
          children = [ (x :> WExpr).ToSymbolTree(); (y :> WExpr).ToSymbolTree() ] }

    member this.ToZ3Expr(ctx: Context, boundVars: BoundVars) : Expr =
      let toExp n =
        (n :> WExpr).ToZ3Expr(ctx, boundVars) :?> ArithExpr

      match this with
      | ExtInteger e -> e.ToZ3Expr(ctx, boundVars)
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
  | ExtProposition of WExpr // used for wrapping other operators that return booleans besides Equals and Differs (variables, >, <, etc.)
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
  | Quantifier of Quantifier * vars: WExpr list * body: Proposition

  override this.ToString() : string =
    (this :> WExpr).ToSymbolTree().ToString()

  /// <summary>extract Z3 pattern from recursive definitions like fib (n+2) = fib(n+1) + fib n</summary>
  /// <param name="ctx"></param>
  /// <param name="boundVars">variables bound by a quantifier</param>
  /// <param name="e">expression containing a recurrence relation</param>
  /// <returns></returns>
  static member extractPatternFromRecurrence(ctx: Context, boundVars: BoundVars, e: WExpr) =
    let rec loop (e: WExpr) =
      match e with
      | :? Proposition as p ->
        match p with
        | ExtProposition m -> loop m
        | True
        | False -> [], []
        | Equals(x, _) ->
          let rx = loop x

          match rx with
          | rs, [] -> rs, []
          | rs, ts -> ts :: rs, []
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
        | Empty _ -> [], []
        | ExtSequence m -> loop m
        | Head m
        | Tail m
        | Length m -> loop m
        | Cons(l, r) ->
          let _, rl = loop l
          let _, rr = loop r
          [], rl @ rr
        | Concat(l, r)
        | IsPrefix(l, r)
        | IsSuffix(l, r) ->
          let _, rl = loop l
          let _, rr = loop r
          [], rl @ rr
      | :? FnApp as p ->

        let splitLast xs =
          match List.rev xs with
          | y :: ys -> List.rev ys, y
          | _ -> failwith "signature cannot be empty"

        let (signArgs: WSort list, ret: WSort) = splitLast p.FnDecl.Signature
        let z3ArgSorts = signArgs |> List.map (fun a -> a.toZ3Sort ctx) |> List.toArray
        let z3Ret = ret.toZ3Sort ctx
        let decl = ctx.MkFuncDecl(p.FnDecl.Name, z3ArgSorts, z3Ret)
        // only if an argument contains a bound variable it should appear in the pattern
        let exps =
          p.Args
          |> List.choose (function
            | arg when arg.ToSymbolTree().existsNode _.IsVar -> Some(arg.ToZ3Expr(ctx, boundVars))
            | _ -> None)

        match exps with
        | _ when exps.Length = signArgs.Length -> [], [ decl.Apply(List.toArray exps) ]
        | _ -> [], []
      | _ -> [], []

    loop e
    |> fst
    |> List.choose (function
      | [] -> None
      | ps -> Some(ctx.MkPattern(List.toArray ps)))
    |> List.toArray

  interface WExpr with
    member this.ToSymbolTree() =
      match this with
      | True ->
        { node = Symbol.Const "true"
          children = [] }
      | False ->
        { node = Symbol.Const "false"
          children = [] }
      | ExtProposition x -> x.ToSymbolTree()
      | Equals(x, y) ->
        { node = Symbol.Op("=", 4)
          children = [ x.ToSymbolTree(); y.ToSymbolTree() ] }
      | Differs(x, y) ->
        { node = Symbol.Op("≠", 4)
          children = [ x.ToSymbolTree(); y.ToSymbolTree() ] }
      | Not right ->
        { node = Symbol.Op("¬", 3)
          children = [ (right :> WExpr).ToSymbolTree() ] }
      | And(left, right) ->
        { node = Symbol.Op("∧", 2)
          children = [ (left :> WExpr).ToSymbolTree(); (right :> WExpr).ToSymbolTree() ] }
      | Or(left, right) ->
        { node = Symbol.Op("∨", 2)
          children = [ (left :> WExpr).ToSymbolTree(); (right :> WExpr).ToSymbolTree() ] }
      | Implies(left, right) ->
        { node = Symbol.Op("⇒", 1)
          children = [ (left :> WExpr).ToSymbolTree(); (right :> WExpr).ToSymbolTree() ] }
      | Follows(left, right) ->
        { node = Symbol.Op("⇐", 1)
          children = [ (left :> WExpr).ToSymbolTree(); (right :> WExpr).ToSymbolTree() ] }
      | Equiv(left, right) ->
        let l = (left :> WExpr).ToSymbolTree()
        let r = (right :> WExpr).ToSymbolTree()

        { node = Symbol.Op("≡", 0)
          children = [ l; r ] }
      | Inequiv(left, right) ->
        { node = Symbol.Op("≢", 0)
          children = [ (left :> WExpr).ToSymbolTree(); (right :> WExpr).ToSymbolTree() ] }
      | Quantifier(q, vars, body) ->
        let symbol =
          match q with
          | Forall -> "∀"
          | Exists -> "∃"

        let vs = vars |> List.map (fun v -> v.ToString()) |> String.concat ","
        let p = (body :> WExpr).ToSymbolTree().ToString()

        { node = Symbol.Atom $"⟨{symbol}{vs} → {p}⟩" // \langle \rangle ⟨⟩
          children = [] }


    member this.ToZ3Expr(ctx: Context, boundVars: BoundVars) : Expr =
      let toExp (p: WExpr) = p.ToZ3Expr(ctx, boundVars) :?> BoolExpr

      match this with
      | True -> ctx.MkBool true
      | False -> ctx.MkBool false
      | ExtProposition b -> b.ToZ3Expr(ctx, boundVars)
      | Equals(n, m) -> ctx.MkEq(n.ToZ3Expr(ctx, boundVars), m.ToZ3Expr(ctx, boundVars))
      | Differs(n, m) -> ctx.MkNot(Equals(n, m) |> toExp)
      | Not right -> ctx.MkNot(toExp right)
      | And(left, right) -> ctx.MkAnd(toExp left, toExp right)
      | Or(left, right) -> ctx.MkOr(toExp left, toExp right)
      | Equiv(left, right) -> ctx.MkEq(toExp left, toExp right)
      | Inequiv(left, right) -> toExp (Not(Equiv(left, right)))
      | Implies(left, right) -> ctx.MkImplies(toExp left, toExp right)
      | Follows(left, right) -> ctx.MkImplies(toExp right, toExp left)
      | Quantifier(q, vars, body) ->
        let rec mkBoundExpr i (v: WExpr) =
          match v with
          | :? Var as v -> v, ctx.MkBound(uint32 i, v.Sort.toZ3Sort ctx)
          | :? Proposition as p ->
            match p with
            | ExtProposition e -> mkBoundExpr i e
            | _ -> failwith $"only variables are allowed in quantifier variable section, got {p}"
          | :? Sequence as s ->
            match s with
            | ExtSequence e -> mkBoundExpr i e
            | _ -> failwith $"only variables are allowed in quantifier variable section, got {s}"
          | :? Integer as n ->
            match n with
            | ExtInteger e -> mkBoundExpr i e
            | _ -> failwith $"only variables are allowed in quantifier variable section, got {n}"
          | _ -> failwith $"only variables are allowed in quantifier variable section, got {v}"

        let z3Vars = vars |> List.map (fun v -> v.ToZ3Expr(ctx, boundVars)) |> List.toArray

        let boundVars =
          vars
          |> List.mapi mkBoundExpr
          |> List.fold (fun m (k, v) -> Map.add k.Name v m) boundVars

        let z3Body = (body :> WExpr).ToZ3Expr(ctx, boundVars)
        let patterns = Proposition.extractPatternFromRecurrence (ctx, boundVars, body)

        match q with
        | Forall -> ctx.MkForall(z3Vars, body = z3Body, patterns = patterns)
        | Exists -> ctx.MkExists(z3Vars, body = z3Body, patterns = patterns)

and Sequence =
  | Empty of WSort
  | ExtSequence of WExpr
  | Cons of WExpr * Sequence
  | Concat of Sequence * Sequence
  | IsPrefix of Sequence * Sequence
  | IsSuffix of Sequence * Sequence
  | Length of Sequence
  | Head of Sequence
  | Tail of Sequence

  override this.ToString() : string =
    (this :> WExpr).ToSymbolTree().ToString()

  interface WExpr with
    member this.ToSymbolTree() : SymbolTree =
      match this with
      | Length x ->
        { node = Symbol.Op("#", 6)
          children = [ (x :> WExpr).ToSymbolTree() ] }
      | Empty _ ->
        { node = Symbol.Const "ϵ"
          children = [] }
      | ExtSequence x -> x.ToSymbolTree()
      | Cons(x, xs) ->
        { node = Symbol.Op("::", 6)
          children = [ x.ToSymbolTree(); (xs :> WExpr).ToSymbolTree() ] }
      | Concat(xs, ys) ->
        { node = Symbol.Op("++", 6)
          children = [ (xs :> WExpr).ToSymbolTree(); (ys :> WExpr).ToSymbolTree() ] }
      | IsPrefix(xs, ys) ->
        { node = Symbol.Op("◁", 6)
          children = [ (xs :> WExpr).ToSymbolTree(); (ys :> WExpr).ToSymbolTree() ] }
      | IsSuffix(xs, ys) ->
        { node = Symbol.Op("▷", 6)
          children = [ (xs :> WExpr).ToSymbolTree(); (ys :> WExpr).ToSymbolTree() ] }
      | Head xs ->
        { node = Symbol.Atom "head"
          children = [ (xs :> WExpr).ToSymbolTree() ] }
      | Tail xs ->
        { node = Symbol.Atom "tail"
          children = [ (xs :> WExpr).ToSymbolTree() ] }

    member this.ToZ3Expr(ctx: Context, boundVars: BoundVars) : Expr =
      let toSeqExpr (x: WExpr) = x.ToZ3Expr(ctx, boundVars) :?> SeqExpr

      match this with
      | Empty s ->
        // Create an empty sequence sort over the uninterpreted element sort "a"
        let elemSort = s.toZ3Sort ctx
        let seqSort = ctx.MkSeqSort elemSort
        ctx.MkEmptySeq seqSort
      | ExtSequence e -> e.ToZ3Expr(ctx, boundVars)
      | Cons(x, xs) ->
        let x = ctx.MkUnit(x.ToZ3Expr(ctx, boundVars))
        ctx.MkConcat(x, toSeqExpr xs)
      | Concat(xs, ys) -> ctx.MkConcat(toSeqExpr xs, toSeqExpr ys)
      | IsSuffix(xs, ys) -> ctx.MkSuffixOf(toSeqExpr xs, toSeqExpr ys)
      | IsPrefix(xs, ys) -> ctx.MkPrefixOf(toSeqExpr xs, toSeqExpr ys)
      | Length xs -> ctx.MkLength(toSeqExpr xs)
      | Head xs -> (toSeqExpr xs).Item(ctx.MkInt 0)
      | Tail xs ->
        let xs = toSeqExpr xs
        let one = ctx.MkInt 1 :> IntExpr
        let tailLength = ctx.MkSub(ctx.MkLength xs, ctx.MkInt 1) :?> IntExpr
        ctx.MkExtract(xs, one, tailLength)

and WSort =
  | WInt
  | WBool
  | WSeq of WSort
  | WVarSort of string

  member this.toZ3Sort(ctx: Context) =
    let rec mkSort sort =
      match sort with
      | WInt -> ctx.IntSort :> Sort
      | WBool -> ctx.BoolSort
      | WSeq s -> ctx.MkSeqSort(mkSort s)
      | WVarSort s -> ctx.MkUninterpretedSort s

    mkSort this

and Var =
  | Var of name: string * sort: WSort

  member this.Name =
    let (Var(name, _)) = this
    name

  member this.Sort: WSort =
    let (Var(_, sort)) = this
    sort

  override this.ToString() : string = this.Name

  interface WExpr with
    member this.ToSymbolTree() : SymbolTree =
      { node = Symbol.Var this.Name
        children = [] }

    member this.ToZ3Expr(ctx: Context, boundVars: BoundVars) =
      let rec mkSort sort =
        match sort with
        | WInt -> ctx.IntSort :> Sort
        | WBool -> ctx.BoolSort
        | WSeq s -> ctx.MkSeqSort(mkSort s)
        | WVarSort v -> ctx.MkUninterpretedSort v

      match Map.tryFind this.Name boundVars with
      | Some e -> e
      | None -> ctx.MkConst(this.Name, mkSort this.Sort)

and FnDecl =
  | FnDecl of name: string * signature: (WSort list)

  member this.Name: string =
    let (FnDecl(name, _)) = this
    name

  member this.Signature =
    let (FnDecl(_, signature)) = this
    signature

and FnApp =
  | FnApp of FnDecl * (WExpr list)

  member this.FnDecl: FnDecl =
    let (FnApp(decl, _)) = this
    decl

  member this.Args: WExpr list =
    let (FnApp(_, args)) = this
    args

  override this.ToString() =
    let args = this.Args |> List.map string |> String.concat ", "
    $"{this.FnDecl.Name}({args})"

  interface WExpr with
    member this.ToSymbolTree() : SymbolTree =
      match this.Args with
      | _ :: _ ->
        let rargs = List.rev this.Args
        let x, xs = List.head rargs, List.tail rargs

        let argTree =
          xs
          |> List.fold
            (fun acc x ->
              { node = Symbol.Op(",", 0)
                children = [ x.ToSymbolTree(); acc ] })
            (x.ToSymbolTree())

        { node = Symbol.Atom this.FnDecl.Name
          children = [ argTree ] }
      | [] ->
        { node = Symbol.Atom this.FnDecl.Name
          children = [] }

    member this.ToZ3Expr(ctx: Context, boundVars: BoundVars) =
      let toZ3FnDecl (signature: WSort list) =
        signature
        |> List.map (fun s -> s.toZ3Sort ctx)
        |> function
          | [] -> failwith $"signature cannot be empty, at function {this.FnDecl.Name}"
          | xs ->
            let rev = List.rev xs
            let args = List.tail rev |> List.rev |> List.toArray
            let result = List.head rev
            ctx.MkFuncDecl(this.FnDecl.Name, args, result)

      let z3Args =
        this.Args |> List.map (fun v -> v.ToZ3Expr(ctx, boundVars)) |> List.toArray

      let funcDecl = toZ3FnDecl this.FnDecl.Signature
      funcDecl.Apply z3Args

// section Calculation
//
// A calculation consists of a demonstradum (a formula to prove) and a sequence of transformations that provide
// evidence for checking the validity of the demonstrandumd.
//
// Calculations are implemented as a computation expression where instances of the type ProofLine are yielded
// and parsed to compose a valid instance of the Calculation type. This is implemented by the CalculationCE type, which
// also includes a Run member that checks the proof, producing a CheckedCalculation value.
//
// The LawsCE is also a computation expression which allows to extract valid Wybe expressions from axioms and
// theorems (from successfully checked calculations also in Wybe) useful as intermediate step in a proof.

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
  | WrongEvidence of counterExample: string * premise: Proposition list * consequence: Proposition
  | InsufficientEvidence of assumptions: Proposition list * demonstrandum: Proposition
  | RefutedFormula of demonstrandum: Proposition

let internal stepToProposition (s: Step) =
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

let internal checkAssuming (ctx: Context) (assumptions: Proposition list) (p: Proposition) =
  let solver = ctx.MkSolver()

  assumptions
  |> List.iter (fun l -> solver.Assert((l :> WExpr).ToZ3Expr(ctx, Map.empty) :?> BoolExpr))

  let exp = ((p :> WExpr).ToZ3Expr(ctx, Map.empty)) :?> BoolExpr
  solver.Assert(ctx.MkNot exp)

  match solver.Check() with
  | Status.SATISFIABLE ->
    let r = solver.Model.Evaluate exp
    Refuted(r.ToString())
  | Status.UNSATISFIABLE -> Proved
  | Status.UNKNOWN -> Unknown
  | v -> failwith $"unexpected enum value {v}"

let internal checkStep (ctx: Context) (s: Step) =
  let assumptions = s.laws |> List.map _.body
  let stepProp = stepToProposition s
  checkAssuming ctx assumptions stepProp

let private checkStepsImpliesDemonstrandum (ctx: Context) (steps: Step list) (demonstrandum: Proposition) =
  let assumptions = steps |> List.map stepToProposition

  match checkAssuming ctx assumptions demonstrandum with
  | Proved -> Ok()
  | Refuted counterExample -> Error(WrongEvidence(counterExample, assumptions, demonstrandum))
  | Unknown -> Error(InsufficientEvidence(assumptions, demonstrandum))

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
      let cfg = System.Collections.Generic.Dictionary<string, string>()
      cfg.Add("model", "true")
      let ctx = new Context(cfg)

      let failed =
        calc.steps
        |> List.mapi (fun i s ->
          match checkStep ctx s with
          | Proved -> []
          | e -> [ i, stepToProposition s, e ])
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

let ``==`` = LawsCE StepOperator.Equals
