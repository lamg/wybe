module Core

open Microsoft.Z3

// This module allows to write expressions made of boolean, integers, sequences and functions; also to write and check proofs made of those expressions.

// sections
// - Symbol Tree
// - WExpr
// - Calculation

// Symbol Tree
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
type Expected =
  | Step
  | Hint
  | Theorem

[<RequireQualifiedAccess>]
type CheckResult =
  | Proved
  | Refuted of string
  | Unknown

type WybeError =
  | InvalidSymbolTree of nodeChildrenAmount: int
  | EmptySignature of functionName: string
  | NonVarInQuantifiedVars of var: string
  | StepExprShouldBePropositions of string * string
  | CannotExtractLawFromFailedProof of string
  | FailedParsing of lineNo: int * lines: string list * Expected
  | FailedSteps of list<int * string * CheckResult>
  | WrongEvidence of counterExample: string * premise: string list * consequence: string
  | InsufficientEvidence of assumptions: string list * demonstrandum: string
  | RefutedFormula of demonstrandum: string

type WybeException(e: WybeError) =
  inherit System.Exception(e.ToString())

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

[<RequireQualifiedAccess>]
type SymbolTree =
  | Node of value: Symbol * children: SymbolTree list

  member this.Value =
    let (Node(value, _)) = this
    value

  member this.Children =
    let (Node(_, children)) = this
    children

  override this.ToString() =
    let parenthesise (parent: Symbol) (child: SymbolTree) =
      if parent.Precedence > child.Value.Precedence then
        $"({child})"
      else
        let chainableOps = Set [ "≡"; "≢"; parent.Symbol ]

        let areChainable =
          Set.isSubset (Set [ parent.Symbol; child.Value.Symbol ]) chainableOps

        if not areChainable && parent.Precedence = child.Value.Precedence then
          $"({child})"
        else
          child.ToString()

    match this with
    | Node(x, [ left; right ]) when x.Symbol = "," -> $"{parenthesise x left}{x.Symbol} {parenthesise x right}"
    | Node(x, [ left; right ]) -> $"{parenthesise x left} {x.Symbol} {parenthesise x right}"
    | Node(x, [ right ]) -> $"{x.Symbol}{parenthesise x right}"
    | Node(x, []) -> x.Symbol
    | Node(_, xs) -> raise (WybeException(InvalidSymbolTree xs.Length))

  member this.existsNode(p: Symbol -> bool) =
    p this.Value || this.Children |> List.exists (fun c -> c.existsNode p)

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
      let toTree (e: WExpr) = e.ToSymbolTree()

      match this with
      | ExtInteger e -> e.ToSymbolTree()
      | Integer i -> SymbolTree.Node(Symbol.Const $"{i}", [])
      | UnaryMinus n -> SymbolTree.Node(Symbol.Op("-", 6), [ toTree n ])
      | Plus(x, y) -> SymbolTree.Node(Symbol.Op("+", 5), [ toTree x; toTree y ])
      | Minus(x, y) -> SymbolTree.Node(Symbol.Op("-", 5), [ toTree x; toTree y ])
      | Times(x, y) -> SymbolTree.Node(Symbol.Op("×", 5), [ toTree x; toTree y ])
      | Divide(x, y) -> SymbolTree.Node(Symbol.Op("÷", 5), [ toTree x; toTree y ])
      | Exceeds(x, y) -> SymbolTree.Node(Symbol.Op(">", 5), [ toTree x; toTree y ])
      | LessThan(x, y) -> SymbolTree.Node(Symbol.Op("<", 5), [ toTree x; toTree y ])
      | AtLeast(x, y) -> SymbolTree.Node(Symbol.Op("≥", 5), [ toTree x; toTree y ])
      | AtMost(x, y) -> SymbolTree.Node(Symbol.Op("≤", 5), [ toTree x; toTree y ])
      | IsDivisor(x, y) -> SymbolTree.Node(Symbol.Op("∣", 5), [ toTree x; toTree y ])

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
        let extractVar =
          function
          | ExtInteger a ->
            match a with
            | :? Var as z -> Some z.Name
            | _ -> None
          | _ -> None

        let varSet = [ n; m ] |> List.choose extractVar |> Set
        let x = varSet - Set [ "x"; "y"; "z" ] |> Set.toList |> List.head
        // x ∉ { n, m }

        let x = ctx.MkIntConst x
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

  // recursive definitions like ⟨∀n → fib (n+2) = fib(n+1) + fib n⟩ need to be converted to Z3 expressions
  // specifying which terms need to be unfolded, by providing a *pattern*.
  // In this case the pattern is [|fib (n+1); fib n|]. This is implemented by the extractPatternFromRecurrence
  // function by visiting the WExpr tree and collecting function applications, FnApp instances, and converting them
  // to their equivalent in Z3, to finally create a Z3 pattern with them.

  /// <summary>extract Z3 pattern from recursive definitions like fib (n+2) = fib(n+1) + fib n</summary>
  /// <param name="ctx"></param>
  /// <param name="boundVars">variables bound by a quantifier</param>
  /// <param name="e">expression containing a recurrence relation</param>
  /// <returns></returns>
  static member internal extractPatternFromRecurrence(ctx: Context, boundVars: BoundVars, e: WExpr) =
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
          | _ -> raise (WybeException(EmptySignature p.FnDecl.Name))

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
      let toTree (e: WExpr) = e.ToSymbolTree()

      match this with
      | True -> SymbolTree.Node(Symbol.Const "true", [])
      | False -> SymbolTree.Node(Symbol.Const "false", [])
      | ExtProposition x -> x.ToSymbolTree()
      | Equals(x, y) -> SymbolTree.Node(Symbol.Op("=", 4), [ toTree x; toTree y ])
      | Differs(x, y) -> SymbolTree.Node(Symbol.Op("≠", 4), [ toTree x; toTree y ])
      | Not right -> SymbolTree.Node(Symbol.Op("¬", 3), [ toTree right ])
      | And(left, right) -> SymbolTree.Node(Symbol.Op("∧", 2), [ toTree left; toTree right ])
      | Or(left, right) -> SymbolTree.Node(Symbol.Op("∨", 2), [ toTree left; toTree right ])
      | Implies(left, right) -> SymbolTree.Node(Symbol.Op("⇒", 1), [ toTree left; toTree right ])
      | Follows(left, right) -> SymbolTree.Node(Symbol.Op("⇐", 1), [ toTree left; toTree right ])
      | Equiv(left, right) ->
        let l = (left :> WExpr).ToSymbolTree()
        let r = (right :> WExpr).ToSymbolTree()

        SymbolTree.Node(Symbol.Op("≡", 0), [ l; r ])
      | Inequiv(left, right) -> SymbolTree.Node(Symbol.Op("≢", 0), [ toTree left; toTree right ])
      | Quantifier(q, vars, body) ->
        let symbol =
          match q with
          | Forall -> "∀"
          | Exists -> "∃"

        let vs = vars |> List.map (fun v -> v.ToString()) |> String.concat ","
        let p = (body :> WExpr).ToSymbolTree().ToString()

        SymbolTree.Node(Symbol.Atom $"⟨{symbol}{vs} → {p}⟩", [])


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
            | _ -> raise (WybeException(NonVarInQuantifiedVars(string v)))
          | :? Sequence as s ->
            match s with
            | ExtSequence e -> mkBoundExpr i e
            | _ -> raise (WybeException(NonVarInQuantifiedVars(string v)))
          | :? Integer as n ->
            match n with
            | ExtInteger e -> mkBoundExpr i e
            | _ -> raise (WybeException(NonVarInQuantifiedVars(string v)))
          | _ -> raise (WybeException(NonVarInQuantifiedVars(string v)))

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
      let toTree (e: WExpr) = e.ToSymbolTree()

      match this with
      | Length x -> SymbolTree.Node(Symbol.Op("#", 6), [ toTree x ])
      | Empty _ -> SymbolTree.Node(Symbol.Const "ϵ", [])
      | ExtSequence x -> x.ToSymbolTree()
      | Cons(x, xs) -> SymbolTree.Node(Symbol.Op("::", 6), [ toTree x; toTree xs ])
      | Concat(xs, ys) -> SymbolTree.Node(Symbol.Op("++", 6), [ toTree xs; toTree ys ])
      | IsPrefix(xs, ys) -> SymbolTree.Node(Symbol.Op("◁", 6), [ toTree xs; toTree ys ])
      | IsSuffix(xs, ys) -> SymbolTree.Node(Symbol.Op("▷", 6), [ toTree xs; toTree ys ])
      | Head xs -> SymbolTree.Node(Symbol.Atom "head", [ toTree xs ])
      | Tail xs -> SymbolTree.Node(Symbol.Atom "tail", [ toTree xs ])

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
      SymbolTree.Node(Symbol.Var this.Name, [])

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
          |> List.fold (fun acc x -> SymbolTree.Node(Symbol.Op(",", 0), [ x.ToSymbolTree(); acc ])) (x.ToSymbolTree())

        SymbolTree.Node(Symbol.Atom this.FnDecl.Name, [ argTree ])
      | [] -> SymbolTree.Node(Symbol.Atom this.FnDecl.Name, [])

    member this.ToZ3Expr(ctx: Context, boundVars: BoundVars) =
      let toZ3FnDecl (signature: WSort list) =
        signature
        |> List.map (fun s -> s.toZ3Sort ctx)
        |> function
          | [] -> raise (WybeException(EmptySignature this.FnDecl.Name))
          | xs ->
            let rev = List.rev xs
            let args = List.tail rev |> List.rev |> List.toArray
            let result = List.head rev
            ctx.MkFuncDecl(this.FnDecl.Name, args, result)

      let z3Args =
        this.Args |> List.map (fun v -> v.ToZ3Expr(ctx, boundVars)) |> List.toArray

      let funcDecl = toZ3FnDecl this.FnDecl.Signature
      funcDecl.Apply z3Args

// Calculation
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
  | Calculation of demonstradum: Law * steps: Step list

  member this.Demonstrandum =
    let (Calculation(demonstrandum, _)) = this
    demonstrandum

  member this.Steps =
    let (Calculation(_, steps)) = this
    steps

and CheckedCalculation =
  | CheckedCalculation of calculation: Calculation * error: WybeError option

  member this.Calculation =
    let (CheckedCalculation(calculation, _)) = this
    calculation

  member this.Error =
    let (CheckedCalculation(_, error)) = this
    error

and Law =
  | Law of identifier: string * body: Proposition

  member this.Identifier =
    let (Law(identifier, _)) = this
    identifier

  member this.Body =
    let (Law(_, body)) = this
    body

and [<RequireQualifiedAccess>] StepOperator =
  | Equiv
  | Implies
  | Follows
  | Equals

and Step =
  | Step of fromExp: WExpr * stepOp: StepOperator * laws: Law list * toStep: WExpr

  member this.FromExpr =
    let (Step(fromExpr, _, _, _)) = this
    fromExpr

  member this.ToExpr =
    let (Step(_, _, _, toExpr)) = this
    toExpr

  member this.StepOp =
    let (Step(_, stepOp, _, _)) = this
    stepOp

  member this.Laws =
    let (Step(_, _, laws, _)) = this
    laws

let internal stepToProposition (s: Step) =
  let boolStep (t: WExpr, u: WExpr) =
    try
      t :?> Proposition, u :?> Proposition
    with _ ->
      raise (WybeException(StepExprShouldBePropositions(string t, string u)))

  match s.StepOp with
  | StepOperator.Equiv -> Equiv(boolStep (s.FromExpr, s.ToExpr))
  | StepOperator.Follows -> Follows(boolStep (s.FromExpr, s.ToExpr))
  | StepOperator.Implies -> Implies(boolStep (s.FromExpr, s.ToExpr))
  | StepOperator.Equals -> Equals(s.FromExpr, s.ToExpr)

let internal checkAssuming (ctx: Context) (assumptions: Proposition list) (p: Proposition) =
  let solver = ctx.MkSolver()

  assumptions
  |> List.iter (fun l -> solver.Assert((l :> WExpr).ToZ3Expr(ctx, Map.empty) :?> BoolExpr))

  let exp = ((p :> WExpr).ToZ3Expr(ctx, Map.empty)) :?> BoolExpr
  solver.Assert(ctx.MkNot exp)

  match solver.Check() with
  | Status.SATISFIABLE ->
    let r = solver.Model.Evaluate exp
    CheckResult.Refuted(r.ToString())
  | Status.UNSATISFIABLE -> CheckResult.Proved
  | Status.UNKNOWN -> CheckResult.Unknown
  | v -> failwith $"unexpected Z3 solver result {v}"

let internal checkStep (ctx: Context) (s: Step) : CheckResult =
  let assumptions = s.Laws |> List.map _.Body
  let stepProp = stepToProposition s
  checkAssuming ctx assumptions stepProp

let private checkStepsImpliesDemonstrandum (ctx: Context) (steps: Step list) (demonstrandum: Proposition) =
  let assumptions = steps |> List.map stepToProposition

  match checkAssuming ctx assumptions demonstrandum with
  | CheckResult.Proved -> Ok()
  | CheckResult.Refuted counterExample ->
    Error(WrongEvidence(counterExample, List.map string assumptions, string demonstrandum))
  | CheckResult.Unknown -> Error(InsufficientEvidence(List.map string assumptions, string demonstrandum))

type ProofLine =
  | Hint of StepOperator * Law list
  | WybeExpr of WExpr
  | Theorem of Law

let private parseProofLines (lines: ProofLine list) =
  let rec fixedPoint (f: 'b -> 'b option) (state: 'b) =
    match f state with
    | Some x -> fixedPoint f x
    | None -> state

  let buildStep =
    function
    | steps, lines ->
      match lines with
      | [ WybeExpr f; Hint(op, laws); WybeExpr t ] -> Some(Step(f, op, laws, t) :: steps, [])
      | WybeExpr f :: Hint(op, laws) :: WybeExpr t :: lines -> Some(Step(f, op, laws, t) :: steps, WybeExpr t :: lines)
      | _ -> None

  let theorem, lines =
    match lines with
    | Theorem t :: xs -> t, xs
    | _ -> raise (WybeException(FailedParsing(1, List.map string lines, Expected.Theorem)))

  // syntax of lines: theorem (expr hint expr)*
  let steps, remainingLines = fixedPoint buildStep ([], lines)
  let parsedLines = lines.Length - remainingLines.Length

  match remainingLines with
  | [] -> ()
  | WybeExpr _ :: _ -> raise (WybeException(FailedParsing(parsedLines, List.map string lines, Expected.Hint)))
  | _ :: _ -> raise (WybeException(FailedParsing(parsedLines, List.map string lines, Expected.Step)))

  Calculation(theorem, List.rev steps)

let private parseAndCheck (lines: ProofLine list) =
  let calc = parseProofLines lines
  let cfg = System.Collections.Generic.Dictionary<string, string>()
  cfg.Add("model", "true")
  let ctx = new Context(cfg)

  let failed =
    calc.Steps
    |> List.mapi (fun i s ->
      match checkStep ctx s with
      | CheckResult.Proved -> []
      | e -> [ i, string (stepToProposition s), e ])
    |> List.concat

  let error =
    match failed with
    | [] ->
      match checkStepsImpliesDemonstrandum ctx calc.Steps calc.Demonstrandum.Body with
      | Ok() -> None
      | Error e -> Some e
    | _ -> Some(FailedSteps failed)

  CheckedCalculation(calc, error)

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
    // TODO catch exceptions and add message to the message stack
    // coming for proof lines generated by failing proofs
    parseAndCheck xs


let proof = CalculationCE()

type LawsCE(op: StepOperator) =
  member _.Yield(x: Proposition) = [ Law(string x, x) ]

  member _.Yield(x: Law) = [ x ]
  member _.Yield(xs: Law list) = xs

  member _.Yield(x: CheckedCalculation) =
    match x.Error with
    | None -> [ x.Calculation.Demonstrandum ]
    | Some e -> raise (WybeException(CannotExtractLawFromFailedProof(string e)))

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
