module GCL.Interpreter

open GCL.Language

type EvalError =
  | ExpectingType of Identifier * Identifier
  | UnknownExpression
  | ExpectingValue of Expression
  | Undefined of Identifier
  | CannotApplyBinOp of Operator * Value * Value
  | CannotApplyUnaryOp of UnaryOp * Expression
  | ConflictingValues of Identifier * List<Value>

exception EvalErrorEx of EvalError

type Context = { varValues: Map<Identifier, Value> }

let reduceBinary (op: Operator) (left: Expression) (right: Expression) =
  match op, left, right with
  // number -> number
  | Plus, Literal(Uint64 x), Literal(Uint64 y) -> Literal(Uint64(x + y))
  | Minus, Literal(Uint64 x), Literal(Uint64 y) -> Literal(Uint64(x - y))
  | Times, Literal(Uint64 x), Literal(Uint64 y) -> Literal(Uint64(x * y))
  | Divide, Literal(Uint64 x), Literal(Uint64 y) -> Literal(Uint64(x / y))
  | Plus, Literal(Int64 x), Literal(Int64 y) -> Literal(Int64(x + y))
  | Minus, Literal(Int64 x), Literal(Int64 y) -> Literal(Int64(x - y))
  | Times, Literal(Int64 x), Literal(Int64 y) -> Literal(Int64(x * y))
  | Divide, Literal(Int64 x), Literal(Int64 y) -> Literal(Int64(x / y))
  | Plus, Literal x, Literal y -> CannotApplyBinOp(op, x, y) |> EvalErrorEx |> raise
  | Minus, Literal x, Literal y -> CannotApplyBinOp(op, x, y) |> EvalErrorEx |> raise
  | Times, Literal x, Literal y -> CannotApplyBinOp(op, x, y) |> EvalErrorEx |> raise
  | Divide, Literal x, Literal y -> CannotApplyBinOp(op, x, y) |> EvalErrorEx |> raise
  // bool -> bool
  | And, Literal(Bool x), Literal(Bool y) -> Literal(Bool(x && y))
  | Or, Literal(Bool x), Literal(Bool y) -> Literal(Bool(x || y))
  | BoolEqual, Literal(Bool x), Literal(Bool y) -> Literal(Bool(x = y))
  | BoolDifferent, Literal(Bool x), Literal(Bool y) -> Literal(Bool(x <> y))
  | Implies, Literal(Bool x), Literal(Bool y) -> Literal(Bool(not x || y))
  | Follows, Literal(Bool x), Literal(Bool y) -> Literal(Bool(x || not y))
  | And, Literal x, Literal y -> CannotApplyBinOp(op, x, y) |> EvalErrorEx |> raise
  | Or, Literal x, Literal y -> CannotApplyBinOp(op, x, y) |> EvalErrorEx |> raise
  | BoolEqual, Literal x, Literal y -> CannotApplyBinOp(op, x, y) |> EvalErrorEx |> raise
  | BoolDifferent, Literal x, Literal y -> CannotApplyBinOp(op, x, y) |> EvalErrorEx |> raise
  // x -> bool
  | Equal, Literal (Bool x), Literal (Bool y) -> Literal(Bool(x = y))
  | Equal, Literal (Uint64 x), Literal (Uint64 y) -> Literal(Bool(x = y))
  | Equal, Literal (Int64 x), Literal (Int64 y) -> Literal(Bool(x = y))
  | Equal, Literal x, Literal y -> CannotApplyBinOp(op, x, y) |> EvalErrorEx |> raise
  | Different, Literal (Bool x), Literal (Bool y) -> Literal(Bool(x <> y))
  | Different, Literal (Uint64 x), Literal (Uint64 y) -> Literal(Bool(x <> y))
  | Different, Literal (Int64 x), Literal (Int64 y) -> Literal(Bool(x <> y))
  | Different, Literal x, Literal y -> CannotApplyBinOp(op, x, y) |> EvalErrorEx |> raise
  // number -> bool
  | Gt, Literal(Uint64 x), Literal(Uint64 y) -> Literal(Bool(x > y))
  | Lt, Literal(Uint64 x), Literal(Uint64 y) -> Literal(Bool(x < y))
  | Gte, Literal(Uint64 x), Literal(Uint64 y) -> Literal(Bool(x >= y))
  | Lte, Literal(Uint64 x), Literal(Uint64 y) -> Literal(Bool(x <= y))
  | Gt, Literal(Int64 x), Literal(Int64 y) -> Literal(Bool(x > y))
  | Lt, Literal(Int64 x), Literal(Int64 y) -> Literal(Bool(x < y))
  | Gte, Literal(Int64 x), Literal(Int64 y) -> Literal(Bool(x >= y))
  | Lte, Literal(Int64 x), Literal(Int64 y) -> Literal(Bool(x <= y))
  | Gt, Literal x, Literal y -> CannotApplyBinOp(op, x, y) |> EvalErrorEx |> raise
  | Lt, Literal x, Literal y -> CannotApplyBinOp(op, x, y) |> EvalErrorEx |> raise
  | Gte, Literal x, Literal y -> CannotApplyBinOp(op, x, y) |> EvalErrorEx |> raise
  | Lte, Literal x, Literal y -> CannotApplyBinOp(op, x, y) |> EvalErrorEx |> raise
  | _ -> Binary(op, left, right)

let rec evalBinary (ctx: Context) (op: Operator) (left: Expression) (right: Expression) =
  let l = evaluate ctx left
  let r = evaluate ctx right
  reduceBinary op l r

and evalUnary (ctx: Context) (op: UnaryOp) (right: Expression) =
  match op, evaluate ctx right with
  | Not, Literal(Bool v) -> Literal(Bool(not v))
  | UnaryMinus, Literal(Int64 v) -> Literal(Int64 -v)
  | _, v -> CannotApplyUnaryOp(op, v) |> EvalErrorEx |> raise

and evaluate (ctx: Context) (expr: Expression) =
  match expr with
  | Literal _ -> expr
  | Variable id ->
    match Map.tryFind id ctx.varValues with
    | Some m -> Literal m
    | _ -> expr
  | Binary(op, left, right) -> evalBinary ctx op left right
  | Unary(op, right) -> evalUnary ctx op right

type ExecCtx =
  { values: Map<Identifier, Value>
    data: SetDeclaration list
    procedures: Proc list
    statements: Statement array
    current: int
    returnVars: Identifier list }

let execute (ctx: ExecCtx) =
  let current = ctx.statements[ctx.current]

  // TODO
  match current with
  | Assignment(vars, exprs) -> ctx
  | Alternative guards -> ctx
  | Repetition guards -> ctx
  | Skip -> ctx
  | SetDeclaration d -> ctx
  | SetTransformation exp -> ctx
  | Call p -> ctx
  | Composition xs -> ctx
  | Proc p -> ctx
