module GCL.Interpreter

open GCL.Language

type EvalError =
  | ExpectingValue of Expression
  | CannotApplyBinOp of Operator * Value * Value
  | CannotApplyUnaryOp of UnaryOp * Value

exception EvalErrorEx of EvalError

type ExecError =
  | MalformedAssigment of Identifier list * Expression list
  | AltGuardFailure
  | FindProcFailure of Identifier
  | AssertionFailed of Identifier * Expression

exception ExecException of ExecError

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
  | Equal, Literal(Bool x), Literal(Bool y) -> Literal(Bool(x = y))
  | Equal, Literal(Uint64 x), Literal(Uint64 y) -> Literal(Bool(x = y))
  | Equal, Literal(Int64 x), Literal(Int64 y) -> Literal(Bool(x = y))
  | Equal, Literal x, Literal y -> CannotApplyBinOp(op, x, y) |> EvalErrorEx |> raise
  | Different, Literal(Bool x), Literal(Bool y) -> Literal(Bool(x <> y))
  | Different, Literal(Uint64 x), Literal(Uint64 y) -> Literal(Bool(x <> y))
  | Different, Literal(Int64 x), Literal(Int64 y) -> Literal(Bool(x <> y))
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
  | _, Literal x -> CannotApplyUnaryOp (op,x) |> EvalErrorEx |> raise
  | _, v -> ExpectingValue v |> EvalErrorEx |> raise

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
    procedures: Proc list }

let execAssignment ctx (vars: Identifier list) (expressions: Expression list) =
  let values = ctx.values

  if vars.Length = expressions.Length then
    expressions
    |> List.map (evaluate { varValues = values })
    |> List.zip vars
    |> List.fold
      (fun acc (id, e) ->
        match e with
        | Literal v -> Map.add id v acc
        | _ -> ExpectingValue e |> EvalErrorEx |> raise)
      values
    |> fun vs -> { ctx with values = vs }
  else
    MalformedAssigment(vars, expressions) |> ExecException |> raise

let chooseStatement ctx (xs: Guarded list) =
  xs
  |> List.choose (fun (guard, statement) ->
    match evaluate ctx guard with
    | Literal(Bool true) -> Some statement
    | Literal(Bool false) -> None
    | e -> ExpectingValue e |> EvalErrorEx |> raise)
  |> List.tryHead

let evalAssertion ctx ident e =
  // TODO reduce scope
  match evaluate { varValues = ctx.values } e with
  | Literal (Bool true) ->
    ()
  | e ->
    AssertionFailed (ident, e) |> ExecException |> raise

let rec execAlternative ctx (xs: Guarded list) =
  match chooseStatement { varValues = ctx.values } xs with
  | Some s -> execute ctx s
  | None -> AltGuardFailure |> ExecException |> raise

and execRepetition (xs: Guarded list) ctx =
  match chooseStatement { varValues = ctx.values } xs with
  | Some s -> execute ctx s |> execRepetition xs
  | None -> ctx

and execProc ctx (p: Proc) =
  evalAssertion ctx p.name p.input
  let ctx' = execute ctx p.body
  evalAssertion ctx' p.name p.output
  ctx'

and callProc ctx p =
  ctx.procedures
  |> List.tryFind (fun x -> x.name = p)
  |> function
    | Some p -> execProc ctx p
    | None -> FindProcFailure p |> ExecException |> raise

and execute (ctx: ExecCtx) (s: SourceStatement) =
  // TODO
  match s.statement with
  | Assignment(vars, xs) -> execAssignment ctx vars xs
  | Alternative guards -> execAlternative ctx guards
  | Repetition guards -> execRepetition guards ctx
  | Skip -> ctx
  | SetDeclaration d -> ctx
  | SetTransformation exp -> ctx
  | Call p -> callProc ctx p
  | Composition xs -> xs |> List.fold execute ctx
  | Proc p -> ctx
