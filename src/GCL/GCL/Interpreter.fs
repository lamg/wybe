module GCL.Interpreter

open GCL.Language

type Error =
  | ExpectingType of Identifier * Identifier
  | UnknownExpression
  | ExpectingValue of Expression
  | Undefined of Identifier
  | CannotApplyBinOp of Operator * Expression * Expression
  | CannotApplyUnaryOp of UnaryOp * Expression

type Context =
  { values: Map<Identifier, Value>
    expr: Expression
    error: Error option }

let evalVariable (ctx: Context) (id: Identifier) =
  if ctx.values.ContainsKey id then
    { ctx with
        expr = Literal ctx.values[id] }
  else
    { ctx with error = Some(Undefined id) }

let rec evalBinary (ctx: Context) (op: Operator) (left: Expression) (right: Expression) =
  let lCtx = evaluate { ctx with expr = left }
  let rCtx = evaluate { lCtx with expr = right }

  match op, lCtx.expr, rCtx.expr with
  | Plus, Literal(Uint64 x), Literal(Uint64 y) ->
    { rCtx with
        expr = Literal(Uint64(x + y)) }
  | Minus, Literal(Uint64 x), Literal(Uint64 y) ->
    { rCtx with
        expr = Literal(Uint64(x - y)) }
  | Times, Literal(Uint64 x), Literal(Uint64 y) ->
    { rCtx with
        expr = Literal(Uint64(x * y)) }
  | Divide, Literal(Uint64 x), Literal(Uint64 y) ->
    { rCtx with
        expr = Literal(Uint64(x / y)) }
  | Plus, Literal(Int64 x), Literal(Int64 y) ->
    { rCtx with
        expr = Literal(Int64(x + y)) }
  | Minus, Literal(Int64 x), Literal(Int64 y) ->
    { rCtx with
        expr = Literal(Int64(x - y)) }
  | Times, Literal(Int64 x), Literal(Int64 y) ->
    { rCtx with
        expr = Literal(Int64(x * y)) }
  | Divide, Literal(Int64 x), Literal(Int64 y) ->
    { rCtx with
        expr = Literal(Int64(x / y)) }
  | And, Literal(Bool x), Literal(Bool y) ->
    { rCtx with
        expr = Literal(Bool(x && y)) }
  | Or, Literal(Bool x), Literal(Bool y) ->
    { rCtx with
        expr = Literal(Bool(x || y)) }
  | BoolEqual, Literal(Bool x), Literal(Bool y) ->
    { rCtx with
        expr = Literal(Bool(x = y)) }
  | BoolDifferent, Literal(Bool x), Literal(Bool y) ->
    { rCtx with
        expr = Literal(Bool(x <> y)) }
  | Implies, Literal(Bool x), Literal(Bool y) ->
    { rCtx with
        expr = Literal(Bool(not x || y)) }
  | Follows, Literal(Bool x), Literal(Bool y) ->
    { rCtx with
        expr = Literal(Bool(x || not y)) }
  | Equal, Literal(Uint64 x), Literal(Uint64 y) ->
    { rCtx with
        expr = Literal(Bool(x = y)) }
  | Different, Literal(Uint64 x), Literal(Uint64 y) ->
    { rCtx with
        expr = Literal(Bool(x <> y)) }
  | Gt, Literal(Uint64 x), Literal(Uint64 y) ->
    { rCtx with
        expr = Literal(Bool(x > y)) }
  | Lt, Literal(Uint64 x), Literal(Uint64 y) ->
    { rCtx with
        expr = Literal(Bool(x < y)) }
  | Gte, Literal(Uint64 x), Literal(Uint64 y) ->
    { rCtx with
        expr = Literal(Bool(x >= y)) }
  | Lte, Literal(Uint64 x), Literal(Uint64 y) ->
    { rCtx with
        expr = Literal(Bool(x <= y)) }
  | Equal, Literal(Int64 x), Literal(Int64 y) ->
    { rCtx with
        expr = Literal(Bool(x = y)) }
  | Different, Literal(Int64 x), Literal(Int64 y) ->
    { rCtx with
        expr = Literal(Bool(x <> y)) }
  | Gt, Literal(Int64 x), Literal(Int64 y) ->
    { rCtx with
        expr = Literal(Bool(x > y)) }
  | Lt, Literal(Int64 x), Literal(Int64 y) ->
    { rCtx with
        expr = Literal(Bool(x < y)) }
  | Gte, Literal(Int64 x), Literal(Int64 y) ->
    { rCtx with
        expr = Literal(Bool(x >= y)) }
  | Lte, Literal(Int64 x), Literal(Int64 y) ->
    { rCtx with
        expr = Literal(Bool(x <= y)) }
  | _, x, y ->
    { rCtx with
        error = Some(CannotApplyBinOp(op, x, y)) }

and evalUnary (ctx: Context) (op: UnaryOp) (right: Expression) =
  let rCtx = evaluate { ctx with expr = right }

  match op, rCtx.expr with
  | Not, Literal(Bool v) ->
    { rCtx with
        expr = Literal(Bool(not v)) }
  | UnaryMinus, Literal(Int64 v) -> { rCtx with expr = Literal(Int64 -v) }
  | _, v ->
    { rCtx with
        error = Some(CannotApplyUnaryOp(op, v)) }

and callProc ctx proc args = ctx //TODO

and evalRecordExpr ctx (ns: RecordExpr) =
  let ctx, vs =
    ns
    |> List.fold
      (fun (ctx, xs) (id, x) ->
        match ctx with
        | { error = Some _ } -> ctx, xs
        | { expr = Literal v } -> (evaluate {ctx with expr = x}, (id, v) :: xs)
        | { expr = m } ->
          { ctx with
              error = Some(ExpectingValue m) },
          xs)
      (ctx, [])
  
  {ctx with expr = Literal (RecordValue vs) }

and evaluate (ctx: Context) =
  match ctx.expr with
  | Literal _ -> ctx
  | Variable id -> evalVariable ctx id
  | Binary(op, left, right) -> evalBinary ctx op left right
  | Unary(op, right) -> evalUnary ctx op right
  | RecordExpr e -> evalRecordExpr ctx e
  | Call(proc, args) -> callProc ctx proc args


type ExecCtx =
  { values: Map<Identifier, Value>
    types: SetDeclaration list
    procedures: Proc list
    statements: Statement array
    current: int
    returnVars: Identifier list }

let execute (ctx: ExecCtx) =
  let current = ctx.statements[ctx.current]

  match current with
  | Assignment(vars, expr) -> ctx
  | _ -> ctx // TODO
