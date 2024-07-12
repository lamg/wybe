module GCL.Language

type Identifier = string

and Operator =
  | Plus
  | Minus
  | Times
  | Divide
  | And
  | Or
  | BoolEqual
  | BoolDifferent
  | Implies
  | Follows
  | Equal
  | Different
  | Gt
  | Lt
  | Gte
  | Lte
  | ElementOf

and UnaryOp =
  | Not
  | UnaryMinus

and Value =
  | Uint64 of uint64
  | Bytes of byte array
  | String of string
  | Bool of bool
  | Int64 of int64

and Expression =
  | Literal of Value
  | Binary of Operator * Expression * Expression
  | Unary of UnaryOp * Expression
  | Variable of Identifier

  static member (+)(a: Expression, b: Expression) = Binary(Plus, a, b)
  static member (-)(a: Expression, b: Expression) = Binary(Minus, a, b)
  static member (*)(a: Expression, b: Expression) = Binary(Times, a, b)
  static member (/)(a: Expression, b: Expression) = Binary(Divide, a, b)

and Guarded = Expression * SourceStatement
and SetDeclaration = Identifier * Expression list // list of alternative sets

and Proc =
  { name: Identifier
    input: Expression // restricted to StateExpr
    output: Expression // restricted to StateExpr
    body: SourceStatement list }

and Statement =
  | Alternative of Guarded list
  | Repetition of Guarded list
  | Assignment of Identifier list * Expression list
  | Skip
  | Proc of Proc
  | SetDeclaration of SetDeclaration
  | SetTransformation of Expression
  | Call of Identifier
  | Composition of SourceStatement list

and SourceStatement = { id: uint; statement: Statement }
