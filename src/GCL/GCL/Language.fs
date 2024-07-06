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

and UnaryOp =
  | Not
  | UnaryMinus

and RecordValue = (Identifier * Value) list

and Value =
  | Uint64 of uint64
  | Bytes of byte array
  | String of string
  | Bool of bool
  | Int64 of int64
  | RecordValue of RecordValue
  | Constructor of Identifier * Value

and RecordExpr = (Identifier * Expression) list

and Expression =
  | Literal of Value
  | Binary of Operator * Expression * Expression
  | Unary of UnaryOp * Expression
  | Variable of Identifier
  | RecordExpr of RecordExpr
  | Call of Identifier * Expression // Expression restricted to RecordExpr

  static member (+)(a: Expression, b: Expression) = Binary(Plus, a, b)
  static member (-)(a: Expression, b: Expression) = Binary(Minus, a, b)
  static member (*)(a: Expression, b: Expression) = Binary(Times, a, b)
  static member (/)(a: Expression, b: Expression) = Binary(Divide, a, b)

and Guarded = Expression * SourceStatement

and IdentType =
  { name: Identifier
    nameType: Identifier }

and RecordBody = IdentType list

and Proc =
  { name: Identifier
    input: RecordBody
    output: RecordBody
    body: SourceStatement list }

and TypeDecl =
  | TypeSynonym of Identifier * Identifier
  | Record of Identifier * RecordBody
  | Union of Identifier * Identifier list

and Statement =
  | Alternative of Guarded list
  | Repetition of Guarded list
  | Assignment of Identifier list * Expression
  | Skip
  | Proc of Proc
  | TypeDecl of TypeDecl
  | Assertion of Expression // Expression restricted to Bool

and SourceStatement = {id: uint; statement: Statement}