module GCL.Language

type Identifier = string

and TupleDestructor =
  | Fst
  | Snd

and Operator =
  | Plus
  | Minus
  | Times
  | Divide
  | And
  | Or
  | BoolEqual
  | Implies
  | Follows
  | Equal
  | Gt
  | Lt
  | Gte
  | Lte

and UnaryOp =
  | Not
  | UnaryMinus

and Literal =
  | Natural of uint64
  | Bytes of byte array
  | String of string
  | Bool of bool
  | Integer of int64
  | RecordValue of (Identifier * Literal) list
  | Constructior of Identifier * Literal

and Expression =
  | Constant of Literal
  | Binary of Operator * Expression * Expression
  | Variable of Identifier

  static member (+)(a: Expression, b: Expression) = Binary(Plus, a, b)
  static member (-)(a: Expression, b: Expression) = Binary(Minus, a, b)
  static member (*)(a: Expression, b: Expression) = Binary(Times, a, b)
  static member (/)(a: Expression, b: Expression) = Binary(Divide, a, b)

and Guarded = Expression * Statement

and IdentType =
  { name: Identifier
    nameType: Identifier }

and Proc =
  { name: Identifier
    args: IdentType list
    body: Statement list }

and TypeDecl =
  | TypeSynonym of Identifier * Identifier
  | Record of IdentType list
  | Union of Identifier * Identifier list

and Statement =
  | Alternative of Guarded list
  | Repetition of Guarded list
  | Assignment of Identifier * Expression
  | Skip
  | Proc of Proc
  | TypeDecl of TypeDecl
  | Assertion of Expression
