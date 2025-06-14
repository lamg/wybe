module LanguageServices.Compact.AST

/// Identifier (variable, function, type names)
type Identifier = string list

/// Literal values: integers, booleans, and strings
type Literal =
  | Int of int
  | Bool of bool
  | Str of string

[<RequireQualifiedAccess>]
type CompactOp =
  | Plus
  | Minus
  | Times
  | Div
  | Eq
  | NotEq
  | Lte
  | Gte
  | Lt
  | Gt
  | And
  | Or
  | Not

/// Expressions in Compact
type Expr =
  | Var of Identifier
  | Lit of Literal
  | Unary of CompactOp * Expr
  | Binary of Expr * CompactOp * Expr
  | MemberAccess of Expr * Identifier
  | IndexAccess of Expr * Expr
  | Array of Expr list
  | Call of longId: Identifier * typeArgs: CompactType list * args: Expr list
  | Cast of string * Expr
  | Version of int list
  | As of Identifier * CompactType

and TypeParam =
  | CompactTypeParam of CompactType
  | TypeParamInt of int

and CompactType =
  | NamedType of typeName: Identifier * typeParam: TypeParam list
  | Void

/// Statements in Compact
type Statement =
  | Assign of Expr * Expr
  | If of Expr * Statement list * Statement list option
  | For of i: Identifier * vectorOrLower: Expr * upper: Expr option * body: Statement list
  | Return of Expr option
  | CallStatement of Expr
  | Const of Identifier * Expr

type Param =
  { paramName: Identifier
    paramType: CompactType }

type Signature =
  { args: Param list
    returnType: CompactType }

/// Top-level definitions in Compact
type TopLevel =
  | Pragma of Identifier * Expr
  | Import of Identifier list
  | Ledger of exported: bool * Param
  | Witness of exported: bool * Identifier * Signature
  | Circuit of exported: bool * Identifier * Signature * body: Statement list
  | Enum of exported: bool * name: Identifier * members: Identifier list
  | Constructor of args: Param list * body: Statement list

/// A Compact program is a sequence of top-level definitions
type Program = TopLevel list

let compactInt = NamedType([ "int" ], [])
let compactBool = NamedType([ "bool" ], [])
let compactString = NamedType([ "string" ], [])
let compactArrayTypeId = ["array"]
