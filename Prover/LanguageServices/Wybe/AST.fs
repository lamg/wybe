module LanguageServices.Wybe.AST

type Literal =
  | Int of int
  | Bool of bool
  | Str of string

[<RequireQualifiedAccess>]
type WybeOp =
  // integer → integer → integer
  | Plus
  | Minus
  | Times
  | Div
  | UnaryMinus // integer → integer
  // 'a → 'a → boolean
  | Eq
  | NotEq
  // integer → integer → boolean
  // this terminology comes from https://www.cs.utexas.edu/~EWD/ewd07xx/EWD768.PDF
  | AtMost // ≤
  | AtLeast // ≥
  | LessThan // <
  | Exceeds // >
  // proposition
  | Not // boolean → boolean
  // boolean → boolean → boolean
  | Equiv
  | NotEquiv
  | And
  | Or
  | Implies
  | Follows
  // sequence -> integer
  | Length

type Expr =
  | Var of name: string
  | Lit of Literal
  | Unary of WybeOp * Expr
  | Binary of Expr * WybeOp * Expr
  | Array of Expr list
  | ArrayElem of name: string * index: Expr

[<RequireQualifiedAccess>]
type WybeType =
  | Integer
  | Boolean
  | String
  | VarType of string
  | Array of WybeType

type SameTypeDecl = string list * WybeType
type Guard = Guard of Expr * Statement list

and Statement =
  | VarDecl of SameTypeDecl list
  | Becomes of vars: string list * exprs: Expr list
  | If of Guard list
  | Do of Guard list
  | Assert of Expr
  | Compose of Statement * Statement
  | Skip

type TopLevel = Procedure of name: string * Statement list
