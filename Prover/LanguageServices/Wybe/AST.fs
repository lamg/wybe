module LanguageServices.Wybe.AST

type Literal =
  | Int of int
  | Bool of bool
  | Str of string

[<RequireQualifiedAccess>]
type Op =
  // integer → integer → integer
  | Plus
  | Minus
  | Times
  | Div
  | UnaryMinus // integer → integer
  // 'a → 'a → boolean
  | Equals
  | Differs
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
  | Inequiv
  | And
  | Or
  | Implies
  | Follows
  // sequence -> integer
  | Length
  | HasType
  // sequence operations
  | Cons // element -> sequence -> sequence
  | Concat // sequence -> sequence -> sequence
  | IsPrefix // sequence -> sequence -> boolean
  | IsSuffix // sequence -> sequence -> boolean
  | Head // sequence -> element
  | Tail // sequence -> sequence

type Expr =
  | Var of name: string
  | Lit of Literal
  | Unary of Op * Expr
  | Binary of Expr * Op * Expr
  | Array of Expr list
  | ArrayElem of name: string * index: Expr

[<RequireQualifiedAccess>]
type Type =
  | Integer
  | Boolean
  | String
  | VarType of string
  | Array of Type

type SameTypeDecl = string list * Type
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
