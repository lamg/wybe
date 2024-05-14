module Language

type Binary = { operator: string; left: Expr; right: Expr }
and Unary = { operator: string; expr: Expr }
and Expr =
  | Ident of string
  | Binary of Binary
  | Unary of Unary

type Hint =
  { operator: string
    lawNames: string list }

type Transformer =
  | Trans of Hint
  | End

type Step = { expr: Expr; trans: Transformer }

type Proof = { thesis: Expr; steps: Step list }

type NamedExpr = { name: string; expr: Expr }

type Law =
  | Theorem of NamedExpr
  | Axiom of NamedExpr

type Value = Value of string
type TypeDecl = { name: string; values: Value list }
type TypeOfDecl = { func: string; signature: string list }

type Statement =
  | Open of string
  | Law of Law
  | Proof of Proof
  | TypeDecl of TypeDecl
  | TypeOfDecl of TypeOfDecl

type Module =
  { name: string
    statements: Statement list }
