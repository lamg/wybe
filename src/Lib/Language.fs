module Language

type Binary = { left: Expr; right: Expr }
and Unary = Expr

and Expr =
  | Ident of string
  | And of Binary
  | Or of Binary
  | Implies of Binary
  | Follows of Binary
  | Equivales of Binary
  | Differs of Binary
  | Not of Unary

type HintOp =
  | HintImplies
  | HintFollows
  | HintEquivales
  | HintDiffers

type Hint =
  { operator: HintOp
    lawNames: string list }

type Transformer =
  | Trans of Hint
  | End

type Step = { pred: Expr; trans: Transformer }

type Proof = { thesis: Expr; steps: Step list }

type NamedPred = { name: string; pred: Expr }

type Law =
  | Theorem of NamedPred
  | Axiom of NamedPred

type Value = Value of string
type TypeDecl = { name: string; values: Value list }

type Statement =
  | Open of string
  | Law of Law
  | Proof of Proof
  | TypeDecl of TypeDecl

type Module =
  { name: string
    statements: Statement list }
