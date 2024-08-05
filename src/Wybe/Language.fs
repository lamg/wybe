module Language

type Binary =
  { operator: string
    left: Expr
    right: Expr }

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
type SetDecl = { name: string; values: Value list }

type TypeOfDecl =
  { func: string; signature: string list }

type Branch<'a, 'b> =
  { value: 'a
    children: Tree<'a, 'b> seq }

and Tree<'a, 'b> =
  | Branch of Branch<'a, 'b>
  | Leaf of 'b

type Description =
  { element: string; description: string }

type ProcessId = ProcessId of string

type EventId = EventId of string

type AlphabetDecl =
  { processId: ProcessId
    elements: EventId list }

type ProcessDecl =
  { name: ProcessId
    localRecursion: ProcessId option
    alphabet: EventId list
    body: Tree<Description, ProcessId> }

type Statement =
  | Open of string
  | Law of Law
  | Proof of Proof
  | SetDecl of SetDecl
  | TypeOfDecl of TypeOfDecl
  | Description of Description
  | AlphabetDecl of AlphabetDecl
  | ProcessDecl of ProcessDecl

type Module =
  { name: string
    statements: Statement list }
