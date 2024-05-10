module Predicate

type Binary = { left: Predicate; right: Predicate }
and Unary = Predicate

and Predicate =
  | True
  | False
  | Var of string
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

type Step = { pred: Predicate; hint: Hint }

type Proof = { thesis: Predicate; steps: Step list }

type NamedPred = { name: string; pred: Predicate }

type Law =
  | Theorem of NamedPred
  | Axiom of NamedPred

type Statement =
  | Open of string
  | Law of Law
  | Proof of Proof

type Module =
  { name: string
    statements: Statement list }
