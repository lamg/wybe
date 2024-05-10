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
