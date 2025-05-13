module Structor.Types

/// Simple expression AST: variables, integer literals, or binary operations
/// Simple expression AST: variables, integer literals, binary operations,
/// comments, or comment assertions
type TargetLangExpr =
  | Var of string
  | Integer of int64
  | Op of string * TargetLangExpr * TargetLangExpr
  | Comment of string
  | CommentAssertion of string // parses an assertion in a comment with the syntax { <expr> <op> <expr> }

/// Represents a parsed Rust function, including signature and body expressions
type Function =
  { Name: string
    Parameters: (string * string) list
    ReturnType: string option
    Body: TargetLangExpr list }
