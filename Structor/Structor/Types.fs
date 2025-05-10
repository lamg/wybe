module Structor.Types

/// Simple expression AST: variables, integer literals, or binary operations
/// Simple expression AST: variables, integer literals, binary operations,
/// comments, or comment assertions
type Expr =
  | Var of string
  | Integer of int64
  | Op of string * Expr * Expr
  | Comment of string
  | CommentAssertion of Expr // parses an assertion in a comment with the syntax { <expr> <op> <expr> }

/// Represents a parsed Rust function, including signature and body expressions
type Function =
  { Name: string
    Parameters: (string * string) list
    ReturnType: string option
    Body: Expr list }
