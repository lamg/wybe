module Types

/// Simple expression AST: variables, integer literals, or binary operations
/// Simple expression AST: variables, integer literals, binary operations,
/// comments, or comment assertions
/// Represents a parsed Rust function, including signature and body expressions
type TargetFun =
  { Name: string
    Parameters: (string * string) list
    ReturnType: string option
    Body: TargetLangExpr list }

/// Simple expression AST: variables, integer literals, binary operations,
/// comments, comment assertions, or function definitions
and TargetLangExpr =
  | Var of string
  | Integer of int64
  | Op of string * TargetLangExpr * TargetLangExpr
  | Comment of string
  | CommentAssertion of string // parses an assertion in a comment with the syntax { <expr> <op> <expr> }
  | TargetFn of TargetFun // represents a parsed Rust function
