// Signature file for parser generated by fsyacc
module Parser
type token = 
  | EOF
  | IDENT of (string)
  | BULLET
  | ALPHA
  | MU
  | ARROW
  | TYPEOF
  | BAR
  | EQUAL
  | SET
  | MODULE
  | PUB
  | OPEN
  | TH
  | AX
  | SQUARE
  | PROOF
  | COMMA
  | RIGHT_BRACE
  | LEFT_BRACE
  | RIGHT_PAREN
  | LEFT_PAREN
  | UN_OP of (string)
  | BIN_OP of (string)
type tokenId = 
    | TOKEN_EOF
    | TOKEN_IDENT
    | TOKEN_BULLET
    | TOKEN_ALPHA
    | TOKEN_MU
    | TOKEN_ARROW
    | TOKEN_TYPEOF
    | TOKEN_BAR
    | TOKEN_EQUAL
    | TOKEN_SET
    | TOKEN_MODULE
    | TOKEN_PUB
    | TOKEN_OPEN
    | TOKEN_TH
    | TOKEN_AX
    | TOKEN_SQUARE
    | TOKEN_PROOF
    | TOKEN_COMMA
    | TOKEN_RIGHT_BRACE
    | TOKEN_LEFT_BRACE
    | TOKEN_RIGHT_PAREN
    | TOKEN_LEFT_PAREN
    | TOKEN_UN_OP
    | TOKEN_BIN_OP
    | TOKEN_end_of_input
    | TOKEN_error
type nonTerminalId = 
    | NONTERM__startstart
    | NONTERM_expr
    | NONTERM_identList
    | NONTERM_hint
    | NONTERM_transformer
    | NONTERM_steps
    | NONTERM_proof
    | NONTERM_law
    | NONTERM_open
    | NONTERM_valueList
    | NONTERM_setDecl
    | NONTERM_signature
    | NONTERM_funcIdent
    | NONTERM_typeOfDecl
    | NONTERM_statement
    | NONTERM_statements
    | NONTERM_module
    | NONTERM_start
/// This function maps tokens to integer indexes
val tagOfToken: token -> int

/// This function maps integer indexes to symbolic token ids
val tokenTagToTokenId: int -> tokenId

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
val prodIdxToNonTerminal: int -> nonTerminalId

/// This function gets the name of a token as a string
val token_to_string: token -> string
val start : (FSharp.Text.Lexing.LexBuffer<'cty> -> token) -> FSharp.Text.Lexing.LexBuffer<'cty> -> (Module) 