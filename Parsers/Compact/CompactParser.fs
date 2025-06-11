/// Token parsers and helpers
module Parsers.Compact

/// Identifier (variable, function, type names)
type Identifier = string

/// Literal values: integers, booleans, and strings
type Literal =
  | Int of int
  | Bool of bool
  | Str of string

/// Expressions in Compact
type Expr =
  | Var of Identifier
  | Lit of Literal
  | Unary of string * Expr
  | Binary of Expr * string * Expr
  | MemberAccess of Expr * Identifier
  | IndexAccess of Expr * Expr
  | Call of longId: Identifier list * args: Expr list
  | Cast of string * Expr
  | Version of int list

/// Statements in Compact
type Statement =
  | Assign of Expr * string * Expr
  | If of Expr * Statement list * Statement list option
  | For of Identifier * Expr * Expr * Statement list
  | Return of Expr option
  | CallStatement of Expr

type TypeParam =
  | TypeParamId of string
  | TypeParamInt of int

type CompactType =
  | NamedType of typeName: string * typeParam: TypeParam option
  | Void

type Param =
  { paramName: string
    paramType: CompactType }

type Signature =
  { args: Param list
    returnType: CompactType }

/// Top-level definitions in Compact
type TopLevel =
  | Pragma of Identifier * Expr
  | Import of Identifier list
  | Ledger of Identifier * Identifier
  | Circuit of name: Identifier * signature: Signature * body: Statement list

/// A Compact program is a sequence of top-level definitions
type Program = TopLevel list

open FParsec

let commentLine = pstring "//" >>. skipRestOfLine true
let ws = skipMany (spaces1 <|> commentLine)
let str s = pstring s .>> ws

let kw s =
  pstring s .>> notFollowedBy letter >>. ws

let identifier =
  let isIdStart c = isLetter c
  let isIdChar c = isLetter c || isDigit c || c = '_'
  many1Satisfy2L isIdStart isIdChar "identifier" .>> ws

let pint = pint32 .>> ws

let pversion =
  parse {
    let! x = pint
    let! xs = many (pchar '.' >>. pint)
    do! ws
    return Version(x :: xs)
  }

let pstringLiteral =
  between (pchar '"') (pchar '"') (manyChars (noneOf "\"")) .>> ws

let lparen = pchar '(' >>. ws
let rparen = pchar ')' >>. ws
let lbrace = pchar '{' >>. ws
let rbrace = pchar '}' >>. ws
let lbracket = pchar '[' >>. ws
let rbracket = pchar ']' >>. ws
let semicolon = pchar ';' >>. ws
let colon = pchar ':' >>. ws
let comma: Parser<char, unit> = pchar ',' .>> ws

/// Basic term parser: literals, identifiers, parenthesized expressions
let term expr =
  choice
    [ identifier |>> Var
      pint |>> (Int >> Lit)
      (kw "true" >>% Lit(Bool true))
      (kw "false" >>% Lit(Bool false))
      pstringLiteral |>> (Str >> Lit)
      between lparen rparen expr ]

let expr =
  /// FParsec-based parser for Compact
  /// Operator precedence parser for expressions
  let opp = new OperatorPrecedenceParser<Expr, unit, unit>()
  opp.TermParser <- term opp.ExpressionParser
  let infix op prec assoc f = InfixOperator(op, ws, prec, assoc, f)
  let prefix op prec f = PrefixOperator(op, ws, prec, true, f)
  opp.AddOperator(infix "::" 5 Associativity.Right (fun x y -> Binary(x, "::", y)))
  opp.AddOperator(infix "*" 7 Associativity.Left (fun x y -> Binary(x, "*", y)))
  opp.AddOperator(infix "/" 7 Associativity.Left (fun x y -> Binary(x, "/", y)))
  opp.AddOperator(infix "+" 6 Associativity.Left (fun x y -> Binary(x, "+", y)))
  opp.AddOperator(infix "-" 6 Associativity.Left (fun x y -> Binary(x, "-", y)))
  opp.AddOperator(infix "==" 4 Associativity.Left (fun x y -> Binary(x, "==", y)))
  opp.AddOperator(infix "!=" 4 Associativity.Left (fun x y -> Binary(x, "!=", y)))
  opp.AddOperator(infix "<=" 4 Associativity.Left (fun x y -> Binary(x, "<=", y)))
  opp.AddOperator(infix ">=" 4 Associativity.Left (fun x y -> Binary(x, ">=", y)))
  opp.AddOperator(infix "<" 4 Associativity.Left (fun x y -> Binary(x, "<", y)))
  opp.AddOperator(infix ">" 4 Associativity.Left (fun x y -> Binary(x, ">", y)))
  opp.AddOperator(prefix "!" 9 (fun x -> Unary("not", x)))
  opp.AddOperator(infix "&&" 3 Associativity.Left (fun x y -> Binary(x, "and", y)))
  opp.AddOperator(infix "||" 2 Associativity.Left (fun x y -> Binary(x, "or", y)))
  opp.ExpressionParser

let statement =
  /// Statement parser (forward declaration)
  let mutable statement, statementRef = createParserForwardedToRef<Statement, unit> ()

  let assignStmt =
    pipe3 expr (choice [ str "+="; str "-="; str "=" ] .>> ws) expr (fun t op v -> Assign(t, op, v))
    .>> semicolon

  let returnStmt = (kw "return" >>. opt expr) |>> Return .>> semicolon

  let ifStmt =
    pipe3
      (kw "if" >>. between lparen rparen expr)
      (between lbrace rbrace (many statement))
      (opt (kw "else" >>. between lbrace rbrace (many statement)))
      (fun cond thenB elseB -> If(cond, thenB, elseB))

  let forStmt =
    pipe4
      (kw "for" >>. identifier .>> str "=")
      expr
      (str "to" >>. ws >>. expr)
      (between lbrace rbrace (many statement))
      (fun v init cond body -> For(v, init, cond, body))

  let genericStmt =
    parse {
      let! funId = sepBy identifier (pchar '.')
      do! lparen
      let! args = sepBy expr (pchar ',')
      do! rparen
      return CallStatement(Call(funId, args))
    }

  statementRef.Value <-
    parse {
      let! s =
        choice
          [ attempt assignStmt
            attempt returnStmt
            attempt ifStmt
            attempt forStmt
            genericStmt ]

      do! semicolon
      return s
    }

  statement

let pragma =
  parse {
    let! v = kw "pragma" .>> kw "language_version" >>. pversion
    do! semicolon
    return Pragma("language_version", v)
  }

let import =
  parse {
    do! kw "import"
    let! moduleId = identifier
    do! semicolon
    return Import [ moduleId ]
  }

let ledger =
  parse {
    do! kw "ledger"
    let! id = identifier
    do! colon
    let! idType = identifier
    do! semicolon
    return Ledger(id, idType)
  }

let parseType =
  parse {
    do! lbracket >>. rbracket
    return Void
  }
  <|> parse {
    let! typeId = identifier

    let! typeParam =
      opt (
        parse {
          do! pchar '<' >>. preturn ()

          let! typeParam =
            (identifier >>= (fun a -> preturn (TypeParamId a))
             <|> (pint >>= (fun a -> preturn (TypeParamInt a))))

          do! pchar '>' >>. preturn ()
          return typeParam
        }
      )

    return NamedType(typeId, typeParam)
  }

let paramType =
  parse {
    let! id = identifier
    let! varType = parseType
    return { paramName = id; paramType = varType }
  }

let signature =
  parse {
    do! lparen
    let! xs = many paramType
    do! rparen
    do! colon
    let! returnType = parseType
    return { args = xs; returnType = returnType }
  }

let statementBlock =
  parse {
    do! lbrace
    let! xs = many statement
    do! rbrace
    return xs
  }

let circuit =
  parse {
    do! kw "circuit"
    let! id = identifier
    let! signature = signature
    let! body = statementBlock
    return Circuit(id, signature, body)

  }

let exportMember =
  parse {
    do! kw "export"
    return! ledger <|> circuit
  }

let topLevel = pragma <|> import <|> exportMember

/// Top-level program parser (stub for statements)
let program = ws >>. many topLevel .>> eof

/// Parse a Compact program into AST statements
let parse (input: string) : TopLevel list =
  match run program input with
  | Success(res, _, _) -> res
  | Failure(err, _, _) -> failwithf "Parse error: %s" err
