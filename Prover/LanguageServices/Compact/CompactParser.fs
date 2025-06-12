/// Token parsers and helpers
module LanguageServices.Compact.Parser

/// Identifier (variable, function, type names)
type Identifier = string list

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
  | Array of Expr list
  | Call of longId: Identifier * typeArgs: CompactType list * args: Expr list
  | Cast of string * Expr
  | Version of int list
  | As of Identifier * CompactType

and TypeParam =
  | CompactTypeParam of CompactType
  | TypeParamInt of int

and CompactType =
  | NamedType of typeName: Identifier * typeParam: TypeParam list
  | Void

/// Statements in Compact
type Statement =
  | Assign of Expr * string * Expr
  | If of Expr * Statement list * Statement list option
  | For of i: Identifier * vectorOrLower: Expr * upper: Expr option * body: Statement list
  | Return of Expr option
  | CallStatement of Expr
  | Const of Identifier * Expr

type Param =
  { paramName: Identifier
    paramType: CompactType }

type Signature =
  { args: Param list
    returnType: CompactType }

/// Top-level definitions in Compact
type TopLevel =
  | Pragma of Identifier * Expr
  | Import of Identifier list
  | Ledger of exported: bool * Param
  | Witness of exported: bool * Identifier * Signature
  | Circuit of exported: bool * Identifier * Signature * body: Statement list
  | Enum of exported: bool * name: Identifier * members: Identifier list
  | Constructor of args: Param list * body: Statement list

/// A Compact program is a sequence of top-level definitions
type Program = TopLevel list

open FParsec

let commentLine = pstring "//" >>. skipRestOfLine true
let ws = skipMany (spaces1 <|> commentLine)
let str s = pstring s .>> ws

let kw s =
  pstring s .>> notFollowedBy letter >>. ws

let identifier =
  let shortId =
    let isIdStart c = isLetter c
    let isIdChar c = isLetter c || isDigit c || c = '_'
    many1Satisfy2L isIdStart isIdChar "identifier"

  sepBy1 shortId (pchar '.') .>> ws

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

let tuple p = between lparen rparen (sepBy p comma)

let angleTuple p =
  between (pchar '<') (pchar '>') (sepBy p comma) .>> ws |> opt
  |>> Option.toList
  |>> List.concat

let compactType =
  let mutable typeTuple, typeTupleRef =
    createParserForwardedToRef<CompactType, unit> ()

  let typeParamsTuple =
    let paramParser =
      typeTuple |>> CompactTypeParam <|> (pint >>= (TypeParamInt >> preturn))

    angleTuple paramParser

  let p =
    parse {
      do! lbracket >>. rbracket
      return Void
    }
    <|> parse {
      let! typeId = identifier
      let! tuple = typeParamsTuple
      return NamedType(typeId, tuple)
    }

  typeTupleRef.Value <- p
  typeTuple

/// Basic term parser: literals, identifiers, parenthesized expressions
let term expr =
  let idOrCallOrAs =
    let idOrCall id =
      parse {
        let! typeArgs = angleTuple compactType
        let! args = tuple expr
        return Call(id, typeArgs, args)
      }
      <|> parse {
        do! kw "as"
        let! asType = compactType
        return As(id, asType)
      }
      <|> (preturn (Var id))

    identifier >>= idOrCall

  let array = between lbracket rbracket (sepBy expr comma) |>> Array


  choice
    [ idOrCallOrAs
      pint |>> Int |>> Lit
      (kw "true" >>% Lit(Bool true))
      (kw "false" >>% Lit(Bool false))
      pstringLiteral |>> (Str >> Lit)
      between lparen rparen expr
      array ]

let expr =
  let opp = new OperatorPrecedenceParser<Expr, unit, unit>()
  opp.TermParser <- term opp.ExpressionParser
  let infix op prec assoc f = InfixOperator(op, ws, prec, assoc, f)
  let prefix op prec f = PrefixOperator(op, ws, prec, true, f)
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

let statementBlock =
  let mutable statement, statementRef = createParserForwardedToRef<Statement, unit> ()

  let block =
    parse {
      do! lbrace
      let! xs = many statement
      do! rbrace
      return xs
    }

  let assignStmt =
    pipe3 expr (choice [ str "+="; str "-="; str "=" ] .>> ws) expr (fun t op v -> Assign(t, op, v))
    .>> semicolon

  let constDef =
    parse {
      do! kw "const"
      let! var = identifier
      do! kw "="
      let! r = expr
      do! semicolon
      return Const(var, r)
    }

  let returnStmt =
    parse {
      do! kw "return"
      let! r = opt expr
      do! semicolon
      return Return r
    }

  let ifStmt =
    // if (testexpr)
    //   <statement>
    // if (testexpr)
    //   <statement>
    // else
    //  <statement>
    parse {
      do! kw "if"
      let! cond = between lparen rparen expr
      let! thenB = block
      let! elseB = opt (kw "else" >>. block)
      return If(cond, thenB, elseB)
    }

  let forStmt =
    // for (const i of <vector>) <statement>
    // for (const i of <lower>..<upper>) <statement>
    parse {
      do! kw "for"
      do! lparen
      do! kw "const"
      let! i = identifier
      do! kw "of"
      let! vectorOrLower = expr
      let! upper = opt (kw ".." >>. expr)
      do! rparen

      let! statements = block
      return For(i, vectorOrLower, upper, statements)
    }

  let callStatement = expr .>> semicolon |>> CallStatement

  statementRef.Value <-
    parse {
      let! s =
        choice
          [ attempt assignStmt
            attempt returnStmt
            attempt ifStmt
            attempt forStmt
            attempt constDef
            callStatement ]

      return s
    }

  block


let pragma =
  parse {
    let! v = kw "pragma" .>> kw "language_version" >>. pversion
    do! semicolon
    return Pragma([ "language_version" ], v)
  }

let import =
  parse {
    do! kw "import"
    let! moduleId = identifier
    do! semicolon
    return Import [ moduleId ]
  }

let paramType =
  parse {
    let! id = identifier
    do! colon
    let! varType = compactType
    return { paramName = id; paramType = varType }
  }

let ledger exported =
  parse {
    do! kw "ledger"
    let! ledgerVar = paramType
    do! semicolon
    return Ledger(exported, ledgerVar)
  }


let parameters = tuple paramType

let signature =
  parse {
    let! args = parameters
    do! colon
    let! returnType = compactType
    return { args = args; returnType = returnType }
  }


let circuit exported =
  parse {
    do! kw "circuit"
    let! id = identifier
    let! signature = signature
    let! body = statementBlock
    return Circuit(exported, id, signature, body)

  }

let enum exported =
  parse {
    do! kw "enum"
    let! enumId = identifier
    do! lbrace
    let! members = sepBy identifier comma
    do! rbrace
    return Enum(exported, enumId, members)
  }

let constructor =
  parse {
    do! kw "constructor"
    let! args = parameters
    let! body = statementBlock
    return Constructor(args, body)
  }

let witness exported =
  parse {
    do! kw "witness"
    let! id = identifier
    let! s = signature
    do! semicolon
    return Witness(exported, id, s)
  }

let exportMember =
  parse {
    do! kw "export"
    return! ledger true <|> circuit true <|> enum true <|> witness true
  }

let topLevel =
  pragma
  <|> import
  <|> exportMember
  <|> ledger false
  <|> circuit false
  <|> enum false
  <|> constructor
  <|> witness false

/// Top-level program parser (stub for statements)
let program = ws >>. many topLevel .>> eof

/// Parse a Compact program into AST statements
let parse (input: string) : TopLevel list =
  match run program input with
  | Success(res, _, _) -> res
  | Failure(err, _, _) -> failwithf "Parse error: %s" err
