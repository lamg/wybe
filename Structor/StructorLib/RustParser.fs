module StructorLib.RustParser

open RustParserCs
open Antlr4.Runtime
open Antlr4.Runtime.Tree
open System
open System.Text.RegularExpressions

/// Simple expression AST: variables, integer literals, or binary operations
/// Simple expression AST: variables, integer literals, binary operations,
/// comments, or comment assertions
type Expr =
  | Var of string
  | Integer of int64
  | Op of string * Expr * Expr
  | Comment of string
  | CommentAssertion of Expr // parses an assertion in a comment with the syntax { <expr> <op> <expr> }

/// Visitor that builds an Expr AST from parse contexts
type RustVisitor() =
  inherit RustParserBaseVisitor<Expr>()

  /// Visit binary arithmetic or logical expressions: expr <op> expr
  override this.VisitArithmeticOrLogicalExpression(context: RustParser.ArithmeticOrLogicalExpressionContext) =
    // Recursively visit sub-expressions
    let leftExpr = this.Visit(context.expression (0))

    let operator =
      if context.PLUS() <> null then
        context.PLUS().GetText()
      elif context.MINUS() <> null then
        context.MINUS().GetText()
      elif context.STAR() <> null then
        context.STAR().GetText()
      elif context.SLASH() <> null then
        context.SLASH().GetText()
      elif context.PERCENT() <> null then
        context.PERCENT().GetText()
      elif context.shl () <> null then
        context.shl().GetText()
      elif context.shr () <> null then
        context.shr().GetText()
      elif context.AND() <> null then
        context.AND().GetText()
      elif context.CARET() <> null then
        context.CARET().GetText()
      elif context.OR() <> null then
        context.OR().GetText()
      else
        ""

    let rightExpr = this.Visit(context.expression (1))
    Op(operator, leftExpr, rightExpr)

  /// Visit assignment expressions: expr = expr
  override this.VisitAssignmentExpression(context: RustParser.AssignmentExpressionContext) =
    let leftExpr = this.Visit(context.expression (0))
    let rightExpr = this.Visit(context.expression (1))
    // Represent assignment as an Op node with '=' operator
    Op("=", leftExpr, rightExpr)

  /// Visit literal expressions (integer literals)
  override this.VisitLiteralExpression_(context: RustParser.LiteralExpression_Context) =
    let text = context.GetText()
    // Parse integer literals; fall back to variable if not a pure integer
    let mutable value = 0L

    if Int64.TryParse(text, &value) then
      Integer value
    else
      Var text

  /// Visit path expressions as variables
  override this.VisitPathExpression_(context: RustParser.PathExpression_Context) = Var(context.GetText())

  /// Default function visit: delegate to base visitor
  override this.VisitFunction_(context: RustParser.Function_Context) = base.VisitFunction_ context

  /// Visit terminal nodes, capturing comments as Comment expressions
  override this.VisitTerminal(node: ITerminalNode) =
    let tokenType = node.Symbol.Type

    if tokenType = RustParser.LINE_COMMENT || tokenType = RustParser.BLOCK_COMMENT then
      // preserve the raw comment text
      Comment(node.GetText())
    else
      base.VisitTerminal(node)

/// Represents a parsed Rust function, including signature and body expressions
type Function =
  { Name: string
    Parameters: (string * string) list
    ReturnType: string option
    Body: Expr list }

/// Parse a Rust function from the given string.  Recognizes simple signatures
/// and parses body lines as expressions or comment-expressions in `{}`.
let parseFunction (input: string) : Function =
  // Regex to capture fn name, params, optional return type, and body content
  let regex =
    Regex
      "^\s*(?:pub\s+)?fn\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*\\(([^)]*)\\)\s*(?:->\s*([^\\{\s]+))?\s*\\{\s*([\s\S]*?)\s*\\}\s*$"

  let m = regex.Match input

  if not m.Success then
    failwithf "Failed to parse function signature: %s" input

  let name = m.Groups.[1].Value
  let paramsStr = m.Groups.[2].Value.Trim()

  let returnType =
    let rt = m.Groups.[3].Value
    if String.IsNullOrWhiteSpace rt then None else Some rt

  let parameters =
    if String.IsNullOrWhiteSpace paramsStr then
      []
    else
      paramsStr.Split([| ',' |], StringSplitOptions.RemoveEmptyEntries)
      |> Array.map (fun p ->
        let parts = p.Split([| ':' |], StringSplitOptions.RemoveEmptyEntries)
        let n = parts.[0].Trim()
        let t = parts.[1].Trim()
        n, t)
      |> List.ofArray

  let bodyContent = m.Groups.[4].Value

  let lines =
    bodyContent.Split([| '\r'; '\n' |], StringSplitOptions.RemoveEmptyEntries)
    |> Array.map (fun l -> l.Trim())
    |> Array.filter (fun l -> not (String.IsNullOrWhiteSpace l))
    |> Array.toList
  // helper to parse an expression string via ANTLR visitor
  let parseExpr (str: string) : Expr =
    let charStream = CharStreams.fromString str
    let lexer = RustLexer charStream
    let tokens = CommonTokenStream lexer
    let parser = RustParser tokens
    parser.RemoveErrorListeners()
    parser.AddErrorListener(ConsoleErrorListener<IToken>.Instance)
    let tree = parser.expression ()
    RustVisitor().Visit tree
  // parse each line: comments or expressions
  // Parse each line: comments, comment-assertions, or expressions
  let body =
    lines
    |> List.map (fun line ->
      if line.StartsWith "//" then
        let comment = line.Substring(2).Trim()
        // comment assertion of the form { <expr> }
        if comment.StartsWith "{" && comment.EndsWith "}" then
          let inner = comment.Substring(1, comment.Length - 2).Trim()
          CommentAssertion(parseExpr inner)
        else
          Comment line
      else
        parseExpr line)

  { Name = name
    Parameters = parameters
    ReturnType = returnType
    Body = body }
