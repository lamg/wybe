module RustParser

open System

open RustParserCs
open Antlr4.Runtime
open Antlr4.Runtime.Misc
open Antlr4.Runtime.Tree
open Types


/// Visitor that builds an Expr AST from parse contexts
type RustVisitor() =
  inherit RustParserBaseVisitor<TargetLangExpr>()

  /// Visit binary arithmetic or logical expressions: expr <op> expr
  override this.VisitArithmeticOrLogicalExpression(context: RustParser.ArithmeticOrLogicalExpressionContext) =
    // Recursively visit sub-expressions
    let leftExpr = this.Visit(context.expression 0)

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

    let rightExpr = this.Visit(context.expression 1)
    Op(operator, leftExpr, rightExpr)

  /// Visit assignment expressions: expr = expr
  override this.VisitAssignmentExpression(context: RustParser.AssignmentExpressionContext) =
    let leftExpr = this.Visit(context.expression 0)
    let rightExpr = this.Visit(context.expression 1)
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

  /// Visit a Rust function definition, capturing signature and body expressions/comments
  override this.VisitFunction_(context: RustParser.Function_Context) =
    // Function name
    let name = context.identifier().GetText()
    // Parameters: split on commas, then split name and type on ':'
    let parameters =
      match context.functionParameters () with
      | null -> []
      | ps ->
        let txt = ps.GetText()

        if String.IsNullOrWhiteSpace txt then
          []
        else
          txt.Split([| ',' |], StringSplitOptions.RemoveEmptyEntries)
          |> Array.map (fun entry ->
            let parts = entry.Split([| ':' |], 2, StringSplitOptions.RemoveEmptyEntries)
            let n = parts.[0].Trim()
            let t = parts.[1].Trim()
            n, t)
          |> List.ofArray
    // Return type, if any
    let returnType =
      match context.functionReturnType () with
      | null -> None
      | rt ->
        let txt = rt.GetText()
        // rt.GetText() yields '->Type', so drop leading arrow
        let t = if txt.StartsWith "->" then txt.Substring(2) else txt
        Some(t.Trim())
    // Extract body text between braces using input stream positions
    let blockCtx = context.blockExpression ()
    // Get character stream and take text between '{' and '}'
    let inputStream = context.Start.InputStream
    let innerStart = blockCtx.Start.StartIndex + 1
    let innerStop = blockCtx.Stop.StopIndex - 1
    let bodyText = inputStream.GetText(Interval(innerStart, innerStop))
    // Split into non-empty, trimmed lines
    let lines =
      bodyText.Split([| '\r'; '\n' |], StringSplitOptions.RemoveEmptyEntries)
      |> Array.map (fun l -> l.Trim())
      |> Array.filter (fun l -> not (String.IsNullOrWhiteSpace l))
      |> List.ofArray
    // Helper to parse a single Rust expression via ANTLR visitor
    let parseExpr (str: string) : TargetLangExpr =
      let cs = CharStreams.fromString str
      let lex = RustLexer cs
      let tk = CommonTokenStream lex
      let pr = RustParser tk
      pr.RemoveErrorListeners()
      pr.AddErrorListener(ConsoleErrorListener<IToken>.Instance)
      let exprCtx = pr.expression ()
      RustVisitor().Visit exprCtx
    // Build body: comments or expressions
    let body =
      lines
      |> List.map (fun line ->
        if line.StartsWith "//" then
          let comment = line.Substring(2).Trim()

          if comment.StartsWith "{" && comment.EndsWith "}" then
            let inner = comment.Substring(1, comment.Length - 2).Trim()
            CommentAssertion inner
          else
            Comment line
        else
          parseExpr line)

    TargetFn
      { Name = name
        Parameters = parameters
        ReturnType = returnType
        Body = body }

  /// Visit terminal nodes, capturing comments as Comment expressions
  override this.VisitTerminal(node: ITerminalNode) =
    let tokenType = node.Symbol.Type

    if tokenType = RustParser.LINE_COMMENT || tokenType = RustParser.BLOCK_COMMENT then
      // preserve the raw comment text
      Comment(node.GetText())
    else
      base.VisitTerminal node

/// Parse all Rust functions from the given input string
let parseFunctions (input: string) : TargetFun list =
  // Initialize parser on the full crate
  let cs = CharStreams.fromString input
  let lex = RustLexer cs
  let tk = CommonTokenStream lex
  let pr = RustParser tk
  // Suppress ANTLR console error output when parsing functions
  pr.RemoveErrorListeners()
  // pr.AddErrorListener(ConsoleErrorListener<IToken>.Instance)
  let tree = pr.crate ()
  // Find all function definitions under visItem
  tree.item ()
  |> Seq.choose (fun item ->
    let vis = item.visItem ()

    if vis <> null then
      let fctx = vis.function_ ()

      if fctx <> null && fctx.blockExpression () <> null then
        // skip main functions; only extract proof functions
        let name = fctx.identifier().GetText()

        if name = "main" then
          None
        else
          match RustVisitor().VisitFunction_ fctx with
          | TargetFn f -> Some f
          | _ -> None
      else
        None
    else
      None)
  |> Seq.toList
