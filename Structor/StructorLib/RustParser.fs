module StructorLib.RustParser

open RustParserCs
open Antlr4.Runtime.Tree
open System

/// Simple expression AST: variables, integer literals, or binary operations
type Expr =
  | Var of string
  | Integer of int64
  | Op of string * Expr * Expr
  | Comment of string

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
