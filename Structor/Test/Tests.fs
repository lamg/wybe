module Tests

open System
open Xunit
open Antlr4.Runtime
open Antlr4.Runtime.Tree
open RustParserCs
open StructorLib.RustParser

/// Helper to parse an expression rule from a string
let parseExpression (input: string) =
    let charStream = CharStreams.fromString input
    let lexer = RustLexer(charStream)
    let tokens = CommonTokenStream(lexer)
    let parser = RustParser(tokens)
    parser.RemoveErrorListeners()
    parser.AddErrorListener(ConsoleErrorListener<IToken>.Instance)
    parser.expression()

[<Fact>]
let ``simple addition`` () =
    let tree = parseExpression "1 + 2"
    let expr = RustVisitor().Visit(tree)
    match expr with
    | Op("+", Integer 1L, Integer 2L) -> ()
    | _ -> failwithf "Expected Op(\"+\", Integer 1, Integer 2), got %A" expr

[<Fact>]
let ``assignment expression`` () =
    let tree = parseExpression "a = 42"
    let expr = RustVisitor().Visit(tree)
    match expr with
    | Op("=", Var "a", Integer 42L) -> ()
    | _ -> failwithf "Expected Op(\"=\", Var \"a\", Integer 42), got %A" expr

[<Fact>]
let ``comment terminal`` () =
    let token = CommonToken(RustParser.LINE_COMMENT, "// comment")
    let node = TerminalNodeImpl(token)
    let expr = RustVisitor().VisitTerminal(node)
    Assert.Equal(Comment "// comment", expr)