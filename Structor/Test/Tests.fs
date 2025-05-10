module Tests

open Xunit
open Antlr4.Runtime
open Antlr4.Runtime.Tree
open RustParserCs
open StructorLib.RustParser

/// Helper to parse an expression rule from a string
let parseExpression (input: string) =
  let charStream = CharStreams.fromString input
  let lexer = RustLexer charStream
  let tokens = CommonTokenStream lexer
  let parser = RustParser tokens
  parser.RemoveErrorListeners()
  parser.AddErrorListener(ConsoleErrorListener<IToken>.Instance)
  parser.expression ()

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
  let node = TerminalNodeImpl token
  let expr = RustVisitor().VisitTerminal node
  Assert.Equal(Comment "// comment", expr)

[<Fact>]
let ``simple rust function`` () =
  let add_one_rust =
    "
    pub fn add_one(x: i32) -> i32 {
      // { x = X }
      x + 1
      // { x = X + 1 }
    }
    "
  // Parse the function and validate its structure
  let func = parseFunction add_one_rust
  // Signature
  Assert.Equal("add_one", func.Name)
  // Expect a list of parameter name-type pairs
  Assert.Equal<(string * string) list>([ ("x", "i32") ], func.Parameters)
  Assert.Equal(Some "i32", func.ReturnType)
  // Body expressions: assertion, arithmetic, assertion
  match func.Body with
  | [ CommentAssertion(Op("=", Var "x", Var "X"))
      Op("+", Var "x", Integer 1L)
      CommentAssertion(Op("=", Var "x", Op("+", Var "X", Integer 1L))) ] -> ()
  | _ -> failwithf "Unexpected function body: %A" func.Body
