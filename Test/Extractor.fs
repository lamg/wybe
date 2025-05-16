module ExtractorTest


open Xunit
open Antlr4.Runtime
open Antlr4.Runtime.Tree
open RustParserCs
open Types
open RustParser
open Emitter

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
  let expr = RustVisitor().Visit tree

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
  let func = (parseFunctions add_one_rust).Head
  // Signature
  Assert.Equal("add_one", func.Name)
  // Expect a list of parameter name-type pairs
  Assert.Equal<list<string * string>>([ ("x", "i32") ], func.Parameters)
  Assert.Equal(Some "i32", func.ReturnType)
  // Body expressions: assertion, arithmetic, assertion
  match func.Body with
  | [ CommentAssertion "x = X"; Op("+", Var "x", Integer 1L); CommentAssertion "x = X + 1" ] -> ()
  | _ -> failwithf "Unexpected function body: %A" func.Body

[<Fact>]
let ``solana style function`` () =
  let sol_fn =
    """
    pub fn do_something(ctx: Context<DoSomething>, amount: u64) -> Result<()> {
      // { amount + 1 }
      amount * 2
    }
    """

  let func = (parseFunctions sol_fn).Head
  // Signature
  Assert.Equal("do_something", func.Name)
  // Two parameters: context and a value
  Assert.Equal<list<string * string>>([ "ctx", "Context<DoSomething>"; "amount", "u64" ], func.Parameters)
  Assert.Equal(Some "Result<()>", func.ReturnType)
  // Body: assertion then multiplication
  match func.Body with
  | [ CommentAssertion "amount + 1"; Op("*", Var "amount", Integer 2L) ] -> ()
  | _ -> failwithf "Unexpected function body: %A" func.Body

// Tests for the ProofEmitter module
[<Fact>]
let ``extract proof obligations`` () =
  // Prepare a dummy function with an assertion and a normal expression
  let funcs =
    [ { Name = "foo"
        Parameters = []
        ReturnType = None
        Body = [ Integer 42L; CommentAssertion "$e > 5" ] } ]

  let obligations = extractProofObligations funcs
  Assert.Equal(1, obligations.Length)

  let fortyTwoExceedsFive =
    Core.Exceeds(Core.Integer 42, Core.Integer 5) :> Core.WExpr |> Core.ExtBoolOp

  Assert.Equal<(string * List<Core.Var> * Core.Proposition) list>([ "foo_0", [], fortyTwoExceedsFive ], obligations)

[<Fact>]
let ``parse and emit`` () =
  let add_one_rust =
    "
    pub fn add_one(x: i32) -> i32 {
      x + 1
      // { $e > x }
    }
    "

  use writer = new System.IO.StringWriter()

  parseAndEmitProofObligations
    { path = ""
      content = add_one_rust
      language = Rust }
    writer

  let fsCode = writer.ToString().Split "\n"

  let expected =
    [| "#r \"nuget: Wybe, 0.0.2\""
       "open Wybe"
       "open Core"
       ""
       ""
       ""
       "let add_one_0 () ="
       ""
       """  proof { theorem "add_one_0" (x + Integer 1 > x) }"""
       ""
       "checkTheorems [ add_one_0 ]"
       "" |]

  Assert.Equal<string array>(expected, fsCode)
