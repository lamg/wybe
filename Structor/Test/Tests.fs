module Tests

open Xunit
open Antlr4.Runtime
open Antlr4.Runtime.Tree
open RustParserCs
open Structor.Types
open Structor.RustParser
open Structor.ProofEmitter

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
  let func = parseFunction add_one_rust
  // Signature
  Assert.Equal("add_one", func.Name)
  // Expect a list of parameter name-type pairs
  Assert.Equal<list<string * string>>([ ("x", "i32") ], func.Parameters)
  Assert.Equal(Some "i32", func.ReturnType)
  // Body expressions: assertion, arithmetic, assertion
  match func.Body with
  | [ CommentAssertion(Op("=", Var "x", Var "X"))
      Op("+", Var "x", Integer 1L)
      CommentAssertion(Op("=", Var "x", Op("+", Var "X", Integer 1L))) ] -> ()
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

  let func = parseFunction sol_fn
  // Signature
  Assert.Equal("do_something", func.Name)
  // Two parameters: context and a value
  Assert.Equal<list<string * string>>([ "ctx", "Context<DoSomething>"; "amount", "u64" ], func.Parameters)
  Assert.Equal(Some "Result<()>", func.ReturnType)
  // Body: assertion then multiplication
  match func.Body with
  | [ CommentAssertion(Op("+", Var "amount", Integer 1L)); Op("*", Var "amount", Integer 2L) ] -> ()
  | _ -> failwithf "Unexpected function body: %A" func.Body

// Tests for the ProofEmitter module
[<Fact>]
let ``extract proof obligations`` () =
  // Prepare a dummy function with an assertion and a normal expression
  let funcs =
    [ { Name = "foo"
        Parameters = []
        ReturnType = None
        Body = [ CommentAssertion(Op("=", Var "x", Integer 5L)); Integer 42L ] } ]

  let obligations = extractProofObligations funcs
  Assert.Equal(1, obligations.Length)
  let id, expr = List.head obligations
  Assert.Equal("foo_obl_0", id)

  match expr with
  | Op("=", Var "x", Integer 5L) -> ()
  | _ -> failwithf "Unexpected expr: %A" expr

[<Fact>]
let ``generate proof code`` () =
  let obligations = [ ("bar_obl_0", Op("+", Var "y", Integer 1L)) ]
  let code = generateProofCode obligations
  // Generated code should reference the obligation name, proof block, and the expression
  Assert.Contains("bar_obl_0", code)
  Assert.Contains("proof {", code)
  Assert.Contains("y + 1", code)
