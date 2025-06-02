#r "nuget: FSharp.Compiler.Service, 43.9.300"

open FSharp.Compiler.Tokenization

/// Tokenize a single line of F# code
let rec tokenizeLine (tokenizer: FSharpLineTokenizer) state =
  match tokenizer.ScanToken(state) with
  | Some tok, state ->
    // Print token name
    printf "%s " tok.TokenName
    // Tokenize the rest, in the new state
    tokenizeLine tokenizer state
  | None, state ->
    printfn ""
    state

let tokenizingExample () =
  let src = FSharpSourceTokenizer([], Some "fib_proof.fsx", Some "8.0", None)
  
  let lines =
    """
    // Hello world
    let hello() =
       printfn "Hello world!" """
      .Split('\r', '\n')
  
  /// Print token names for multiple lines of code
  let rec tokenizeLines state count lines =
    match lines with
    | line :: lines ->
      // Create tokenizer & tokenize single line
      printf "Line %d: " count
      let tokenizer = src.CreateLineTokenizer(line)
      let state = tokenizeLine tokenizer state
      // Tokenize the rest using new state
      tokenizeLines state (count + 1) lines
    | [] -> ()
  
  lines |> List.ofSeq |> tokenizeLines FSharpTokenizerLexState.Initial 1

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Text

let checker = FSharpChecker.Create()

let getUntypedTree (file, input) =
  // Get compiler options for the 'project' implied by a single script file
  let projOptions, diagnostics =
    checker.GetProjectOptionsFromScript(file, input, assumeDotNetFramework = false)
    |> Async.RunSynchronously

  let parsingOptions, _errors =
    checker.GetParsingOptionsFromProjectOptions(projOptions)

  // Run the first phase (untyped parsing) of the compiler
  let parseFileResults =
    checker.ParseFile(file, input, parsingOptions) |> Async.RunSynchronously

  parseFileResults.ParseTree

open FSharp.Compiler.Syntax

// Walk over a pattern - this is for example used in
/// let <pat> = <expr> or in the 'match' expression
let rec visitPattern =
  function
  | SynPat.Wild _ -> printfn "  .. underscore pattern"
  | SynPat.Named(ident = SynIdent(ident = name)) -> printfn "  .. named as '%s'" name.idText
  | SynPat.LongIdent(longDotId = SynLongIdent(id = ident)) ->
    let names = String.concat "." [ for i in ident -> i.idText ]
    printfn "  .. identifier: %s" names
  | pat -> printfn "  .. other pattern: %A" pat

/// Walk over an expression - if expression contains two or three
/// sub-expressions (two if the 'else' branch is missing), let expression
/// contains pattern and two sub-expressions
let rec visitExpression e =
  match e with
  | SynExpr.IfThenElse(ifExpr = cond; thenExpr = trueBranch; elseExpr = falseBranchOpt) ->
    // Visit all sub-expressions
    printfn "Conditional:"
    visitExpression cond
    visitExpression trueBranch
    falseBranchOpt |> Option.iter visitExpression

  | SynExpr.LetOrUse(_, _, bindings, body, _, _) ->
    // Visit bindings (there may be multiple
    // for 'let .. = .. and .. = .. in ...'
    printfn "LetOrUse with the following bindings:"

    for binding in bindings do
      let (SynBinding(headPat = headPat; expr = init)) = binding
      visitPattern headPat
      visitExpression init
    // Visit the body expression
    printfn "And the following body:"
    visitExpression body
  | expr -> printfn " - not supported expression: %A" expr

/// Walk over a list of declarations in a module. This is anything
/// that you can write as a top-level inside module (let bindings,
/// nested modules, type declarations etc.)
let visitDeclarations decls =
  for declaration in decls do
    match declaration with
    | SynModuleDecl.Let(isRec, bindings, range) ->
      // Let binding as a declaration is similar to let binding
      // as an expression (in visitExpression), but has no body
      for binding in bindings do
        let (SynBinding(headPat = pat; expr = body)) = binding
        visitPattern pat
        visitExpression body
    | _ -> printfn " - not supported declaration: %A" declaration

/// Walk over all module or namespace declarations
/// (basically 'module Foo =' or 'namespace Foo.Bar')
/// Note that there is one implicitly, even if the file
/// does not explicitly define it..
let visitModulesAndNamespaces modulesOrNss =
  for moduleOrNs in modulesOrNss do
    let (SynModuleOrNamespace(longId = lid; decls = decls)) = moduleOrNs
    printfn "Namespace or module: %A" lid
    visitDeclarations decls

// Sample input for the compiler service
let input =
  """
  let foo() = 
    let msg = "Hello world"
    if true then 
      printfn "%s" msg
  """

// File name in Unix format
let file = "/home/user/Test.fsx"

// Get the AST of sample F# code
let tree = getUntypedTree(file, SourceText.ofString input)

// Extract implementation file details
match tree with
| ParsedInput.ImplFile(implFile) ->
    // Extract declarations and walk over them
    let (ParsedImplFileInput(contents = modules)) = implFile
    visitModulesAndNamespaces modules
| _ -> failwith "F# Interface file (*.fsi) not supported."
