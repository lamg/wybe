#r "nuget: FSharp.Compiler.Service, 43.9.300"

open FSharp.Compiler.Tokenization

let src = FSharpSourceTokenizer([], Some "fib_proof.fsx", Some "8.0", None)

let tokenizer = src.CreateLineTokenizer("let answer=42")

/// Tokenize a single line of F# code
let rec tokenizeLine state =
  match tokenizer.ScanToken(state) with
  | Some tok, state ->
    // Print token name
    printf "%s " tok.TokenName
    // Tokenize the rest, in the new state
    tokenizeLine state
  | None, state -> state

tokenizeLine FSharpTokenizerLexState.Initial
