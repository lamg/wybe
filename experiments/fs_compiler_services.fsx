#r "nuget: FSharp.Compiler.Service, 43.9.300"

open FSharp.Compiler.Tokenization

let src = FSharpSourceTokenizer([], Some "fib_proof.fsx", Some "8.0", None)

let tokenizer = src.CreateLineTokenizer("let answer=42")

/// Tokenize a single line of F# code
let rec tokenizeLine (tokenizer: FSharpLineTokenizer) state =
  match tokenizer.ScanToken(state) with
  | Some tok, state ->
    // Print token name
    printf "%s " tok.TokenName
    // Tokenize the rest, in the new state
    tokenizeLine tokenizer state
  | None, state -> printfn "";state

tokenizeLine tokenizer FSharpTokenizerLexState.Initial

let lines = """
  // Hello world
  let hello() =
     printfn "Hello world!" """.Split('\r','\n')

/// Print token names for multiple lines of code
let rec tokenizeLines state count lines = 
  match lines with
  | line::lines ->
      // Create tokenizer & tokenize single line
      printf "Line %d: " count
      let tokenizer = src.CreateLineTokenizer(line)
      let state = tokenizeLine tokenizer state
      // Tokenize the rest using new state
      tokenizeLines state (count+1) lines
  | [] -> ()

lines
|> List.ofSeq
|> tokenizeLines FSharpTokenizerLexState.Initial 1
