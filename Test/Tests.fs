module Tests

open Xunit
open FSharp.Text.Lexing
open Predicate

let parse source =
  let lexbuf = LexBuffer<char>.FromString source
  let res = Parser.start Lexer.read lexbuf

  match res with
  | Some ast -> ast
  | None -> failwith "failed to parse"

[<Fact>]
let ``basic constructions`` () =
  [ "true", True
    "false", False
    "id", Var "id"
    "¬false", (Not False)
    "true ∧ false", And { left = True; right = False }
    "true ∨ false", Or { left = True; right = False }
    "true ⇒ false", Implies { left = True; right = False }
    "true ⇐ false", Follows { left = True; right = False }
    "true ≡ false", Equivales { left = True; right = False }
    "true ≢ false", Differs { left = True; right = False } ]
  |> List.iter (fun (source, res) -> Assert.Equal(res, parse source))
