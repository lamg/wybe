module Tests

open Xunit
open FSharp.Text.Lexing
open Predicate

let parse source =
  let lexbuf = LexBuffer<char>.FromString source
  Parser.start Lexer.read lexbuf

let pred p =
  { name = "x"
    statements = [ Law(Axiom { name = "t"; pred = p }) ] }

[<Fact>]
let ``basic constructions`` () =
  [ "module x ax t true", pred True
    "module x ax t false", pred False
    "module x ax t id", pred (Var "id")
    "module x ax t ¬false", pred (Not False)
    "module x ax t true ∧ false", pred (And { left = True; right = False })
    "module x ax t true ∨ false", pred (Or { left = True; right = False })
    "module x ax t true ⇒ false", pred (Implies { left = True; right = False })
    "module x ax t true ⇐ false", pred (Follows { left = True; right = False })
    "module x ax t true ≡ false", pred (Equivales { left = True; right = False })
    "module x ax t true ≢ false", pred (Differs { left = True; right = False }) ]
  |> List.iter (fun (source, res) -> Assert.Equal(res, parse source))
