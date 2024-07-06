module Tests

open Xunit
open FSharp.Text.Lexing
open Language

let parse source =
  let lexbuf = LexBuffer<char>.FromString source
  Parser.start Lexer.read lexbuf

let expr p =
  { name = "x"
    statements = [ Law(Axiom { name = "t"; expr = p }) ] }

let theorem name p =
  { name = "x"
    statements = [ Law(Theorem({ name = name; expr = p })) ] }

let axiom name p =
  { name = "x"
    statements = [ Law(Axiom({ name = name; expr = p })) ] }

let equiv x y =
  Binary
    { operator = "≡"
      left = Ident x
      right = Ident y }

let binaryTF operator =
  Binary
    { operator = operator
      left = Ident "true"
      right = Ident "false" }
  |> expr

let proof0 =
  "
module x

proof a ≡ b
c ≡ d
≡ { t0 }
a ≡ b
□
"

let falseExpr = Ident "false"
let trueExpr = Ident "true"

[<Fact>]
let ``basic constructions`` () =
  [ "module x ax t true", expr trueExpr
    "module x ax t false", expr falseExpr
    "module x ax t id", expr (Ident "id")
    "module x ax t ¬false", expr (Unary { operator = "¬"; expr = falseExpr })
    "module x ax t true ∧ false", binaryTF "∧"
    "module x ax t true ∨ false", binaryTF "∨"
    "module x ax t true ⇒ false", binaryTF "⇒"
    "module x ax t true ⇐ false", binaryTF "⇐"
    "module x ax t true ≡ false", binaryTF "≡"
    "module x ax t true ≢ false", binaryTF "≢" ]
  |> List.iter (fun (source, res) -> Assert.Equal(res, parse source))

[<Fact>]
let ``identifier`` () =
  [ "module x0 open y1",
    { name = "x0"
      statements = [ Open "y1" ] }
    "module x0x0 open y1y1",
    { name = "x0x0"
      statements = [ Open "y1y1" ] } ]
  |> List.iter (fun (source, res) -> Assert.Equal(res, parse source))

[<Fact>]
let ``open statement`` () =
  [ "module x open y",
    { name = "x"
      statements = [ Open "y" ] } ]
  |> List.iter (fun (source, res) -> Assert.Equal(res, parse source))

[<Fact>]
let ``laws`` () =
  [ "module x th m a ≡ b",
    theorem
      "m"
      (Binary
        { operator = "≡"
          left = Ident "a"
          right = Ident "b" })
    "module x ax m a ≡ b",
    axiom
      "m"
      (Binary
        { operator = "≡"
          left = Ident "a"
          right = Ident "b" }) ]
  |> List.iter (fun (source, res) -> Assert.Equal(res, parse source))


[<Fact>]
let ``type declaration`` () =
  [ "module x type bool = true | false",
    { name = "x"
      statements =
        [ TypeDecl
            { name = "bool"
              values = [ Value "true"; Value "false" ] } ] } ]
  |> List.iter (fun (source, res) -> Assert.Equal(res, parse source))

[<Fact>]
let ``proofs`` () =
  [ proof0,
    { name = "x"
      statements =
        [ Proof
            { thesis = equiv "a" "b"
              steps =
                [ { expr = equiv "c" "d"
                    trans = Trans { operator = "≡"; lawNames = [ "t0" ] } }
                  { expr = equiv "a" "b"; trans = End } ] } ] } ]
  |> List.iter (fun (source, res) -> Assert.Equal(res, parse source))

[<Fact>]
let ``typeof declarations`` () =
  [ "module x typeof f = bool → bool",
    { name = "x"
      statements =
        [ TypeOfDecl
            { func = "f"
              signature = [ "bool"; "bool" ] } ] }

    "module x typeof ≡ = bool → bool → bool",
    { name = "x"
      statements =
        [ TypeOfDecl
            { func = "≡"
              signature = [ "bool"; "bool"; "bool" ] } ] } ]
  |> List.iter (fun (source, res) -> Assert.Equal(res, parse source))
