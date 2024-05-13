module Tests

open Xunit
open FSharp.Text.Lexing
open Language

let parse source =
  let lexbuf = LexBuffer<char>.FromString source
  Parser.start Lexer.read lexbuf

let pred p =
  { name = "x"
    statements = [ Law(Axiom { name = "t"; pred = p }) ] }

let theorem name p =
  { name = "x"
    statements = [ Law(Theorem({ name = name; pred = p })) ] }

let axiom name p =
  { name = "x"
    statements = [ Law(Axiom({ name = name; pred = p })) ] }

let equiv x y =
  Equivales { left = Ident x; right = Ident y }

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
  [ "module x ax t true", pred trueExpr
    "module x ax t false", pred falseExpr
    "module x ax t id", pred (Ident "id")
    "module x ax t ¬false", pred (Not falseExpr)
    "module x ax t true ∧ false", pred (And { left = trueExpr; right = falseExpr })
    "module x ax t true ∨ false", pred (Or { left = trueExpr; right = falseExpr })
    "module x ax t true ⇒ false", pred (Implies { left = trueExpr; right = falseExpr })
    "module x ax t true ⇐ false", pred (Follows { left = trueExpr; right = falseExpr })
    "module x ax t true ≡ false", pred (Equivales { left = trueExpr; right = falseExpr })
    "module x ax t true ≢ false", pred (Differs { left = trueExpr; right = falseExpr }) ]
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
  [ "module x th m a ≡ b", theorem "m" (Equivales { left = Ident "a"; right = Ident "b" })
    "module x ax m a ≡ b", axiom "m" (Equivales { left = Ident "a"; right = Ident "b" }) ]
  |> List.iter (fun (source, res) -> Assert.Equal(res, parse source))


[<Fact>]
let ``type declaration`` () =
  [ "module x type bool = true | false", { name = "x"; statements = [ TypeDecl { name = "bool"; values = [ Value "true"; Value "false" ] } ] } ]
  |> List.iter (fun (source, res) -> Assert.Equal(res, parse source))

[<Fact>]
let ``proofs`` () =
  [ proof0,
    { name = "x"
      statements =
        [ Proof
            { thesis = equiv "a" "b"
              steps =
                [ { pred = equiv "c" "d"
                    trans =
                      Trans
                        { operator = HintEquivales
                          lawNames = [ "t0" ] } }
                  { pred = equiv "a" "b"; trans = End } ] } ] } ]
  |> List.iter (fun (source, res) -> Assert.Equal(res, parse source))
