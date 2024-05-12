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
  Equivales { left = Var x; right = Var y }

let proof0 =
  "
module x

proof a ≡ b
c ≡ d
≡ { t0 }
a ≡ b
□
"



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
  [ "module x th m a ≡ b", theorem "m" (Equivales { left = Var "a"; right = Var "b" })
    "module x ax m a ≡ b", axiom "m" (Equivales { left = Var "a"; right = Var "b" }) ]
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
