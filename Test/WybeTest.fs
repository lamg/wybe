module WybeTest

open Xunit
open LanguageServices.Wybe
open AST
open Semantics

[<Fact>]
let ``typing simple expression`` () =
  let vars = [ "x", WybeType.Integer; "y", WybeType.Integer ] |> Map.ofList
  let divVars = Binary(Var "x", WybeOp.Div, Var "y")
  let r = extractSemantics vars divVars
  printfn $"{r}"
