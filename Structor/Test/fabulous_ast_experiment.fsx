#r "nuget: Fabulous.AST"

//#r "../../Wybe/bin/Debug/net9.0/Wybe.dll"

// open Core
// open GriesSchneider.PredicateCalculus
open Fabulous.AST
open type Fabulous.AST.Ast



Oak() { AnonymousModule() { Value("x", "12") } }
|> Gen.mkOak
|> Gen.run
|> printfn "%s"


Oak() {
  AnonymousModule() {
    NamedComputationExpr(
      ConstantExpr(Constant "proof"),
      CompExprBodyExpr [ AppExpr("lemma", [ String "theorem body" ]) ]
    )
  }
}
|> Gen.mkOak
|> Gen.run
|> printfn "%s"
