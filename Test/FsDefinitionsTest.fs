module FsDefinitionsTest

open Xunit
open FsDefinitions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Text

let checker = FSharpChecker.Create(keepAssemblyContents = true)

let parseAndTypeCheckSingleFile (file, input) =
  // Get context representing a stand-alone (script) file
  let projOptions, errors =
    checker.GetProjectOptionsFromScript(file, input, assumeDotNetFramework = false)
    |> Async.RunSynchronously

  let parseFileResults, checkFileResults =
    checker.ParseAndCheckFileInProject(file, 0, input, projOptions)
    |> Async.RunSynchronously

  // Wait until type checking succeeds (or 100 attempts)
  match checkFileResults with
  | FSharpCheckFileAnswer.Succeeded(res) -> parseFileResults, res
  | res -> failwithf "Parsing did not finish... (%A)" res

open Core
open GriesSchneider

#nowarn 86


[<Fact>]
let ``extract typed variables from insert function`` () =
  let file = "insert.fsx"

  let source =
    """
let rec insert (n: int) =
 function
 | [] -> [ n ]
 | x :: xs when n <= x -> n :: x :: xs
 | x :: xs -> x :: insert n xs"""

  // let decl = Fn("insert", [ WInt; WSeq WInt; WSeq WInt ])
  // let insert (n, xs) = ExtSeq(App(decl, [ n; xs ]))

  let _, res = parseAndTypeCheckSingleFile (file, SourceText.ofString source)

  let (>) = FSharp.Core.Operators.(>)

  match res.ImplementationFile with
  | Some m when m.Declarations.Length > 0 ->
    let vars, errs = m.Declarations |> List.collect toDeclTriples |> getDeclVars

    let expected =
      [ Var("n", WInt)
        Var("_arg1", WSeq WInt)
        Var("xs", WSeq WInt)
        Var("x", WInt) ]

    Assert.Equal<Var list>(expected, vars)
    Assert.Equal<string list>([], errs)
  | _ -> Assert.Fail "expecting at least one declaration"

[<Fact>]
let ``extract from failwith`` () =
  let file = "failwith.fsx"

  let source =
    """
let fw (n: int) =
  function
  | ([]: int list) -> [ n ]
  | _ -> failwith "non empty list"
  """

  //let fw (n: WExpr, xs: WExpr) =
  //  let declFw = Fn("fw", [ WInt; WSeq WInt; WSeq WInt ])
  //  ExtSeq(App(declFw, [ n; xs ]))

  let (>) = FSharp.Core.Operators.(>)
  let _, res = parseAndTypeCheckSingleFile (file, SourceText.ofString source)

  match res.ImplementationFile with
  | Some m when m.Declarations.Length > 0 ->
    let vars, errs = m.Declarations |> List.collect toDeclTriples |> getDeclVars

    let expected = [ Var("n", WInt); Var("_arg1", WSeq WInt) ]

    Assert.Equal<string list>([], errs)
    Assert.Equal<Var list>(expected, vars)
  | _ -> Assert.Fail "expecting at least one declaration"
