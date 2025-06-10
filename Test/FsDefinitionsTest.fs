module FsDefinitionsTest

open Xunit
open FsDefinitions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Text
open FSharp.Compiler.Syntax

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

  let parseRes, checkRes =
    parseAndTypeCheckSingleFile (file, SourceText.ofString source)

  let (>) = FSharp.Core.Operators.(>)

  match checkRes.ImplementationFile with
  | Some m when m.Declarations.Length > 0 ->
    let decls = m.Declarations |> List.collect toDeclTriples |> getFunDecls
    
    let vars =
      [ { name = "n"; sort = WInt }
        { name = "_arg1"; sort = WSeq WInt }
        { name = "xs"; sort = WSeq WInt }
        { name = "x"; sort = WInt } ]

    let expected = [ Fn("insert", [ WInt; WSeq WInt; WSeq WInt ]), vars, [] ]

    Assert.Equal<List<Core.Function * Var list * string list>>(expected, decls)

    match parseRes.ParseTree with
    | ParsedInput.ImplFile f ->
      let fsExprs = getModuleOrNssExpressions f.Contents
      Assert.Equal(1, fsExprs.Length)
      let fnDecls = decls |> List.map (fun (fn, _,_) -> fn)
      fsExprs
      |> List.iter (fun (value, headPat, expr) ->
        let fn = headPatToFun vars (value, headPat)
        let fctx = { fnDecls = fnDecls; fn = fn; vars = vars }
        let exprs = visitExpression fctx expr
        printfn $"EXPRS {exprs}"
        Assert.True(exprs.Length > 0))
    | _ -> failwith "expecting implementation file"
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

  let (>) = FSharp.Core.Operators.(>)
  let _, res = parseAndTypeCheckSingleFile (file, SourceText.ofString source)

  match res.ImplementationFile with
  | Some m when m.Declarations.Length > 0 ->
    let decls = m.Declarations |> List.collect toDeclTriples |> getFunDecls

    let expected =
      [ Core.Fn("fw", [ WInt; WSeq WInt; WSeq WInt ]),
        [ { name = "n"; sort = WInt }; { name = "_arg1"; sort = WSeq WInt } ],
        [] ]

    Assert.Equal<List<Core.Function * Var list * string list>>(expected, decls)
  | _ -> Assert.Fail "expecting at least one declaration"
