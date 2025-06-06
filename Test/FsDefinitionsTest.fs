module FsDefinitionsTest

open Xunit
open FsDefinitions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Text

let checker = FSharpChecker.Create(keepAssemblyContents=true)

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

//IfThenElse
//  (UnionCaseTest
//  (Value val _arg1,
//   type Microsoft.FSharp.Collections.List<Microsoft.FSharp.Core.int>, Cons),
//   IfThenElse
//  (Let
//  ((val xs,
//    UnionCaseGet
//  (Value val _arg1,
//   type Microsoft.FSharp.Collections.List<Microsoft.FSharp.Core.int>, Cons,
//   field Tail),
//    NoneAtInvisible),
//   Let
//  ((val x,
//    UnionCaseGet
//  (Value val _arg1,
//   type Microsoft.FSharp.Collections.List<Microsoft.FSharp.Core.int>, Cons,
//   field Head),
//    NoneAtInvisible),
//   Call
//  (None, val op_LessThanOrEqual, [], [type Microsoft.FSharp.Core.int], [],
//   [Value val n; Value val x]))),
//   DecisionTreeSuccess
//  (1,
//   [UnionCaseGet
//  (Value val _arg1,
//   type Microsoft.FSharp.Collections.List<Microsoft.FSharp.Core.int>, Cons,
//   field Head);
//    UnionCaseGet
//  (Value val _arg1,
//   type Microsoft.FSharp.Collections.List<Microsoft.FSharp.Core.int>, Cons,
//   field Tail)]),
//   DecisionTreeSuccess
//  (2,
//   [UnionCaseGet
//  (Value val _arg1,
//   type Microsoft.FSharp.Collections.List<Microsoft.FSharp.Core.int>, Cons,
//   field Head);
//    UnionCaseGet
//  (Value val _arg1,
//   type Microsoft.FSharp.Collections.List<Microsoft.FSharp.Core.int>, Cons,
//   field Tail)])),
//   DecisionTreeSuccess (0, [])) guard UnionCaseTest
//  (Value val _arg1,
//   type Microsoft.FSharp.Collections.List<Microsoft.FSharp.Core.int>, Cons)

[<Fact>]
let ``extract propositions from insert function`` () = 
  let file = "insert.fsx"
  let insert = """
let rec insert (n: int) =
 function
 | [] -> [ n ]
 | x :: xs when n <= x -> n :: x :: xs
 | x :: xs -> x :: insert n xs"""
  let _, res = parseAndTypeCheckSingleFile(file, SourceText.ofString insert)
  match res.ImplementationFile with
  | Some m when m.Declarations.Length > 0->
    let props = m.Declarations |> List.collect getDeclaration
    Assert.True(props.Length > 0)
  | _ -> Assert.Fail "expecting at least one declaration"
