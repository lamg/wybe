module Runner

open System
open System.IO
open System.Text
open FSharp.Compiler.Interactive.Shell

/// Create and configure a new F# Interactive session.
let createSession () : FsiEvaluationSession * StringBuilder * StringBuilder =
  let sbOut = StringBuilder()
  let sbErr = StringBuilder()
  let inStream = new StringReader ""
  let outStream = new StringWriter(sbOut)
  let errStream = new StringWriter(sbErr)
  let fsiConfig = FsiEvaluationSession.GetDefaultConfiguration()
  let argv = [| "fsi.exe"; "--noninteractive" |]

  let session =
    FsiEvaluationSession.Create(fsiConfig, argv, inStream, outStream, errStream)

  session, sbOut, sbErr

/// Find all top-level functions in an F# script
/// whose type is unit -> CheckedCalculation.
let filterProofs (session: FsiEvaluationSession) =
  // Initialize session and load the script
  // Collect all bound values (name and FsiValue)
  let bound = session.GetBoundValues()
  // let v = session.EvalExpression "``hola mundo`` ()"
  // printfn $"v {v}"

  printfn $"bounds {bound.Length}"

  bound
  |> Seq.choose (fun (bv: FsiBoundValue) ->
    // Value is an option containing the evaluated F# value
    let ty = bv.Value.ReflectionType
    printfn $"ty {ty}"
    // Filter F# functions of type unit -> CheckedCalculation
    if
      ty.IsGenericType
      && ty.GetGenericTypeDefinition() = typedefof<Microsoft.FSharp.Core.FSharpFunc<_, _>>
    then
      let args = ty.GetGenericArguments()
      printfn $"args {args}"

      if args.Length = 1 && args[0] = typeof<unit> then
        Some bv.Name
      else
        None
    else
      None)
  |> Seq.toList

/// Run each function in the given list within the specified F# Interactive session,
/// piping the result of each function application to printCalculationResult.
let runFunctions (session: FsiEvaluationSession) (functionNames: string list) =
  printfn $"{functionNames}"

  functionNames
  |> List.iter (fun name ->
    let code = $"{name}() |> Inspect.printCalculationResult"
    session.EvalInteraction code)
