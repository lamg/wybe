module Extractor.Runner

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

/// Load an F# script file (.fsx) into the session.
let loadScript (session: FsiEvaluationSession) (scriptPath: string) : unit = session.EvalScript(scriptPath)

/// Evaluate an expression in the session, returning an FsiValue option.
let evalExpression (session: FsiEvaluationSession) (expr: string) = session.EvalExpression(expr)

/// Get captured standard output from the session.
let getStdOut (sbOut: StringBuilder) : string = sbOut.ToString()

/// Get captured standard error from the session.
let getStdErr (sbErr: StringBuilder) : string = sbErr.ToString()

/// Convenience: load a script and evaluate an expression.
let run (scriptPath: string) (expr: string) =
  let session, sbOut, sbErr = createSession ()
  session.EvalScript scriptPath
  let result = session.EvalExpression expr
  result, sbOut.ToString(), sbErr.ToString()

/// Find all top-level functions in an F# script
/// whose type is unit -> CheckedCalculation.
let filterProofs (scriptPath: string) : string list =
  // Initialize session and load the script
  let session, _, _ = createSession ()
  session.EvalScript scriptPath
  // Collect all bound values (name and FsiValue)
  let bound = session.GetBoundValues()

  bound
  |> Seq.choose (fun (bv: FsiBoundValue) ->
    // Value is an option containing the evaluated F# value
    let ty = bv.Value.ReflectionType
    // Filter F# functions of type unit -> CheckedCalculation
    if
      ty.IsGenericType
      && ty.GetGenericTypeDefinition() = typedefof<Microsoft.FSharp.Core.FSharpFunc<_, _>>
    then
      let args = ty.GetGenericArguments()

      if
        args.Length = 2
        && args.[0] = typeof<unit>
        && args.[1] = typeof<Core.CheckedCalculation>
      then
        Some bv.Name
      else
        None
    else
      None)
  |> Seq.toList

/// Run each function in the given list within the specified F# Interactive session,
/// piping the result of each function application to printCalculationResult.
let runFunctions (session: FsiEvaluationSession) (functionNames: string list) : unit =
  functionNames
  |> List.iter (fun name ->
    let code = $"{name}() |> Inspect.printCalculationResult"
    session.EvalInteraction code)
