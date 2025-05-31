open Argu

type Args =
  | [<AltCommandLine("-e")>] Extract of string
  | [<AltCommandLine("-v")>] Version
  | [<AltCommandLine("-c")>] Check of string

  interface IArgParserTemplate with
    member s.Usage =
      match s with
      | Extract _ -> "extract proof obligations"
      | Version -> "Prints Wybe's version"
      | Check _ -> "check the proofs in a Wybe fsx script"

// let extract (path: string) =
//   let baseName = System.IO.Path.GetFileName path
//   let fsScript = $"{baseName}.fsx"

//   if baseName = "example_functions.rs" then
//     Emitter.solanaDemo ()
//   else
//     Emitter.parseAndEmitObligations path fsScript

//   0

let version () =
  let asm = System.Reflection.Assembly.GetExecutingAssembly()

  let version = asm.GetName().Version
  printfn $"{version.Major}.{version.Minor}.{version.Build}"
  0

// let check (path: string) =
//   let session, sbOut, sbErr = Runner.createSession ()
//   session.EvalScript path
//   let out = sbOut.ToString()
//   let err = sbErr.ToString()
//   printfn $"{err}"
//   printfn $"{out}"
//   // TODO extract proof obligations and filter by those already fulfilled
//   // for the non-fulfilled ones add them if they don't exist
//   session |> Runner.filterProofs |> Runner.runFunctions session

//   let out = sbOut.ToString()
//   let err = sbErr.ToString()
//   printfn $"{err}"
//   printfn $"{out}"

//   0

[<EntryPoint>]
let main args =

  let errorHandler =
    ProcessExiter(
      colorizer =
        function
        | ErrorCode.HelpText -> None
        | _ -> Some System.ConsoleColor.Red
    )

  let parser =
    ArgumentParser.Create<Args>(programName = "wybe", errorHandler = errorHandler)

  let results = parser.ParseCommandLine(inputs = args, raiseOnUsage = true)


  try
    match true with
    | _ when results.Contains Version -> version ()
    //  | _ when results.Contains Extract -> <@ Extract @> |> results.TryGetResult |> _.Value |> extract
    //    | _ when results.Contains Check -> <@ Check @> |> results.TryGetResult |> _.Value |> check
    | _ ->
      eprintfn "unrecognized argument"
      1
  with e ->
    eprintfn $"{e.Message}"
    1
