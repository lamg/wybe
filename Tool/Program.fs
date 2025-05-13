open Argu

type Args =
  | [<AltCommandLine("-e")>] Extract of string
  | [<AltCommandLine("-v")>] Version

  interface IArgParserTemplate with
    member s.Usage =
      match s with
      | Extract _ -> "extract proof obligations"
      | Version -> "Prints Wybe's version"

let extract (path: string) =
  let baseName = System.IO.Path.GetFileNameWithoutExtension path
  let fsScript = $"{baseName}.fsx"
  Extractor.Emitter.parseFileAndEmitProofObligations path fsScript
  0

let version () =
  let asm = System.Reflection.Assembly.GetExecutingAssembly()

  let version = asm.GetName().Version
  printfn $"{version.Major}.{version.Minor}.{version.Build}"
  0

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
    match results.TryGetResult Extract with
    | _ when results.Contains Version -> version ()
    | Some path -> extract path
    | _ ->
      eprintfn "unrecognized argument"
      1
  with e ->
    eprintfn $"{e.Message}"
    1
