open Argu

type Args =
  | [<CliPrefix(CliPrefix.None)>] Extract of ParseResults<ExtractArgs>
  | [<AltCommandLine("-v")>] Version

  interface IArgParserTemplate with
    member s.Usage =
      match s with
      | Extract _ -> "extract proof obligations"
      | Version -> "Prints Wybe's version"

and ExtractArgs =
  | [<AltCommandLine("-p")>] Path of string

  interface IArgParserTemplate with
    member s.Usage =
      match s with
      | Path _ -> "path of rust file to extract proof obligations"

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

  let command = results.TryGetSubCommand()

  try
    match command with
    | _ when results.Contains Version -> version ()
    | Some(Extract _) ->
      printfn "extract!"
      0
    | _ ->
      eprintfn "unrecognized argument"
      1
  with e ->
    eprintfn $"{e.Message}"
    1
