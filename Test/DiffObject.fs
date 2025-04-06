module DiffObject

let greenFragment x =
  let ansiGreen = "\x1b[32m"
  let ansiReset = "\x1b[0m"
  $"%s{ansiGreen}%s{x}%s{ansiReset}"

let redFragment x =
  let ansiRed = "\x1b[31m"
  let ansiReset = "\x1b[0m"
  $"%s{ansiRed}%s{x}%s{ansiReset}"

let fillArrays (xs: string array) (ys: string array) =
  let diff = xs.Length - ys.Length

  if diff > 0 then
    xs, Array.replicate diff "" |> Array.append ys
  else
    Array.replicate (diff * -1) "" |> Array.append xs, ys

let diffSideBySide (actual: string array) (expected: string array) =
  let max = actual |> Array.maxBy _.Length |> _.Length

  let fillLine (x: string) =
    let diff = max - x.Length
    let fill = if diff > 0 then String.replicate diff " " else ""
    $"{x}{fill}"

  fillArrays actual expected
  |> fun (xs, ys) -> Array.zip xs ys
  |> Array.map (function
    | (x, y) when x <> y -> $"{redFragment (fillLine x)} {greenFragment y}"
    | (x, y) -> $"{fillLine x} {y}")

let diffObjects (expected: 'b) (actual: 'a) =
  let left = ObjectDumper.Dump expected |> _.Split('\n')
  let right = ObjectDumper.Dump actual |> _.Split('\n')
  diffSideBySide left right

let diffAndPrint (expected: 'b) (actual: 'a) =
  diffObjects expected actual |> Array.iter (printfn "%s")
