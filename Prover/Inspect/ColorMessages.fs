module internal ColorMessages

type Color =
  | BrightRed
  | BrightGreen
  | BrightYellow
  | BrightBlue
  | BrightMagenta

let ansiColor =
  function
  | BrightRed -> "\x1b[91m"
  | BrightGreen -> "\x1b[92m"
  | BrightYellow -> "\x1b[93m"
  | BrightBlue -> "\x1b[94m"
  | BrightMagenta -> "\x1b[95m"


let colorizeString color s =
  let c = ansiColor color
  let ansiReset = "\x1b[0m"
  $"%s{c}%s{s}%s{ansiReset}"

let message (c: Color) (head: string) (body: string) = $"{colorizeString c head}: {body}"

let info head body = message BrightBlue head body
let error head body = message BrightRed head body

let section head = $"{colorizeString BrightYellow head}"
let sectionBody head body = message BrightYellow head body
