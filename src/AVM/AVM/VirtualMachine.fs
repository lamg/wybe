module AVM.VirtualMachine

type Value =
  | Num of uint64
  | Bytes of array<byte>

type Address = uint64

type Instruction =
  | Add
  | Sub
  | Mul
  | Div
  | Not
  | PushInt of uint64
  | PushBytes of byte
  | Dup
  | Pop
  | Load of Address
  | Loads
  | Store of Address
  | Swap
  | B of string
  | Bnz of string
  | Bz of string
  | Label of string
  | Retsub
  | Callsub of string
  | Return

type Context =
  { instructions: Instruction array
    programCounter: uint
    scratch: Map<Address, Value>
    returnStack: uint list // stack storing the next instruction after each subroutine call
    stack: Value list }

let arithmeticInstructions = [ Add; Sub; Mul; Div ]
let isArithmetic (x: Instruction) = List.contains x arithmeticInstructions

let booleanInstructions = [ Not ]
let isBoolean (x: Instruction) = List.contains x booleanInstructions

let currentInstruction ctx =
  ctx.instructions[int ctx.programCounter]

let executeArithmetic ctx =
  let inst = currentInstruction ctx

  match inst with
  | Add -> (+)
  | Sub -> (-)
  | Mul -> (*)
  | Div -> (/)
  | x -> failwith $"instruction {x} should be one of {arithmeticInstructions}"
  |> fun f ->
    match ctx.stack with
    | Num y :: Num x :: tail ->
      { ctx with
          stack = Num(f x y) :: tail
          programCounter = ctx.programCounter + 1ul }
    | _ -> ctx

let findLabel (program: Instruction array) (label: string) =
  program
  |> Array.tryFindIndex (function
    | Label l when l = label -> true
    | _ -> false)
  |> function
    | Some n -> uint n
    | None -> failwith $"could not find label {label}"

let incPC ctx =
  { ctx with
      programCounter = ctx.programCounter + 1ul }

let jumpTo label ctx =
  { ctx with
      programCounter = findLabel ctx.instructions label }

let pcToReturnStack ctx =
  { ctx with
      returnStack = ctx.programCounter :: ctx.returnStack }

let step (ctx: Context) =
  let inst = currentInstruction ctx

  match inst with
  | x when isArithmetic x -> executeArithmetic ctx
  | x when isBoolean x -> ctx
  | PushInt v ->
    { ctx with
        stack = (Num v) :: ctx.stack }
    |> incPC
  | Dup ->
    match ctx.stack with
    | x :: xs -> { ctx with stack = x :: x :: xs } |> incPC
    | _ -> failwith $"Dup expects an non-empty stack"
  | Pop when ctx.stack.Length > 0 -> { ctx with stack = ctx.stack.Tail } |> incPC
  | Load s when ctx.scratch.ContainsKey s ->
    { ctx with
        stack = ctx.scratch[s] :: ctx.stack }
    |> incPC
  | Store s when ctx.stack.Length > 0 ->
    { ctx with
        stack = ctx.stack.Tail
        scratch = Map.add s ctx.stack.Head ctx.scratch }
    |> incPC
  | Callsub label -> ctx |> pcToReturnStack |> jumpTo label
  | Retsub ->
    match ctx.returnStack with
    | pc :: tail ->
      { ctx with
          returnStack = tail
          programCounter = pc + 1ul }
    | [] -> failwith "return stack underflow"
  | B label -> ctx |> jumpTo label
  | Bz label ->
    match ctx.stack with
    | Num 0UL :: tail -> { ctx with stack = tail } |> jumpTo label
    | _ :: tail -> { ctx with stack = tail } |> incPC
    | _ -> failwith "stack underflow, bz expects at least an element in the stack"
  | Bnz label ->
    match ctx.stack with
    | Num n :: tail when n <> 0UL -> { ctx with stack = tail } |> jumpTo label
    | _ :: tail -> { ctx with stack = tail } |> incPC
    | _ -> failwith "stack underflow, bz expects at least an element in the stack"
  | Swap ->
    match ctx.stack with
    | x :: y :: tail -> { ctx with stack = y :: x :: tail } |> incPC
    | _ -> failwith "swap needs at least two elements"
  | Loads ->
    match ctx.stack with
    | Num addr :: tail ->
      { ctx with
          stack = ctx.scratch[addr] :: tail }
      |> incPC
    | _ -> failwith "Loads expects at least an element in stack for"
  | Label _ -> incPC ctx
  | x -> failwith $"instruction {x} is not implemented"

let fixedPoint (ok: 'a -> bool) (f: 'a -> 'a) (initial: 'a) =
  let rec loop current =
    if ok current then loop (f current) else current

  loop initial

let execute (ctx: Context) =
  let hasNext ctx =
    ctx.programCounter < uint ctx.instructions.Length

  fixedPoint hasNext step ctx
