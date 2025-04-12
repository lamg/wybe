module TypedExpression

open FSharpPlus
open FsToolkit.ErrorHandling

open ExpressionMatch

type TypeSpec =
  | TypeId of string
  | Fun of TypeSpec list

type Symbol =
  | Free of string
  | Fixed of string // a constant or operator

  override this.ToString() =
    match this with
    | Free x -> x
    | Fixed x -> x

type TypedSymbol = { symbol: Symbol; signature: TypeSpec }

let matchSymbol (x: TypedSymbol) (y: TypedSymbol) =
  match x, y with
  | { symbol = Free _ }, _ when x.signature = y.signature -> true
  | _ -> x = y

type TypingError =
  | ExcessArguments of TypeSpec list
  | Mismatch of TypeSpec * TypeSpec

let calculateType (signature: TypeSpec) (args: TypeSpec list) =
  match signature with
  | TypeId _ when args.Length <> 0 -> ExcessArguments args |> Error
  | Fun signature ->
    let signatureArgs = signature.Length - 1

    match args with
    | _ when args.Length > signatureArgs -> ExcessArguments(args |> List.drop signatureArgs) |> Error
    | _ ->
      args
      |> List.zipShortest signature
      |> List.tryFind (fun (x, y) ->
        match x, y with
        | TypeId t, TypeId s when t = s -> false
        | _ -> x <> y)
      |> function
        | Some(x, y) -> Mismatch(x, y) |> Error
        | None ->
          signature
          |> List.drop args.Length
          |> function
            | [ x ] -> x
            | xs -> Fun xs
          |> Ok
  | TypeId _ -> Ok signature

type TypedExpr = Tree<TypedSymbol>
type TypingResult = Result<TypedExpr, TypingError>

type ITypedExpr =
  abstract member toTypedExpr: unit -> TypingResult

let getTypedExpr x =
  x :> ITypedExpr |> _.toTypedExpr() |> Result.get

let boolId = TypeId "𝔹"

let typedTree symbol (args: TypingResult list) : TypingResult =
  result {
    let! xs = List.sequenceResultM args
    let argTypes = xs |> List.map _.node.signature
    let! t = calculateType symbol.signature argTypes

    return
      { node = { symbol with signature = t }
        subtrees = xs }
  }

type Pred<'a when 'a: equality and 'a :> ITypedExpr> =
  | True
  | False
  | Var of string
  | Bool of 'a
  | Not of right: Pred<'a>
  | And of left: Pred<'a> * right: Pred<'a>
  | Or of left: Pred<'a> * right: Pred<'a>
  | Equiv of left: Pred<'a> * right: Pred<'a>
  | Differs of left: Pred<'a> * right: Pred<'a>
  | Implies of left: Pred<'a> * right: Pred<'a>
  | Follows of left: Pred<'a> * right: Pred<'a>

  interface ITypedExpr with
    member this.toTypedExpr() : TypingResult =
      let binaryOpSignature = Fun [ boolId; boolId; boolId ]
      let atom e = { symbol = e; signature = boolId }

      let symbol, args =
        match this with
        | True -> atom (Fixed "true"), []
        | False -> atom (Fixed "false"), []
        | Var x -> atom (Free x), []
        | Not right ->
          { symbol = Fixed "¬"
            signature = Fun [ boolId; boolId ] },
          [ right :> ITypedExpr |> _.toTypedExpr() ]
        | And(left, right) ->
          { symbol = Fixed "∧"
            signature = binaryOpSignature },
          [ left :> ITypedExpr |> _.toTypedExpr()
            right :> ITypedExpr |> _.toTypedExpr() ]
        | Or(left, right) ->
          { symbol = Fixed "∨"
            signature = binaryOpSignature },
          [ left :> ITypedExpr |> _.toTypedExpr()
            right :> ITypedExpr |> _.toTypedExpr() ]
        | Equiv(left, right) ->
          { symbol = Fixed "≡"
            signature = binaryOpSignature },
          [ left :> ITypedExpr |> _.toTypedExpr()
            right :> ITypedExpr |> _.toTypedExpr() ]
        | Differs(left, right) ->
          { symbol = Fixed "≢"
            signature = binaryOpSignature },
          [ left :> ITypedExpr |> _.toTypedExpr()
            right :> ITypedExpr |> _.toTypedExpr() ]
        | Implies(left, right) ->
          { symbol = Fixed "⇒"
            signature = binaryOpSignature },
          [ left :> ITypedExpr |> _.toTypedExpr()
            right :> ITypedExpr |> _.toTypedExpr() ]
        | Follows(left, right) ->
          { symbol = Fixed "⇐"
            signature = binaryOpSignature },
          [ left :> ITypedExpr |> _.toTypedExpr()
            right :> ITypedExpr |> _.toTypedExpr() ]
        | Bool x ->
          match x :> ITypedExpr |> _.toTypedExpr() with
          | Ok s when s.node.signature = boolId ->
            { symbol = s.node.symbol
              signature = boolId },
            []
          | Ok s -> s.node, [ Error(Mismatch(boolId, s.node.signature)) ]
          | r ->
            { symbol = Fixed "⊥"
              signature = boolId },
            [ r ]

      typedTree symbol args

let equivSymbol =
  { symbol = Fixed "≡"
    signature = Fun [ boolId; boolId; boolId ] }

let impliesSymbol =
  { symbol = Fixed "⇒"
    signature = Fun [ boolId; boolId; boolId ] }

let followsSymbol =
  { symbol = Fixed "⇐"
    signature = Fun [ boolId; boolId; boolId ] }

let (<||>) x y = Or(x, y)
let (<&&>) x y = And(x, y)
let (==>) x y = Implies(x, y)
let (<==) x y = Follows(x, y)
let (===) x y = Equiv(x, y)
let (!==) x y = Differs(x, y)
let (!) e = Not e



type Rel<'a when 'a: equality and 'a :> ITypedExpr> =
  | Transpose of Rel<'a>
  | Compose of left: Rel<'a> * Rel: Pred<'a>
  | Identity
  | Pred of Pred<'a>

  interface ITypedExpr with
    member this.toTypedExpr() : TypingResult = failwith "not impl"

let natId = TypeId "ℕ"

[<RequireQualifiedAccess>]
type Nat =
  | Zero
  | Succ of Nat
  | Var of string

  interface ITypedExpr with
    member this.toTypedExpr() =
      let rec symbolN n =
        match n with
        | Zero -> 0
        | Succ o -> 1 + symbolN o
        | _ -> failwith "expecting constant ℕ, not a variable"

      let symbol =
        match this with
        | Var x -> Free x
        | _ -> Fixed(symbolN this |> _.ToString())

      Ok
        { node = { symbol = symbol; signature = natId }
          subtrees = [] }


// https://www.cs.utexas.edu/~EWD/ewd07xx/EWD768.PDF
[<RequireQualifiedAccess>]
type PredNat =
  | Equals of Nat * Nat // x = y
  | Differs of Nat * Nat // x ≠ y
  | Exceeds of Nat * Nat // x > y
  | AtLeast of Nat * Nat // x ≥ y
  | LessThan of Nat * Nat // x < y
  | AtMost of Nat * Nat // x ≤ y

  interface ITypedExpr with
    member this.toTypedExpr() =
      let symbol, args =
        match this with
        | Equals(left, right) -> "=", [ left; right ]
        | Differs(left, right) -> "≠", [ left; right ]
        | Exceeds(left, right) -> ">", [ left; right ]
        | AtLeast(left, right) -> "≥", [ left; right ]
        | LessThan(left, right) -> "<", [ left; right ]
        | AtMost(left, right) -> "≤", [ left; right ]

      let op =
        { symbol = Fixed symbol
          signature = Fun [ natId; natId; boolId ] }

      typedTree op (args |> List.map (fun a -> a :> ITypedExpr |> _.toTypedExpr()))

let rec printTypedExpr (p: Tree<TypedSymbol>) =
  match p with
  | { node = { symbol = x }; subtrees = [] } -> $"{x}"
  | _ ->
    p.subtrees
    |> List.map (fun x ->
      match x with
      | { subtrees = [] } -> printTypedExpr x
      | _ when x.subtrees.Length = 1 -> printTypedExpr x
      | _ -> $"({printTypedExpr x})")
    |> function
      | [ x ] -> $"{p.node.symbol}{x}"
      | xs -> xs |> String.concat $" {p.node.symbol} "
