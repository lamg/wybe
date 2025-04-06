module CalculationCE

open FSharpPlus
open FsToolkit.ErrorHandling
open Inference
open TypedExpression

type ProofLine<'a when 'a: equality and 'a :> ITypedExpr> =
  | Hint of LawHint
  | Pred of Pred<'a>
  | Theorem of string * Pred<'a>
  | WithLaws of Law list
  | Name of string

type Expected =
  | ExpectingStep
  | ExpectingHint
  | ExpectingTheorem

type ProofBuildError<'a when 'a: equality and 'a :> ITypedExpr> =
  { expected: Expected
    line: ProofLine<'a> option }

let buildBasic (lines: ProofLine<'a> list) =
  let rec fixedPoint (f: 'b -> 'b option) (state: 'b) =
    match f state with
    | Some x -> fixedPoint f x
    | None -> state

  // syntax of lines: theorem with_laws? (expr hint)* expr
  result {
    let! (name, theorem), withLaws, lines =
      match lines with
      | [] ->
        Error
          { expected = ExpectingTheorem
            line = None }
      | Theorem(name, t) :: WithLaws ls :: lines -> Ok((name, t), ls, lines)
      | Theorem(name, t) :: lines -> Ok((name, t), [], lines)
      | l :: _ ->
        Error
          { expected = ExpectingTheorem
            line = Some l }

    let steps, lines =
      fixedPoint
        (function
        | steps, lines ->
          match lines with
          | Pred s :: Hint hint :: lines ->
            Some(
              { expr = getTypedExpr s
                hint = Hint.Law hint }
              :: steps,
              lines
            )
          | [ Pred s ] ->
            Some(
              { expr = getTypedExpr s
                hint = Hint.End }
              :: steps,
              []
            )
          | _ -> None)
        ([], lines)

    do!
      match lines with
      | [] -> Ok()
      | Pred s :: _ ->
        Error
          { expected = ExpectingHint
            line = Some(Pred s) }
      | l :: _ ->
        Error
          { expected = ExpectingStep
            line = Some l }
    // x ≡ y  ⇒  f.x ≡ f.y
    let eqLeibniz =
      let x, y, fx, fy = Var "x", Var "y", Var "fx", Var "fy"
      (x === y) ==> (fx === fy) |> law "leibniz"


    // (x ≡ y) ∧ (y ≡ z)  ⇒  (x ≡ z)
    let eqTrans =
      let x, y, z = Var "x", Var "y", Var "z"
      ((x === y) <&&> (y === z)) ==> (x === z) |> law "≡-transitivity"

    return
      { demonstrandum = theorem |> law name
        leibniz = [ eqLeibniz ]
        transitivity = [ eqTrans ]
        applyToResult = withLaws
        steps = steps |> List.rev |> List.toArray }
  }

let buildAndCheck p = p |> buildBasic |> Result.get |> check


type CalculationCE<'a, 'runRes when 'a: equality and 'a :> ITypedExpr>(runner: ProofLine<'a> list -> 'runRes) =
  member _.Bind(l: ProofLine<'a>, f: ProofLine<'a> -> ProofLine<'a> list) = f l

  member _.Zero() = []

  member _.Yield(s: ProofLine<'a>) = [ s ]
  member _.Yield(s: Pred<'a>) = [ Pred s ]

  member _.Return(x: ProofLine<'a>) = [ x ]

  member _.ReturnFrom(l: ProofLine<'a> list) = l

  member _.Combine(l1: ProofLine<'a> list, l2: ProofLine<'a> list) = l1 @ l2

  member _.Delay(f: unit -> ProofLine<'a> list) = f ()

  member _.Run(xs: ProofLine<'a> list) = runner xs

let checkRunner (xs: ProofLine<'a> list) =
  match buildBasic xs with
  | Ok calc ->
    match check calc with
    | Ok r when r.check.isOk -> r.calculation.demonstrandum
    | Ok r ->
      r.calculation
      |> Inspect.Inspect.inspect
      |> Inspect.Inspect.summary
      |> _.accumulated
      |> String.concat "\n"
      |> failwith
    | Error e -> failwith (e.ToString())
  | Error e -> failwith (e.ToString())

let proof () = CalculationCE checkRunner

let inspectRunner (xs: ProofLine<'a> list) =
  match buildBasic xs with
  | Ok calc ->
    match check calc with
    | Ok r -> Inspect.Inspect.inspect r.calculation
    | Error e -> failwith (e.ToString())
  | Error e -> failwith (e.ToString())

let inspectCalc () = CalculationCE inspectRunner

let singleAltHint op (laws: Law list) =
  let generator _ _ = seq { Seq.ofList laws }
  let id = laws |> Seq.map _.id |> String.concat ", "

  Hint
    { op = op
      lawGenerator =
        { id = id
          generator = generator
          limits =
            { maxAlternatives = 1
              maxAlternativeLength = 7 } } }

type LawsCE(op) =
  member _.Yield(x: Law) = [ x ]
  member _.Combine(xs: Law list, ys: Law list) = xs @ ys
  member _.Run(xs: Law list) = singleAltHint op xs
  member _.Zero() = []
  member _.Return(x: Law) = [ x ]
  member _.Delay(f: unit -> Law list) = f ()

let ``≡`` = LawsCE equivSymbol
let ``⇒`` = LawsCE impliesSymbol
let ``⇐`` = LawsCE followsSymbol
