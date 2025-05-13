module Extractor.Emitter

open System.IO
open Extractor.Types
open Fabulous.AST
open Core
open FParsec

#nowarn 86
let (=) = Operators.(=)

let parseVar sort : Parser<WExpr, unit> =
  parse {
    let! v =
      many1Satisfy2L isLetter (fun c -> isLetter c || isDigit c || c = '_') "variable"
      <|> pstring "$e"

    do! spaces
    return Var(v, sort)
  }

let parseInteger: Parser<Integer, unit> =
  let literal =
    parse {
      let! x = many1SatisfyL isDigit "integer"
      return Integer(int x)
    }

  let intVar =
    parse {
      let! v = parseVar WInteger
      return ExtInteger v
    }

  let term = literal <|> intVar

  parse {
    let! x = term

    let! op =
      choice
        [ pstring "+" >>% Plus
          pstring "-" >>% Minus
          pstring "×" >>% Times
          pstring "÷" >>% Divide
          pstring ">" >>% Exceeds
          pstring "<" >>% LessThan
          pstring "≥" >>% AtLeast
          pstring "≤" >>% AtMost ]

    do! spaces
    let! y = term
    return op (x, y)
  }

let parseProposition: Parser<Proposition, unit> =
  let boolVar =
    parse {
      let! v = parseVar WBool
      return ExtBoolOp v
    }

  let literal = choice [ pstring "true" >>% True; pstring "false" >>% False ]

  let integerProp =
    parse {
      let! p = parseInteger

      let! r =
        match p with
        | AtMost _
        | AtLeast _
        | LessThan _
        | IsDivisor _
        | Exceeds _ -> preturn (ExtBoolOp p)
        | _ -> fail $"expecting a boolean instead of {p}"

      return r
    }

  let factor = integerProp <|> literal <|> boolVar

  let term =
    parse {
      let! x = factor

      let! op =
        choice
          [ pstring "∧" >>% And
            pstring "∨" >>% Or
            pstring "≡" >>% Equiv
            pstring "≢" >>% Inequiv
            pstring "⇒" >>% Implies
            pstring "⇐" >>% Follows ]

      let! y = factor

      return op (x, y)
    }

  factor <|> term



let extractProofObligations (funcs: Function list) =
  let parseWybeExpr (s: string) : Proposition =
    match run parseProposition s with
    | Success(result, _, _) -> result
    | Failure(errorMsg, _, _) -> failwith $"Parsing failed: {errorMsg}"

  let extractObligation (f: Function) =
    let rec substituteE (e: WExpr) (p: WExpr) : WExpr =
      // what if p has no $e, and instead mentions a variable defined explicitly by e
      match p with
      | _ when (p :? Proposition) ->
        let p = p :?> Proposition

        match p with
        | ExtBoolOp x ->
          match x with
          | _ when (x :? Var) ->
            match x :?> Var with
            | Var("$e", _) -> ExtBoolOp e
            | _ -> ExtBoolOp x
          | _ when (x :? Integer) -> ExtBoolOp(substituteE e x)
          | _ -> failwith "not implemented"
        | And(l, r) -> And(substituteE e l :?> Proposition, substituteE e r :?> Proposition)
        | Equals(_, _) -> failwith "Not Implemented equals"
        | Differs(_, _) -> failwith "Not Implemented differs"
        | Not(right) -> failwith "Not Implemented not "
        | Or(left, right) -> failwith "Not Implemented"
        | Equiv(left, right) -> failwith "Not Implemented"
        | Inequiv(left, right) -> failwith "Not Implemented"
        | Implies(left, right) -> failwith "Not Implemented"
        | Follows(left, right) -> failwith "Not Implemented"
        | Forall(_) -> failwith "Not Implemented"
        | Exists(_) -> failwith "Not Implemented"
        | _ -> p
      | _ when (p :? Integer) ->
        match p :?> Integer with
        | Integer.Integer _ -> p
        | Integer.ExtInteger n ->
          match n with
          | _ when (n :? Var) ->
            match n :?> Var with
            | Var("$e", _) -> e
            | _ -> Integer.ExtInteger n
          | _ -> failwith "not implemented"
        | Integer.Plus(_, _) -> failwith "Not Implemented plus"
        | Integer.Minus(_, _) -> failwith "Not Implemented minus"
        | Integer.Times(_, _) -> failwith "Not Implemented times"
        | Integer.Divide(_, _) -> failwith "Not Implemented divide"
        | Integer.Exceeds(l, r) -> Integer.Exceeds(substituteE e l :?> Integer, substituteE e r :?> Integer)
        | Integer.LessThan(_, _) -> failwith "Not Implemented"
        | Integer.AtLeast(_, _) -> failwith "Not Implemented"
        | Integer.AtMost(_, _) -> failwith "Not Implemented"
        | Integer.IsDivisor(_, _) -> failwith "Not Implemented"

      | _ when (p :? Sequence) -> failwith "not implemented"
      | _ when (p :? Var) -> failwith "not implemented"
      | _ -> failwith $"not implemented {p}"

    let rec wybeFromRustExpr (x: TargetLangExpr) : WExpr =
      match x with
      | TargetLangExpr.Var v ->
        f.Parameters
        |> List.filter (fun (t, _) -> t = v)
        |> function
          | [ t, "i32" ] -> ExtInteger(Var(t, WInteger))
          | [ t, "i64" ] -> ExtInteger(Var(t, WInteger))
          | [ t, "bool" ] -> ExtBoolOp(Var(t, WBool))
          | _ -> failwith "not implmented"
      | TargetLangExpr.Integer n -> Integer n
      | TargetLangExpr.Op("+", x, y) -> Plus(wybeFromRustExpr x :?> Integer, wybeFromRustExpr y :?> Integer)
      | TargetLangExpr.Op("-", x, y) -> Minus(wybeFromRustExpr x :?> Integer, wybeFromRustExpr y :?> Integer)
      | TargetLangExpr.Op("*", x, y) -> Times(wybeFromRustExpr x :?> Integer, wybeFromRustExpr y :?> Integer)
      | TargetLangExpr.Op("/", x, y) -> Divide(wybeFromRustExpr x :?> Integer, wybeFromRustExpr y :?> Integer)
      | TargetLangExpr.Op("&&", x, y) -> And(wybeFromRustExpr x :?> Proposition, wybeFromRustExpr y :?> Proposition)
      | TargetLangExpr.Op("||", x, y) -> Or(wybeFromRustExpr x :?> Proposition, wybeFromRustExpr y :?> Proposition)
      | TargetLangExpr.Op("==", x, y) -> Equiv(wybeFromRustExpr x :?> Proposition, wybeFromRustExpr y :?> Proposition)
      | TargetLangExpr.Op("!=", x, y) -> Inequiv(wybeFromRustExpr x :?> Proposition, wybeFromRustExpr y :?> Proposition)
      | TargetLangExpr.Op("->", x, y) -> Implies(wybeFromRustExpr x :?> Proposition, wybeFromRustExpr y :?> Proposition)
      | TargetLangExpr.Op("<-", x, y) -> Follows(wybeFromRustExpr x :?> Proposition, wybeFromRustExpr y :?> Proposition)
      | TargetLangExpr.Op("!", x, _) -> Not(wybeFromRustExpr x :?> Proposition)
      | _ -> failwith "not implemented"
    ///// Adds one to the given integer.
    // fn add_one(x: i32) -> i32 {
    //     x + 1
    //     // { $e > x }
    // }
    // the $e variable is a special variable to capture the expression previous to the assertion
    f.Body
    |> List.pairwise
    |> List.choose (fun (x, y) ->
      match y with
      | CommentAssertion c ->
        let x = wybeFromRustExpr x
        let a = parseWybeExpr c
        let s = substituteE x a
        s :?> Proposition |> Some
      | _ -> None)


  funcs |> List.collect extractObligation



open type Fabulous.AST.Ast

let emitProofObligation (writer: TextWriter) (theoremBody: Proposition) =
  let wExprToString (expr: WExpr) =
    let rec propToStr (expr: Proposition) =
      match expr with
      | And(x, y) -> $"{propToStr x} <&&> {propToStr y}"
      | Or(x, y) -> $"{propToStr x} <||> {propToStr y}"
      | Equiv(x, y) -> $"{propToStr x} === {propToStr y}"
      | Inequiv(x, y) -> $"{propToStr x} !== {propToStr y}"
      | Implies(x, y) -> $"{propToStr x} ==> {propToStr y}"
      | Follows(x, y) -> $"{propToStr x} <== {propToStr y}"
      | Not x -> $"!{propToStr x}"
      | Forall(vars, body) -> $"∀ {vars} ({propToStr body})"
      | Exists(vars, body) -> $"∃ {vars} ({propToStr body})"
      | ExtBoolOp op -> $"{op}"
      | True -> "True"
      | False -> "False"
      | Equals(x, y) -> $"{x} = {y}"
      | Differs(x, y) -> $"{x} != {y}"

    match expr with
    | _ when (expr :? Proposition) ->
      let expr = expr :?> Proposition
      propToStr expr

    | _ -> ""

  Oak() {
    AnonymousModule() {
      HashDirective("r", String "nuget: Wybe, 0.0.1")


      NamedComputationExpr(
        ConstantExpr(Constant "proof"),
        CompExprBodyExpr [ AppExpr("lemma", [ String(wExprToString theoremBody) ]) ]
      )
    }
  }
  |> Gen.mkOak
  |> Gen.run
  |> writer.Write

let parseFileAndEmitProofObligations (rustSource: string) (fsScript: string) =
  // parse all functions in the source file
  let rustSourceContent = File.ReadAllText rustSource
  let rustFunctions = RustParser.parseFunctions rustSourceContent
  let proofObligations = extractProofObligations rustFunctions

  use writer = new StreamWriter(fsScript)
  proofObligations |> List.iter (emitProofObligation writer)
