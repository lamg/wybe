module FsDefinitions

// this module implements a type provider that extracts propositions from F# functions
// this propositions allow proving theorems about the orginal function
// currently only the rules for extracting propositions from a function like `insert`, defined in the example below, are defined
// the rest of the rules are still to be defined and their implementation is a stub

// example

// let rec insert (n: int) =
//  function
//  | [] -> [ n ]
//  | x :: xs when n <= x -> n :: x :: xs
//  | x :: xs -> x :: insert n xs

// from the insert function above the following definitions are extracted
// branch0: ⟨∀ n,xs → Length xs = 0 ⇒ insert n = [n]⟩
// branch1: ⟨∀ n,xs → Length xs > 0  ∧  n ≤ Head xs  ⇒  insert(n,xs) = n :: xs⟩
// branch2: ⟨∀ n,xs → Length xs > 0  ∧  n > Head xs  ⇒  Head xs :: insert n (Tail xs)⟩

// with the extracted definitions we can check the following proof
// proof
//  lemma (insert 5 [1; 4; 6] = [1; 4; 5; 6])
//  insert 5 [1; 4; 6]
// = { branch2 }
//  1 :: insert 5 [4;6]
// = { branch2 }
//  1 :: 4 :: insert 5 [6]
// = { branch1 }
//  1 :: 4 :: 5 :: 6 :: []
// ▢

// the type provider is used the following way

// open FsDefinitions
// type Project = FromProject< "/path/to/project.fsproj" >

// let p = Project()
// let insert = p.module0.insert
// let branch0 = insert.branch0
// let branch1 = insert.branch1
// let branch2 = insert.branch2

// Implementation of a simple type provider for extracting propositions from F# functions

// Plan:
// get the function signatures given a module
// filter functions that for which Wybe can prove properties, by their signature
// implement proposition extraction for supported functions

open System
open System.IO
open System.Reflection
open Microsoft.FSharp.Core.CompilerServices
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Text
open FSharp.Compiler.Symbols
open ProviderImplementation.ProvidedTypes
open Core

#nowarn 86
let (=) = FSharp.Core.Operators.(=)

open GriesSchneider

let private checker = FSharpChecker.Create()

let parseAndTypeCheckSingleFile (file, input) =
  async {
    let! projOptions, errors = checker.GetProjectOptionsFromScript(file, input, assumeDotNetFramework = false)

    match errors with
    | [] ->
      let! parseFileResults, checkFileResults = checker.ParseAndCheckFileInProject(file, 0, input, projOptions)

      return
        match checkFileResults with
        | FSharpCheckFileAnswer.Succeeded res -> Ok(parseFileResults, res)
        | FSharpCheckFileAnswer.Aborted -> Error [ $"failed type checking of {file}" ]
    | _ -> return errors |> List.map string |> Error
  }

let rec checkType =
  function
  | (t: FSharpType) when t.IsGenericParameter || t.IsFunctionType || t.IsTupleType -> None
  | t when t.HasTypeDefinition ->
    let def = t.TypeDefinition
    let name = def.DisplayName
    let args = t.GenericArguments

    match name with
    | "list"
    | "array"
    | "seq" when args.Count.Equals 1 ->
      match checkType args[0] with
      | Some s -> Some(WSort.WSeq s)
      | None -> None
    | "bool" -> Some WBool
    | "int" -> Some WInt
    | _ -> None
  | _ -> None

let getTypedVariables (variables: FSharpMemberOrFunctionOrValue list) =
  // distinguishes variables with types: boolean, integer
  // and sequences (list or seq) of the previous types

  let oks, errs =
    variables
    |> List.fold
      (fun (oks, errs) p ->
        match checkType p.FullType with
        | Some t -> Var(p.DisplayName, t) :: oks, errs
        | None -> oks, p.DisplayName :: errs)
      ([], [])

  List.rev oks, errs


let rec getExprVars =
  function
  | FSharpExprPatterns.Lambda(_lambdaVar, bodyExpr) -> getExprVars bodyExpr
  | FSharpExprPatterns.Let((var, bindingExpr, _dbg), bodyExpr) ->
    match checkType var.FullType with
    | Some t -> Var(var.DisplayName, t) :: getExprVars bindingExpr @ getExprVars bodyExpr
    | None -> []
  | FSharpExprPatterns.LetRec(recursiveBindings, bodyExpr) ->
    let xs =
      recursiveBindings
      |> List.collect (fun (bindingVar, bindingExpr, _) ->
        match checkType bindingVar.FullType with
        | Some t -> Var(bindingVar.DisplayName, t) :: getExprVars bindingExpr
        | None -> [])

    xs @ getExprVars bodyExpr
  | FSharpExprPatterns.DecisionTree(decisionExpr, decisionTargets) ->
    getExprVars decisionExpr @ List.collect (snd >> getExprVars) decisionTargets
  | FSharpExprPatterns.DecisionTreeSuccess(_decisionTargetIdx, decisionTargetExprs) ->
    decisionTargetExprs |> List.collect getExprVars
  | FSharpExprPatterns.Value v ->
    match checkType v.FullType with
    | Some t ->
      match t with
      | WBool when v.DisplayName.Equals "true" -> []
      | WBool when v.DisplayName.Equals "false" -> []
      | _ when v.DisplayName[0] |> Char.IsLetter -> [ Var(v.DisplayName, t) ]
      | _ -> []
    | None -> []
  | FSharpExprPatterns.IfThenElse(cond, thenExpr, elseExpr) -> [ cond; thenExpr; elseExpr ] |> List.collect getExprVars
  | _ -> []


open FSharp.Compiler.Syntax

let rec visitExpression =
  function
  | SynExpr.IfThenElse(ifExpr = cond; thenExpr = trueBranch; elseExpr = falseBranchOpt) -> []
  | _ -> []


let getDeclVars decls =
  let single
    (value: FSharpMemberOrFunctionOrValue, paramLists: FSharpMemberOrFunctionOrValue list list, body: FSharpExpr)
    =
    match checkType value.ReturnParameter.Type with
    | Some _ ->
      let oks, errs = getTypedVariables (List.concat paramLists)
      oks @ getExprVars body, errs
    | None -> [], []

  decls
  |> List.fold
    (fun (oks, errs) d ->
      let noks, nerrs = single d
      oks @ noks, errs @ nerrs)
    ([], [])

let rec toDeclTriples =
  function
  | FSharpImplementationFileDeclaration.MemberOrFunctionOrValue(value, paramLists, body) -> [ value, paramLists, body ]
  | FSharpImplementationFileDeclaration.InitAction _ -> []
  | FSharpImplementationFileDeclaration.Entity(_, decls) -> decls |> List.collect toDeclTriples
