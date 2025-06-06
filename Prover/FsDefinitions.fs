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

let getTypedVariables (paramLists: FSharpMemberOrFunctionOrValue list list) =
  // filter functions whose signatures have as basic types: boolean, integer, string, unit,
  // and sequences (list or seq) of the previous types
  let hasWybeSupport (name, t: FSharpType) =
    t |> checkType |> Option.map (fun t -> name, t)

  let args =
    paramLists |> List.collect (List.map (fun p -> p.DisplayName, p.FullType))

  args
  |> List.map hasWybeSupport
  |> List.fold
    (fun acc x ->
      match x with
      | Some v -> v :: acc
      | None -> [])
    []
  |> function
    | [] -> None
    | xs -> xs |> List.map Var |> Some

let getPropositions (parentFnApp: WExpr) (expr: FSharpExpr) =
  let rec visitExpr (parentFnApp: WExpr) (e: FSharpExpr) =

    match e with
    | FSharpExprPatterns.AddressOf(lvalueExpr) -> visitExpr parentFnApp lvalueExpr
    | FSharpExprPatterns.AddressSet(lvalueExpr, rvalueExpr) ->
      visitExpr parentFnApp lvalueExpr @ visitExpr parentFnApp rvalueExpr
    | FSharpExprPatterns.Application(funcExpr, _typeArgs, argExprs) ->
      visitExpr parentFnApp funcExpr @ visitExprs parentFnApp argExprs
    | FSharpExprPatterns.Call(objExprOpt, _memberOrFunc, _typeArgs1, _typeArgs2, argExprs) ->
      visitObjArg parentFnApp objExprOpt @ visitExprs parentFnApp argExprs
    | FSharpExprPatterns.Coerce(_targetType, inpExpr) -> visitExpr parentFnApp inpExpr
    | FSharpExprPatterns.FastIntegerForLoop(startExpr, limitExpr, consumeExpr, _isUp, _, _) ->
      visitExpr parentFnApp startExpr
      @ visitExpr parentFnApp limitExpr
      @ visitExpr parentFnApp consumeExpr
    | FSharpExprPatterns.ILAsm(_asmCode, _typeArgs, argExprs) -> visitExprs parentFnApp argExprs
    | FSharpExprPatterns.ILFieldGet(objExprOpt, _fieldType, _fieldName) -> visitObjArg parentFnApp objExprOpt
    | FSharpExprPatterns.ILFieldSet(objExprOpt, _fieldType, _fieldName, _valueExpr) ->
      visitObjArg parentFnApp objExprOpt
    | FSharpExprPatterns.IfThenElse(guardExpr, thenExpr, elseExpr) ->
      // make proposition (guardExpr ⇒ parentExpr = thenExpr) ∨ (¬guardExpr ⇒ parentExpr = elseExpr)
      let guard = visitExpr parentFnApp guardExpr |> List.head
      let ok = visitExpr parentFnApp thenExpr |> List.head
      let notOk = visitExpr parentFnApp elseExpr |> List.head
      printfn $"GUARD {guard} {guardExpr}" 
      printfn $"OK {ok} {thenExpr}"
      printfn $"NOTOK {notOk} {elseExpr}"
      let r =
        guard ==> Core.Equals(parentFnApp, ok)
        <||> (!guard ==> Core.Equals(parentFnApp, notOk))

      [ r :> WExpr ]
    | FSharpExprPatterns.Lambda(_lambdaVar, bodyExpr) -> visitExpr parentFnApp bodyExpr
    | FSharpExprPatterns.Let((_bindingVar, bindingExpr, _dbg), bodyExpr) ->
      match checkType _bindingVar.FullType with
      | Some t ->
        let parentFnApp = Var(_bindingVar.DisplayName, t)
        visitExpr parentFnApp bindingExpr @ visitExpr parentFnApp bodyExpr
      | None -> []
    | FSharpExprPatterns.LetRec(recursiveBindings, bodyExpr) ->
      let xs =
        recursiveBindings
        |> List.collect (fun (bindingVar, bindingExpr, _) ->
          match checkType bindingVar.FullType with
          | Some t ->
            let parentFnApp = Var(bindingVar.DisplayName, t)
            visitExpr parentFnApp bindingExpr @ visitExpr parentFnApp bodyExpr
          | None -> [])

      xs @ visitExpr parentFnApp bodyExpr
    | FSharpExprPatterns.NewArray(_arrayType, argExprs) -> visitExprs parentFnApp argExprs
    | FSharpExprPatterns.NewDelegate(_delegateType, delegateBodyExpr) -> visitExpr parentFnApp delegateBodyExpr
    | FSharpExprPatterns.NewObject(_objType, _typeArgs, argExprs) -> visitExprs parentFnApp argExprs
    | FSharpExprPatterns.NewRecord(_recordType, argExprs) -> visitExprs parentFnApp argExprs
    | FSharpExprPatterns.NewAnonRecord(_recordType, argExprs) -> visitExprs parentFnApp argExprs
    | FSharpExprPatterns.NewTuple(_tupleType, argExprs) -> visitExprs parentFnApp argExprs
    | FSharpExprPatterns.NewUnionCase(_unionType, _unionCase, argExprs) -> visitExprs parentFnApp argExprs
    | FSharpExprPatterns.Quote(quotedExpr) -> visitExpr parentFnApp quotedExpr
    | FSharpExprPatterns.FSharpFieldGet(objExprOpt, _recordOrClassType, _fieldInfo) ->
      visitObjArg parentFnApp objExprOpt
    | FSharpExprPatterns.AnonRecordGet(objExpr, _recordOrClassType, _fieldInfo) -> visitExpr parentFnApp objExpr
    | FSharpExprPatterns.FSharpFieldSet(objExprOpt, _recordOrClassType, _fieldInfo, argExpr) ->
      visitObjArg parentFnApp objExprOpt @ visitExpr parentFnApp argExpr
    | FSharpExprPatterns.Sequential(firstExpr, secondExpr) ->
      visitExpr parentFnApp firstExpr @ visitExpr parentFnApp secondExpr
    | FSharpExprPatterns.TryFinally(bodyExpr, finalizeExpr, _dbgTry, _dbgFinally) ->
      visitExpr parentFnApp bodyExpr @ visitExpr parentFnApp finalizeExpr
    | FSharpExprPatterns.TryWith(bodyExpr, _, _, _catchVar, catchExpr, _dbgTry, _dbgWith) ->
      visitExpr parentFnApp bodyExpr @ visitExpr parentFnApp catchExpr
    | FSharpExprPatterns.TupleGet(_tupleType, _tupleElemIndex, tupleExpr) -> visitExpr parentFnApp tupleExpr
    | FSharpExprPatterns.DecisionTree(decisionExpr, decisionTargets) ->
      visitExpr parentFnApp decisionExpr
      @ List.collect (snd >> visitExpr parentFnApp) decisionTargets
    | FSharpExprPatterns.DecisionTreeSuccess(_decisionTargetIdx, decisionTargetExprs) ->
      decisionTargetExprs
      |> List.choose (function
        | FSharpExprPatterns.UnionCaseGet(expr, _, _, field) ->
          let ctr =
            if field.Name.Equals "Head" then Sequence.Head
            else if field.Name.Equals "Tail" then Sequence.Tail
            else failwith $"unexpected field {field}"

          match visitExpr parentFnApp expr with
          | [ v ] ->
            match v with
            | :? Var as v -> Some(ctr (ExtSeq v))
            | _ -> None
          | _ -> None
        | _ -> None)

    // visitExprs parentFnApp decisionTargetExprs
    | FSharpExprPatterns.TypeLambda(_genericParam, bodyExpr) -> visitExpr parentFnApp bodyExpr
    | FSharpExprPatterns.TypeTest(ty, inpExpr) -> visitExpr parentFnApp inpExpr
    | FSharpExprPatterns.UnionCaseSet(unionExpr, _unionType, _unionCase, _unionCaseField, valueExpr) ->
      visitExpr parentFnApp unionExpr @ visitExpr parentFnApp valueExpr
    | FSharpExprPatterns.UnionCaseGet(unionExpr, _unionType, _unionCase, _unionCaseField) ->
      visitExpr parentFnApp unionExpr
    | FSharpExprPatterns.UnionCaseTest(unionExpr, _unionType, _unionCase) -> visitExpr parentFnApp unionExpr
    | FSharpExprPatterns.UnionCaseTag(unionExpr, _unionType) -> visitExpr parentFnApp unionExpr
    | FSharpExprPatterns.ObjectExpr(_objType, baseCallExpr, overrides, interfaceImplementations) ->
      visitExpr parentFnApp baseCallExpr
      @ List.collect (visitObjMember parentFnApp) overrides
      @ List.collect (snd >> List.collect (visitObjMember parentFnApp)) interfaceImplementations
    | FSharpExprPatterns.TraitCall(_sourceTypes, _traitName, _typeArgs, _typeInstantiation, _argTypes, argExprs) ->
      visitExprs parentFnApp argExprs
    | FSharpExprPatterns.ValueSet(_valToSet, valueExpr) -> visitExpr parentFnApp valueExpr
    | FSharpExprPatterns.WhileLoop(guardExpr, bodyExpr, _dbg) ->
      visitExpr parentFnApp guardExpr @ visitExpr parentFnApp bodyExpr
    | FSharpExprPatterns.BaseValue _baseType -> []
    | FSharpExprPatterns.DefaultValue _defaultType -> []
    | FSharpExprPatterns.ThisValue _thisType -> []
    | FSharpExprPatterns.Const(_constValueObj, _constType) -> []
    | FSharpExprPatterns.Value v ->

      match checkType v.FullType with
      | Some t ->
        match t with
        | WBool when v.DisplayName.Equals "true" -> Some(True :> WExpr)
        | WBool when v.DisplayName.Equals "false" -> Some(False :> WExpr)
        | WInt when v.DisplayName[0] |> Char.IsLetter -> Some(Var(v.DisplayName, WInt))
        | WInt -> Some(Integer(int v.DisplayName))
        | WSeq WInt when v.DisplayName.Equals "[]" ->
          Some(Proposition.Equals(ExtBoolOp(Var(v.DisplayName, WSeq WInt)), Sequence.Empty WInt))
        | WSeq x -> 
          printfn $"literal value {v.LiteralValue}"
          Some(Var(v.DisplayName, WSeq x))
        | _ -> None
        |> Option.toList
      | None -> []
    | _ -> []


  and visitExprs parentFnApp exprs =
    List.collect (visitExpr parentFnApp) exprs

  and visitObjArg parentFnApp objOpt =
    Option.map (visitExpr parentFnApp) objOpt |> Option.toList |> List.concat

  and visitObjMember parentFnApp memb = visitExpr parentFnApp memb.Body
  visitExpr parentFnApp expr

let rec getDeclaration =
  function
  | FSharpImplementationFileDeclaration.MemberOrFunctionOrValue(value, paramLists, body) ->
    match checkType value.ReturnParameter.Type with
    | Some t ->

      match getTypedVariables paramLists with
      | Some vars ->
        let signature = List.map (fun (Var(_, t)) -> t) vars @ [ t ]
        let args = vars |> List.map (fun v -> v :> WExpr)
        let parentExpr = App(Fn(value.DisplayName, signature), args)
        getPropositions parentExpr body
      | None -> []
    | None -> []
  | FSharpImplementationFileDeclaration.InitAction _ -> []
  | FSharpImplementationFileDeclaration.Entity(_, decls) -> decls |> List.collect getDeclaration
