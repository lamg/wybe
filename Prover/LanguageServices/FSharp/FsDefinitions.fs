module FsDefinitions

// this module allows to extract propositions from F# functions
// propositions allow proving theorems about the orginal function

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

// Implementation approach
// - Type check an F# module and for each top-level declaration get a list of variables and their types
// - Visit the syntactic tree and with the list of variables found above construct propositions accordingly

open System
open System.IO
open System.Reflection
open Microsoft.FSharp.Core.CompilerServices
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Text
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open ProviderImplementation.ProvidedTypes
open Core

#nowarn 86

open GriesSchneider

let private checker = FSharpChecker.Create(keepAssemblyContents = true)

let typeNameToSort =
  function
  | Some param, "list"
  | Some param, "array"
  | Some param, "seq" -> WSort.WSeq param
  | None, "bool" -> WBool
  | None, "int" -> WInt
  | x -> failwith $"unexpected type representation {x}"

let rec checkType =
  function
  | (t: FSharpType) when t.IsGenericParameter || t.IsFunctionType || t.IsTupleType -> None
  | t when t.HasTypeDefinition ->
    let def = t.TypeDefinition
    let name = def.DisplayName
    let args = t.GenericArguments

    let param = if args.Count.Equals 1 then checkType args[0] else None

    Some(typeNameToSort (param, name))
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

type FunContext =
  { fnDecls: Core.FnDecl list
    fn: FnApp
    vars: Var list }

let rec visitExpression (fctx: FunContext) (expr: SynExpr) : WExpr list =
  let getMatchedVar expr =
    match visitExpression fctx expr with
    | [ e ] -> e
    | r -> failwith $"expected to get a single expression from {expr}, got instead {r}"

  let procClauses clauses (matchedVar: WExpr) : WExpr list =
    clauses
    |> List.choose (fun (SynMatchClause(pat = pat; whenExpr = whenExpr; resultExpr = resultExpr)) ->
      match pat with
      | SynPat.ListCons _ ->
        let r = len matchedVar != zero

        let pat =
          match whenExpr with
          | Some w ->
            match visitExpression fctx w with
            | [ e ] -> r <&&> e
            | ys -> failwith $"expecing a single expression, got {ys}"
          | None -> r

        match visitExpression fctx resultExpr with
        | [ e ] -> Some(pat ==> (fctx.fn = e))
        | ys -> failwith $"expecting a single expression, got {ys} at {resultExpr}"
      | SynPat.ArrayOrList(_, [], _) -> Some(len matchedVar = zero)
      | xs ->
        printfn $"XS {xs}"
        None)

  match expr with
  | SynExpr.IfThenElse(ifExpr = cond; thenExpr = trueBranch; elseExpr = falseBranchOpt) -> []
  | SynExpr.Tuple(exprs = exprs) -> exprs |> List.collect (visitExpression fctx)
  | SynExpr.App(funcExpr = func; argExpr = rhs) ->
    match func with
    | SynExpr.App(funcExpr = SynExpr.LongIdent(longDotId = op); argExpr = lhs; isInfix = true) ->
      match List.last op.LongIdent with
      | h when h.idText.Equals "op_LessThanOrEqual" ->
        match visitExpression fctx lhs, visitExpression fctx rhs with
        | [ l ], [ r ] -> [ l <= r ]
        | h ->
          printfn $"something else {h}"
          []
      | _ ->
        printfn $"{lhs} {op} {rhs}"
        []
    | SynExpr.App(funcExpr = SynExpr.Ident ident; argExpr = lhs) ->
      let largs = visitExpression fctx lhs
      let args = visitExpression fctx rhs

      let fnCall = fctx.fnDecls |> List.find (fun f -> f.Name.Equals ident.idText)

      [ Core.FnApp(fnCall, largs @ args) ]
    | SynExpr.LongIdent(longDotId = fnId) ->
      match List.last fnId.LongIdent with
      | x when x.idText.Equals "op_ColonColon" ->
        match visitExpression fctx rhs with
        | [ x; y ] -> [ x <. y ]
        | _ -> []

      | _ ->
        printfn $"FN {fnId}"
        []
    | _ ->
      printfn $"FUNC {func}"
      printfn $"FUNC {rhs}"
      []
  | SynExpr.Ident n ->
    fctx.vars
    |> List.tryFind (fun v -> v.Name.Equals n.idText)
    |> Option.map (fun x ->
      printfn $"X {x}"
      x :> WExpr)
    |> Option.toList
  | SynExpr.Match(expr = expr; clauses = clauses) -> procClauses clauses (getMatchedVar expr)
  | SynExpr.MatchLambda(matchClauses = clauses) ->
    let hiddenVar =
      fctx.vars |> List.filter (fun v -> v.Name.StartsWith '_') |> List.head

    procClauses clauses hiddenVar
  | _ ->
    printfn $"LAST {expr}"
    []


let getFunDecls declTriples =
  let single
    (value: FSharpMemberOrFunctionOrValue, paramLists: FSharpMemberOrFunctionOrValue list list, body: FSharpExpr)
    =
    match checkType value.ReturnParameter.Type with
    | Some returnSort ->
      let oks, errs = getTypedVariables (List.concat paramLists)
      let signature = (oks |> List.map _.Sort) @ [ returnSort ]
      let decl = Core.FnDecl(value.DisplayName, signature)
      let fn = Core.FnApp(decl, oks |> List.map (fun x -> x :> WExpr))
      (fn, oks @ getExprVars body), errs
    | None -> failwith $"could not check return type when getting declaration {value}"

  declTriples |> List.map single

let rec toDeclTriples =
  function
  | FSharpImplementationFileDeclaration.MemberOrFunctionOrValue(value, paramLists, body) -> [ value, paramLists, body ]
  | FSharpImplementationFileDeclaration.InitAction _ -> []
  | FSharpImplementationFileDeclaration.Entity(_, decls) -> decls |> List.collect toDeclTriples

// let headPatToFun (vars: Var list) (longId: SynLongIdent, pats: SynPat list) =
//   let funName = List.last longId.LongIdent

//   let parameters =
//     pats
//     |> List.choose (function
//       | SynPat.Paren(
//           pat = SynPat.Typed(
//             pat = SynPat.Named(ident = SynIdent.SynIdent(ident = ident)); targetType = SynType.LongIdent targetType)) ->

//         Some
//           { name = ident.idText
//             sort = typeNameToSort (None, targetType.LongIdent |> List.last |> _.idText) }
//       | SynPat.Named(ident = SynIdent.SynIdent(ident = ident)) ->
//         vars |> List.find (fun v -> ident.idText.Equals v.name) |> Some
//       | _ -> None)

//   let decl = Core.Fn(funName.idText, parameters |> List.map _.sort)
//   Core.App(decl, parameters |> List.map (fun x -> x :> WExpr))

let getModuleOrNssExpressions modulesOrNss =
  modulesOrNss
  |> List.collect (fun moduleOrNs ->
    let SynModuleOrNamespace(decls = decls) = moduleOrNs

    decls
    |> List.collect (function
      | SynModuleDecl.Let(bindings = bindings) ->
        bindings
        |> List.choose (function
          | SynBinding(headPat = SynPat.LongIdent(longDotId = longId; argPats = SynArgPats.Pats _); expr = expr) ->
            Some(longId.LongIdent |> List.last |> _.idText, expr)
          | _ -> None)
      | _ -> []))

let parseAndTypeCheckSingleFile (file, input) =
  let projOptions, errors =
    checker.GetProjectOptionsFromScript(file, input, assumeDotNetFramework = false)
    |> Async.RunSynchronously

  match errors with
  | _ :: _ ->
    let msg = errors |> List.map string |> String.concat ","
    failwith $"error parsing project: {msg}"
  | _ -> ()

  let parseFileResults, checkFileResults =
    checker.ParseAndCheckFileInProject(file, 0, input, projOptions)
    |> Async.RunSynchronously

  // Wait until type checking succeeds (or 100 attempts)
  match checkFileResults with
  | FSharpCheckFileAnswer.Succeeded(res) -> parseFileResults, res
  | res -> failwithf "Parsing did not finish... (%A)" res


let getWybeExpressions (file: string, source: string) =
  let parseRes, checkRes =
    parseAndTypeCheckSingleFile (file, SourceText.ofString source)

  let fsSynExprs =
    match parseRes.ParseTree with
    | ParsedInput.ImplFile f -> getModuleOrNssExpressions f.Contents
    | _ -> failwith $"cannot extract Wybe expressions from parse tree {parseRes.ParseTree}"

  let (>) = FSharp.Core.Operators.(>)
  let (=) = FSharp.Core.Operators.(=)

  match checkRes.ImplementationFile with
  | Some m when m.Declarations.Length > 0 ->
    let decls = m.Declarations |> List.collect toDeclTriples |> getFunDecls
    let oks, errors = decls |> List.unzip

    match List.concat errors with
    | [] ->
      let fnDecls = oks |> List.map (fst >> _.FnDecl)

      oks
      |> List.map (fun (fn, allVars) ->
        let ctx =
          { fnDecls = fnDecls
            fn = fn
            vars = allVars }

        let synBody =
          fsSynExprs
          |> List.choose (function
            | (name, body) when name = fn.FnDecl.Name -> Some body
            | _ -> None)
          |> List.head

        visitExpression ctx synBody)
      |> Ok
    | _ -> Error $"errors getting variables from functions: {errors}"
  | _ -> Error $"no declarations in file {file}"
