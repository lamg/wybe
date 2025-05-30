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

open System
open System.IO
open System.Reflection
open Microsoft.FSharp.Core.CompilerServices
open ProviderImplementation.ProvidedTypes
//open FSharp.Compiler.SourceCodeServices
//open FSharp.Compiler.Text
open GriesSchneider.Integers
open GriesSchneider.Sequences

/// Retrieves the specified branch proposition for a function (currently only "insert").
let internal getBranch (projectFile: string) (_moduleName: string) (functionName: string) (branchIdx: int) =
  if functionName = "insert" then
    let n = Core.mkIntVar "n"
    let xs = mkSeq "xs"
    let insertFn = Core.Fn("insert", [ Core.WInt; Core.WSeq sortA ])
    let call = Core.App(insertFn, [ n; xs ])
    let (==>) = Core.(==>)
    let (<&&>) = Core.(<&&>)
    let ``∀`` = Core.``∀``

    match branchIdx with
    | 0 ->
      // branch0: ⟨∀ n,xs → Length xs = 0 ⇒ insert n = [n]⟩
      let cond = Core.Equals(Core.Length xs, zero)
      let body = Core.Equals(call, Core.Cons(n, Core.Empty Core.WInt))
      ``∀`` [ n; xs ] (cond ==> body)
    | 1 ->
      // branch1: ⟨∀ n,xs → Length xs > 0 ∧ n ≤ Head xs ⇒ insert(n,xs) = n :: xs⟩
      let headX = Core.ExtInteger(Core.Head xs)
      let cond = len xs > zero <&&> (n <= headX)
      let body = Core.Equals(call, Core.Cons(n, xs))
      ``∀`` [ n; xs ] (cond ==> body)
    | 2 ->
      // branch2: ⟨∀ n,xs → Length xs > 0 ∧ n > Head xs ⇒ Head xs :: insert n (Tail xs)⟩
      let headX = Core.ExtInteger(Core.Head xs)
      let tailX = Core.Tail xs

      let body =
        Core.Equals(call, Core.Cons(headX, Core.ExtSeq(Core.App(insertFn, [ n; tailX ]))))

      let cond = len xs > zero <&&> (n > headX)
      ``∀`` [ n; xs ] (cond ==> body)
    | _ -> failwithf "branch %d not defined for function %s" branchIdx functionName
  else
    failwithf "function %s not supported" functionName

/// Runtime helper for module access.
let internal getModule (_projectFile: string) (_moduleName: string) : obj = new obj ()

/// Runtime helper for function access.
let internal getFunction (_projectFile: string) (_moduleName: string) (functionName: string) : obj = new obj ()

let ns = "FsDefinitions"
let asm = Assembly.GetExecutingAssembly()
let providedType = ProvidedTypeDefinition(asm, ns, "FromProject", Some typeof<obj>)

[<TypeProvider>]
type FromProjectTypeProvider(config: TypeProviderConfig) as this =
  inherit TypeProviderForNamespaces(config, ns, [ providedType ], sourceAssemblies = [ asm ])

  do
    providedType.DefineStaticParameters(
      [ ProvidedStaticParameter("projectFile", typeof<string>) ],
      (fun typeName args ->
        let projectFile = args.[0] :?> string
        let projectType = ProvidedTypeDefinition(asm, ns, typeName, Some typeof<obj>)

        let moduleName = "module0"
        let moduleType = ProvidedTypeDefinition(moduleName, Some typeof<obj>)

        let insertName = "insert"
        let insertType = ProvidedTypeDefinition(insertName, Some typeof<obj>)

        for idx in 0..2 do
          let branchName = sprintf "branch%d" idx

          let prop =
            ProvidedProperty(
              branchName,
              typeof<Core.Proposition>,
              getterCode = fun _ -> <@@ getBranch projectFile moduleName insertName idx @@>
            )

          insertType.AddMember(prop)

        let insertProp =
          ProvidedProperty(
            insertName,
            insertType,
            getterCode = fun _ -> <@@ getFunction projectFile moduleName insertName @@>
          )

        moduleType.AddMember(insertProp)

        let moduleProp =
          ProvidedProperty(moduleName, moduleType, getterCode = (fun _ -> <@@ getModule projectFile moduleName @@>))

        projectType.AddMember(moduleProp)

        projectType)
    )

  do this.AddNamespace(ns, [ providedType ])

[<TypeProviderAssembly>]
do ()
