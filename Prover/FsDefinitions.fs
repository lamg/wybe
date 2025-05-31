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
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Text
open FSharp.Compiler.Symbols
open ProviderImplementation.ProvidedTypes
open Core

open GriesSchneider

let private checker = FSharpChecker.Create()

// https://fsharp.github.io/fsharp-compiler-docs/fcs/project.html
