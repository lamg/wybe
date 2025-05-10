module Structor.ProofEmitter

open System.IO
open Structor.Types
open Fabulous.AST
open type Fabulous.AST.Ast

/// Converts a simple Expr AST to a Wybe expression string.
/// Recursively translate Expr into Wybe string syntax.
let rec exprToWybe e =
  match e with
  | Var v -> v
  | Integer i -> i.ToString()
  | Op(op, left, right) -> sprintf "(%s %s %s)" (exprToWybe left) op (exprToWybe right)
  | _ -> failwithf "Unsupported expression in proof obligation: %A" e

/// Disambiguated alias for Value to bind the string * string overload.
let private mkValue: string * string -> WidgetBuilder<_> = Value

/// Extract proof obligations from parsed functions.
/// A proof obligation is named <func>_obl_<idx> for each CommentAssertion.
let extractProofObligations (funcs: Function list) : (string * Expr) list =
  funcs
  |> List.collect (fun func ->
    func.Body
    |> List.mapi (fun idx expr ->
      match expr with
      | CommentAssertion cond -> Some(sprintf "%s_obl_%d" func.Name idx, cond)
      | _ -> None)
    |> List.choose id)

/// Generate F# code for proof obligations using Fabulous.AST.
let generateProofCode obligations =
  // Generate code for each obligation using AST and fantomas
  obligations
  |> List.map (fun (id, expr) ->
    let proofText = sprintf "proof {\n    assert (%s)\n}" (exprToWybe expr)
    // Build a mini-AST: an anonymous module with a single value binding
    let ast = Oak() { AnonymousModule() { mkValue (id, proofText) } }
    ast |> Gen.mkOak |> Gen.run)
  |> String.concat "\n\n"

/// Emit proof obligations to the given TextWriter.
/// The header includes loading and opening Wybe.Core, followed by generated obligations.
let emitProofScript (writer: TextWriter) (funcs: Function list) =
  let obligations = extractProofObligations funcs
  // Header: load Wybe.Core and open namespace
  let header = [ "#r \"nuget: Wybe\""; "open Wybe.Core"; "" ] |> String.concat "\n"

  let body = generateProofCode obligations
  // Write header and body to the provided writer
  writer.Write header
  writer.Write "\n\n"
  writer.Write body

/// Convenience: emit proof obligations directly to a file at the given path.
let emitProofScriptToFile (filePath: string) (funcs: Function list) =
  use writer = File.CreateText(filePath)
  emitProofScript writer funcs
