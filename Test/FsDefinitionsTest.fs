module FsDefinitionsTest

open Xunit
open FsDefinitions
open Core
open GriesSchneider

#nowarn 86


[<Fact>]
let ``extract typed variables from insert function`` () =
  let file = "insert.fsx"

  let source =
    """
let rec insert (n: int) =
 function
 | [] -> [ n ]
 | x :: xs when n <= x -> n :: x :: xs
 | x :: xs -> x :: insert n xs"""

  let exprs = getWybeExpressions (file, source)

  match exprs with
  | Ok xs -> printfn $"EXPRS {xs}"
  | Error e -> failwith e

[<Fact>]
let ``extract from failwith`` () =
  let file = "failwith.fsx"

  let source =
    """
let fw (n: int) =
  function
  | ([]: int list) -> [ n ]
  | _ -> failwith "non empty list"
  """

  let exprs = getWybeExpressions (file, source)

  match exprs with
  | Ok xs -> printfn $"EXPRS {xs}"
  | Error e -> failwith e
