#r "nuget: Wybe, 0.0.5"

open Wybe
open Core
open Inspect

let x = mkBoolVar "x"

let ``hola mundo`` () =
  proof { theorem "hola mundo" (x === x) }

// ``hola mundo`` () |> inspect |> summary |> print

// GriesSchneider.PredicateCalculus.``GS 3.14`` () |> inspect |> summary |> print
