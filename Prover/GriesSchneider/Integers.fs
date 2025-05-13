module GriesSchneider.Integers

open Core

let x, y, z = mkIntVar "x", mkIntVar "y", mkIntVar "z"
let zero = Integer 0
let one = Integer 1

#nowarn 86
let (>=) (x: Integer) (y: Integer) = ExtBoolOp(AtLeast(x, y))
let (<=) (x: Integer, y: Integer) = ExtBoolOp(AtMost(x, y))
let (<) (x: Integer) (y: Integer) = ExtBoolOp(LessThan(x, y))
let (>) (x: Integer) (y: Integer) = ExtBoolOp(Exceeds(x, y))



let ``+ associativity`` = x + y + z = x + y + z |> axiom "+ associativity"

let ``× associativity`` = (x * y) * z = x * (y * z) |> axiom "× associativity"

let ``+ symmetry`` = x + y = y + x |> axiom "+ symmetry"

let ``× symmetry`` = x * y = y * x |> axiom "× symmetry"

let ``+ identity`` = x + zero = x |> axiom "+ identity"
let ``× identity`` = x * one = x |> axiom "× identity"

let ``+ over ×`` = x * (y + z) = x * y + x * z |> axiom "+ over ×"

let ``+ inverse`` = ``∃`` [ x ] (x + y = zero) |> axiom "+ inverse"

let ``× cancellation`` =
  z != zero ==> (z * x = z * y === (x = y)) |> axiom "× cancellation"

let ``+ cancellation`` () =
  proof { theorem "+ cancellation" (x + y = x + z === (y = z)) }

let ``× zero`` () =
  proof {
    theorem "× zero" (x * zero = zero)
    x * zero
    ``==`` { }
    zero
  }
