module InspectTest

open Inspect
open Inspect.Inspect
open Z3
open Xunit
open FsUnit


let equal (expected: 'a) (actual: 'a) = should equal expected actual

let accEqual (expected: string list) (n: Inspection<'a>) =

  should equalSeq (List.toArray expected) (List.toArray n.accumulated)

let trueTheorem () =
  let p, q = Var "p", Var "q"

  proof () {
    Theorem("true theorem", Pred.True)
    p === q === (q === p)

    ``≡`` { }

    Pred.True
  }

[<Fact>]
let ``inspect a calculation`` () =
  let expected =
    [ ColorMessages.section "calculation"
      ColorMessages.info "demonstrandum" "true"
      "  p ≡ q ≡ q ≡ p"
      "≡ {  }"
      "  true"
      "▢" ]

  trueTheorem () |> inspect |> calculation |> accEqual expected

[<Fact>]
let ``inspect a step`` () =
  let expected = [ "  p ≡ q ≡ q ≡ p"; "≡ {  }"; "  true" ]

  trueTheorem () |> inspect |> stepAt 0 |> accEqual expected


[<Fact>]
let ``inspect hint`` () =
  let expected = [ ColorMessages.sectionBody "hint at 0" "≡ {  }" ]

  trueTheorem () |> inspect |> hintAt 0 |> accEqual expected


[<Fact>]
let ``proof of true summary`` () =
  let expected =
    [ ColorMessages.section "summary"
      ColorMessages.info "demonstrandum" "true"
      "  p ≡ q ≡ q ≡ p"
      "≡ {  }"
      "  true"
      "▢"
      ColorMessages.info "✅ theorem" "true theorem" ]

  trueTheorem () |> inspect |> summary |> accEqual expected

[<Fact>]
let ``failed proof summary`` () =
  let x, y, z = Var "x", Var "y", Var "z"

  let expected =
    [ ColorMessages.section "summary"
      ColorMessages.info "demonstrandum" "x ≡ y"
      "  x"
      "≡ {  }"
      "  y"
      "≡ {  }"
      "  z"
      "▢"
      ColorMessages.info "❌ theorem" "x ≡ y"
      ColorMessages.error "failed" "0, 1" ]

  proof () {
    Theorem("x ≡ y", x === y)
    x
    ``≡`` { }
    y
    ``≡`` { }
    z
  }
  |> inspect
  |> summary
  |> accEqual expected

[<Fact>]
let ``out of bounds step`` () =
  let expected =
    [ ColorMessages.sectionBody "step at" "19"
      ColorMessages.error "out of range" "0 ≤ 19 < 1" ]

  trueTheorem () |> inspect |> stepAt 19 |> accEqual expected
