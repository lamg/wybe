module InspectTest

open Inspect
open Core
open Xunit
open FsUnit
open GriesSchneider

let accEqual (expected: string list) (n: Inspection) =
  should equalSeq (List.toArray expected) (List.toArray n.accumulated)

let x, y, z = mkBoolVar "x", mkBoolVar "y", mkBoolVar "z"
let True = Proposition.True
let False = Proposition.False

let trueTheorem () =
  proof {
    theorem "true theorem" True
    x === y === (y === x)

    ``≡`` { }

    True
  }

[<Fact>]
let ``inspect a calculation`` () =
  let expected =
    [ section "calculation"
      info "demonstrandum" "true"
      "  x ≡ y ≡ y ≡ x"
      "≡ {  }"
      "  true"
      "▢" ]

  trueTheorem () |> inspect |> calculation |> accEqual expected

[<Fact>]
let ``inspect a step`` () =
  let expected = [ "  x ≡ y ≡ y ≡ x"; "≡ {  }"; "  true" ]

  trueTheorem () |> inspect |> stepAt 0 |> accEqual expected


[<Fact>]
let ``inspect hint`` () =
  let expected = [ sectionBody "hint at 0" "≡ {  }" ]

  trueTheorem () |> inspect |> hintAt 0 |> accEqual expected


[<Fact>]
let ``proof of true summary`` () =
  let expected =
    [ section "proof"
      info "  theorem" "true ✅"
      "  x ≡ y ≡ y ≡ x"
      "≡ {  }"
      "  true"
      section "▢" ]

  trueTheorem () |> inspect |> summary |> accEqual expected

[<Fact>]
let ``failed proof summary`` () =

  let expected =
    [ section "proof"
      info "  theorem" "x ≡ y ❌"
      "  x"
      "≡ {  }"
      "  y"
      "≡ {  }"
      "  z"
      section "▢"
      error "failed steps" ""
      "0: x ≡ y | Refuted \"false\""
      "1: y ≡ z | Refuted \"false\"" ]

  proof {
    theorem "x ≡ y" (x === y)
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
  let expected = [ sectionBody "step at" "19"; error "out of range" "0 ≤ 19 < 1" ]

  trueTheorem () |> inspect |> stepAt 19 |> accEqual expected

[<Fact>]
let ``print predicates`` () =

  [ !(!x), "¬¬x"
    x === y === y === x, "x ≡ y ≡ y ≡ x"
    x <&&> y <||> x, "(x ∧ y) ∨ x"
    x <&&> y <&&> x, "x ∧ y ∧ x"
    x === y !== x, "x ≡ y ≢ x"
    x <&&> x === y, "x ∧ x ≡ y"
    !x <&&> x, "¬x ∧ x"
    !(x <&&> x), "¬(x ∧ x)"
    x === x ==> (x === y), "(x ≡ x) ⇒ (x ≡ y)"
    True, "true"
    x, "x" ]
  |> List.iter (fun (p, expected) ->
    let r = p.ToString()
    r |> should equal expected)

[<Fact>]
let ``inspect calculation steps with error`` () =
  let expected =
    [ error "failed steps" ""
      "0: x ≡ y | Refuted \"false\""
      "1: y ≡ z | Refuted \"false\"" ]

  proof {
    theorem "x ≡ y" (x === y)
    x
    ``≡`` { }
    y
    ``≡`` { }
    z
  }
  |> inspect
  |> calculationError
  |> accEqual expected


[<Fact>]
let ``inspect calculation with wrong evidence`` () =
  let expected =
    [ error "invalid evidence" ""
      $"❌ counter-example found: false"
      $"assuming: x ≡ x"
      $"to conclude: x ≡ y" ]

  proof {
    theorem "x ≡ y" (x === y)
    x
    ``≡`` { }
    x
  }
  |> inspect
  |> calculationError
  |> accEqual expected

[<Fact>]
let ``testing De Morgan's law`` () =

  let expected =
    [ section "proof"
      info "  theorem" "¬⟨∀x → x ∧ x⟩ ≡ ⟨∃x → ¬x⟩ ✅"
      "  ¬⟨∀x → x ∧ x⟩"
      "≡ { De Morgan }"
      "  ⟨∃x → ¬x⟩"
      section "▢" ]

  let testFormula = !(``∀`` [ x ] (x <&&> x)) === ``∃`` [ x ] !x

  let simpleProof =

    proof {
      theorem "testing ∀ and ∃" testFormula
      !(``∀`` [ x ] (x <&&> x))
      ``≡`` { ``De Morgan`` ([ x ], x <&&> x) }
      ``∃`` [ x ] !x
    }

  simpleProof |> inspect |> summary |> accEqual expected

  let implicitDeMorgan =
    proof {
      theorem "¬⟨∀x → x ∧ x⟩ ≡ ⟨∃x → ¬x⟩" testFormula
      !(``∀`` [ x ] (x <&&> x))
      ``≡`` { }
      ``∃`` [ x ] !x
    }

  implicitDeMorgan |> _.Error.IsNone |> Assert.True
