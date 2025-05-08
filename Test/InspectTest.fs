module InspectTest

open Inspect
open Inspect.Inspect
open Core
open Xunit
open FsUnit

let theorem = GriesSchneider.PredicateCalculus.theorem

let accEqual (expected: string list) (n: Inspection) =
  should equalSeq (List.toArray expected) (List.toArray n.accumulated)

let x, y, z = Bool(Bool.Var "x"), Bool(Bool.Var "y"), Bool(Bool.Var "z")
let True = Bool Bool.True

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
    [ ColorMessages.section "calculation"
      ColorMessages.info "demonstrandum" "true"
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
  let expected = [ ColorMessages.sectionBody "hint at 0" "≡ {  }" ]

  trueTheorem () |> inspect |> hintAt 0 |> accEqual expected


[<Fact>]
let ``proof of true summary`` () =
  let expected =
    [ ColorMessages.section "summary"
      ColorMessages.info "demonstrandum" "true"
      "  x ≡ y ≡ y ≡ x"
      "≡ {  }"
      "  true"
      "▢"
      ColorMessages.info "✅ theorem" "true theorem" ]

  trueTheorem () |> inspect |> summary |> accEqual expected

[<Fact>]
let ``failed proof summary`` () =

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
  let expected =
    [ ColorMessages.sectionBody "step at" "19"
      ColorMessages.error "out of range" "0 ≤ 19 < 1" ]

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
    Bool Bool.True, "true"
    x, "x" ]
  |> List.iter (fun (p, expected) ->
    let r = p.ToString()
    r |> should equal expected)

[<Fact>]
let ``inspect calculation steps with error`` () =
  let expected = [ ColorMessages.error "failed steps" ""; "0: x ≡ y"; "1: y ≡ z" ]

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
    [ ColorMessages.error "invalid evidence" ""
      "calculation reduces to: x ≡ x"
      "❌ implication does not hold: (x ≡ x) ⇒ (x ≡ y)" ]

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
  let ``De Morgan`` = GriesSchneider.PredicateCalculus.``De Morgan``

  let expected =
    [ ColorMessages.section "summary"
      ColorMessages.info "demonstrandum" "¬⟨∀x → x ∧ x⟩ ≡ ⟨∃x → ¬x⟩"
      "  ¬⟨∀x → x ∧ x⟩"
      "≡ { De Morgan }"
      "  ⟨∃x → ¬x⟩"
      "▢"
      ColorMessages.info "✅ theorem" "testing ∀ and ∃" ]

  let testFormula = !(``∀`` [ x ] (x <&&> x)) === ``∃`` [ x ] !x

  let simpleProof =

    proof {
      theorem "testing ∀ and ∃" testFormula
      !(``∀`` [ x ] (x <&&> x))
      ``≡`` { ``De Morgan`` (fun x -> x <&&> x) }
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

  implicitDeMorgan |> _.error.IsNone |> Assert.True
