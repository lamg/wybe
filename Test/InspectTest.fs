module InspectTest

open CalculationCE
open TypedExpression
open Inspect
open Inspect.Inspect
open ProofTest
open Xunit

let equal (expected: 'a) (actual: 'a) = Assert.Equal<'a>(expected, actual)
let accEqual (expected: string array) (n: Inspection) = n.accumulated |> equal expected

[<Fact>]
let ``inspect a calculation`` () =
  let expected =
    [| "theorem true"
       "  (p ≡ q) ≡ (q ≡ p)"
       "≡ { ≡ assoc, sym ≡ assoc, ≡ ident }"
       "  p ≡ (true ≡ p)"
       "≡ { ≡ sym, sym ≡ assoc, ≡ ident, ≡ ident }"
       "  true"
       "▢" |]

  trueTheorem |> inspect |> calculation |> accEqual expected

[<Fact>]
let ``inspect a step`` () =
  let expected =
    [| ColorMessages.info "step" "0"
       ColorMessages.info "alt_0" ""
       ColorMessages.info "rewriter" ""
       "(x ≡ y) ≡ z ↦ x ≡ (y ≡ z)"
       "x ≡ (y ≡ z) ↦ (x ≡ y) ≡ z"
       "x ≡ x ↦ true"
       ColorMessages.info "expansion" ""
       "(p ≡ q) ≡ (q ≡ p) ✅0"
       "└── p ≡ (q ≡ (q ≡ p)) ✅0"
       "   ├── (p ≡ q) ≡ (q ≡ p) ❌"
       "   └── p ≡ ((q ≡ q) ≡ p) ✅0"
       "      └── p ≡ (true ≡ p) ✅0" |]

  trueTheorem |> inspect |> stepAt 0 |> accEqual expected

[<Fact>]
let ``inspect rewriters at step`` () =
  let expected =
    [| ColorMessages.info "step" "0"
       ColorMessages.info "rewriter_0" ""
       "(x ≡ y) ≡ z ↦ x ≡ (y ≡ z)"
       "x ≡ (y ≡ z) ↦ (x ≡ y) ≡ z"
       "x ≡ x ↦ true" |]

  trueTheorem |> inspect |> rewritersAt 0 |> accEqual expected

[<Fact>]
let ``inspect expansions at step`` () =
  let expected =
    [| ColorMessages.info "step" "0"
       ColorMessages.info "expansion_0" ""
       "(p ≡ q) ≡ (q ≡ p) ✅0"
       "└── p ≡ (q ≡ (q ≡ p)) ✅0"
       "   ├── (p ≡ q) ≡ (q ≡ p) ❌"
       "   └── p ≡ ((q ≡ q) ≡ p) ✅0"
       "      └── p ≡ (true ≡ p) ✅0" |]

  trueTheorem |> inspect |> expansionsAt 0 |> accEqual expected

[<Fact>]
let ``inspect step alternative rewriters and expansion`` () =
  let expected =
    [| ColorMessages.info "step" "0"
       ColorMessages.info "alternative_0" ""
       ColorMessages.info "rewriter_0" ""
       "(x ≡ y) ≡ z ↦ x ≡ (y ≡ z)"
       "x ≡ (y ≡ z) ↦ (x ≡ y) ≡ z"
       "x ≡ x ↦ true"
       ColorMessages.info "expansion_0" ""
       "(p ≡ q) ≡ (q ≡ p) ✅0"
       "└── p ≡ (q ≡ (q ≡ p)) ✅0"
       "   ├── (p ≡ q) ≡ (q ≡ p) ❌"
       "   └── p ≡ ((q ≡ q) ≡ p) ✅0"
       "      └── p ≡ (true ≡ p) ✅0" |]

  trueTheorem |> inspect |> alternativeAt 0 0 |> accEqual expected

[<Fact>]
let ``inspect hint`` () =
  let expected =
    [| ColorMessages.info "hint_0" "≡ { ≡ assoc, sym ≡ assoc, ≡ ident }" |]

  trueTheorem |> inspect |> hintAt 0 |> accEqual expected

[<Fact>]
let ``composite inspection`` () =
  let expected =
    [| ColorMessages.info "hint_0" "≡ { ≡ assoc, sym ≡ assoc, ≡ ident }"
       ColorMessages.info "step" "0"
       ColorMessages.info "alt_0" ""
       ColorMessages.info "rewriter" ""
       "(x ≡ y) ≡ z ↦ x ≡ (y ≡ z)"
       "x ≡ (y ≡ z) ↦ (x ≡ y) ≡ z"
       "x ≡ x ↦ true"
       ColorMessages.info "expansion" ""
       "(p ≡ q) ≡ (q ≡ p) ✅0"
       "└── p ≡ (q ≡ (q ≡ p)) ✅0"
       "   ├── (p ≡ q) ≡ (q ≡ p) ❌"
       "   └── p ≡ ((q ≡ q) ≡ p) ✅0"
       "      └── p ≡ (true ≡ p) ✅0" |]

  trueTheorem |> inspect |> hintAt 0 |> stepAt 0 |> accEqual expected

[<Fact>]
let ``proofTrue summary`` () =
  let expected =
    [| "theorem true"
       "  (p ≡ q) ≡ (q ≡ p)"
       "≡ { ≡ assoc, sym ≡ assoc, ≡ ident }"
       "  p ≡ (true ≡ p)"
       "≡ { ≡ sym, sym ≡ assoc, ≡ ident, ≡ ident }"
       "  true"
       "▢"
       ColorMessages.info "theorem" "true_theorem"
       ColorMessages.info "ok proof" "True"
       ColorMessages.info "ok steps" "True"
       ColorMessages.info "ok transitivity" "True"
       ColorMessages.info "ok evidence" "True" |]

  trueTheorem |> inspect |> summary |> accEqual expected

[<Fact>]
let ``failed proof summary`` () =
  let x, y, z = Var "x", Var "y", Var "z"

  let expected =
    [| "theorem x ≡ y"
       "  x"
       "≡ {  }"
       "  y"
       "≡ {  }"
       "  z"
       "▢"
       ColorMessages.info "theorem" "x ≡ y"
       ColorMessages.error "ok proof" "False"
       ColorMessages.error "ok steps" "False"
       ColorMessages.error "failed steps" "0, 1"
       ColorMessages.info "ok transitivity" "True"
       ColorMessages.error "ok evidence" "False" |]

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
