module InspectTest

open CalculationCE
open TypedExpression
open Inspect
open Inspect.Inspect
open ProofTest
open Xunit
open FsUnit

let rewriter_0 = [| "x ≡ y ↦ y ≡ x"; "x ≡ x ↦ true" |]
let rewriter_1 = [| "x ≡ y ↦ x ≡ y"; "x ≡ x ↦ true" |]
let rewriter_2 = [| "y ≡ x ↦ x ≡ y"; "x ≡ x ↦ true" |]
let rewriter_3 = [| "y ≡ x ↦ y ≡ x"; "x ≡ x ↦ true" |]
let rewriter_4 = [| "x ≡ y ↦ y ≡ x"; "true ↦ x ≡ x" |]

let expansion_0 =
  [| "(p ≡ q) ≡ (q ≡ p) ✅0"
     "├── (q ≡ p) ≡ (p ≡ q) ❌"
     "├── (q ≡ p) ≡ (q ≡ p) ✅0"
     "│   └── true ✅0"
     "└── (p ≡ q) ≡ (p ≡ q) ✅1"
     "   └── true ✅1" |]

let expansion_1 = [| "(p ≡ q) ≡ (q ≡ p) ❌" |]

let expansion_2 =
  [| "(p ≡ q) ≡ (q ≡ p) ✅0"
     "├── (q ≡ p) ≡ (p ≡ q) ❌"
     "├── (q ≡ p) ≡ (q ≡ p) ✅0"
     "│   └── true ✅0"
     "└── (p ≡ q) ≡ (p ≡ q) ✅1"
     "   └── true ✅1" |]

let expansion_3 = [| "(p ≡ q) ≡ (q ≡ p) ❌" |]

let expansion_4 =
  [| "(p ≡ q) ≡ (q ≡ p) ❌"
     "├── (q ≡ p) ≡ (p ≡ q) ❌"
     "├── (q ≡ p) ≡ (q ≡ p) ❌"
     "└── (p ≡ q) ≡ (p ≡ q) ❌" |]

let equal (expected: 'a) (actual: 'a) = should equal expected actual
let accEqual (expected: string array) (n: Inspection) = should equalSeq expected n.accumulated



[<Fact>]
let ``inspect a calculation`` () =
  let expected =
    [| ColorMessages.section "calculation"
       ColorMessages.info "demonstrandum" "true"
       "  (p ≡ q) ≡ (q ≡ p)"
       "≡ { ≡ sym, ≡ ident }"
       "  true"
       "▢" |]

  trueTheorem |> inspect |> calculation |> accEqual expected

[<Fact>]
let ``inspect a step`` () =
  let expected =
    seq {
      ColorMessages.sectionBody "step at" "0"

      ColorMessages.info "alt_0" ""
      Formatters.indentLine 2 (ColorMessages.info "rewriter" "")
      yield! rewriter_0 |> Seq.map (Formatters.indentLine 2)
      Formatters.indentLine 2 (ColorMessages.info "expansion" "")
      yield! expansion_0 |> Seq.map (Formatters.indentLine 2)

      ColorMessages.info "alt_1" ""
      Formatters.indentLine 2 (ColorMessages.info "rewriter" "")
      yield! rewriter_1 |> Seq.map (Formatters.indentLine 2)
      Formatters.indentLine 2 (ColorMessages.info "expansion" "")
      yield! expansion_1 |> Seq.map (Formatters.indentLine 2)

      ColorMessages.info "alt_2" ""
      Formatters.indentLine 2 (ColorMessages.info "rewriter" "")
      yield! rewriter_2 |> Seq.map (Formatters.indentLine 2)
      Formatters.indentLine 2 (ColorMessages.info "expansion" "")
      yield! expansion_2 |> Seq.map (Formatters.indentLine 2)

      ColorMessages.info "alt_3" ""
      Formatters.indentLine 2 (ColorMessages.info "rewriter" "")
      yield! rewriter_3 |> Seq.map (Formatters.indentLine 2)
      Formatters.indentLine 2 (ColorMessages.info "expansion" "")
      yield! expansion_3 |> Seq.map (Formatters.indentLine 2)

      ColorMessages.info "alt_4" ""
      Formatters.indentLine 2 (ColorMessages.info "rewriter" "")
      yield! rewriter_4 |> Seq.map (Formatters.indentLine 2)
      Formatters.indentLine 2 (ColorMessages.info "expansion" "")
      yield! expansion_4 |> Seq.map (Formatters.indentLine 2)
    }
    |> Seq.toArray

  trueTheorem |> inspect |> stepAt 0 |> accEqual expected

[<Fact>]
let ``inspect rewriters at step`` () =
  let expected =
    seq {
      ColorMessages.sectionBody "rewriters at" "0"
      ColorMessages.info "rewriter_0" ""
      yield! rewriter_0
      ColorMessages.info "rewriter_1" ""
      yield! rewriter_1
      ColorMessages.info "rewriter_2" ""
      yield! rewriter_2
      ColorMessages.info "rewriter_3" ""
      yield! rewriter_3
      ColorMessages.info "rewriter_4" ""
      yield! rewriter_4
    }
    |> Seq.toArray

  trueTheorem |> inspect |> rewritersAt 0 |> accEqual expected

[<Fact>]
let ``inspect expansions at step`` () =
  let expected =
    seq {
      ColorMessages.sectionBody "expansions at" "0"
      ColorMessages.info "expansion_0" ""
      yield! expansion_0
      ColorMessages.info "expansion_1" ""
      yield! expansion_1
      ColorMessages.info "expansion_2" ""
      yield! expansion_2
      ColorMessages.info "expansion_3" ""
      yield! expansion_3
      ColorMessages.info "expansion_4" ""
      yield! expansion_4
    }
    |> Seq.toArray

  trueTheorem |> inspect |> expansionsAt 0 |> accEqual expected

[<Fact>]
let ``inspect step alternative rewriters and expansion`` () =
  let expected =
    seq {
      ColorMessages.sectionBody "alternatives at" "0"
      ColorMessages.info "alternative_0" ""
      ColorMessages.info "rewriter_0" ""
      yield! rewriter_0
      ColorMessages.info "expansion_0" ""
      yield! expansion_0
    }
    |> Seq.toArray

  trueTheorem |> inspect |> alternativeAt 0 0 |> accEqual expected

[<Fact>]
let ``inspect hint`` () =
  let expected = [| ColorMessages.sectionBody "hint at" "0"; "≡ { ≡ sym, ≡ ident }" |]

  trueTheorem |> inspect |> hintAt 0 |> accEqual expected

[<Fact>]
let ``composite inspection`` () =
  let expected =
    [| ColorMessages.sectionBody "hint at" "0"
       "≡ { ≡ sym, ≡ ident }"
       ColorMessages.sectionBody "alternatives at" "0"
       ColorMessages.info "alternative_0" ""
       ColorMessages.info "rewriter_0" ""
       "x ≡ y ↦ y ≡ x"
       "x ≡ x ↦ true"
       ColorMessages.info "expansion_0" ""
       "(p ≡ q) ≡ (q ≡ p) ✅0"
       "├── (q ≡ p) ≡ (p ≡ q) ❌"
       "├── (q ≡ p) ≡ (q ≡ p) ✅0"
       "│   └── true ✅0"
       "└── (p ≡ q) ≡ (p ≡ q) ✅1"
       "   └── true ✅1" |]

  trueTheorem |> inspect |> hintAt 0 |> alternativeAt 0 0 |> accEqual expected

[<Fact>]
let ``proof of true summary`` () =
  let expected =
    [| ColorMessages.section "summary"
       ColorMessages.info "demonstrandum" "true"
       "  (p ≡ q) ≡ (q ≡ p)"
       "≡ { ≡ sym, ≡ ident }"
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
    [| ColorMessages.section "summary"
       ColorMessages.info "demonstrandum" "x ≡ y"
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

[<Fact>]
let ``out of bounds step`` () =
  let expected =
    [| ColorMessages.sectionBody "step at" "19"
       ColorMessages.error "index out of range" "19 not in 0 ≤ i < 1" |]

  trueTheorem |> inspect |> stepAt 19 |> accEqual expected
