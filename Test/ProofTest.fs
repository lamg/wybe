module ProofTest

open GriesSchneider.Axioms
open TypedExpression
open Inference
open CalculationCE

let p, q = Var "p", Var "q"

let proofTrueNoCE () : Calculation =
  //   (p ≡ q) ≡ (q ≡ p)
  // ≡ { assoc }
  //   p ≡ (q ≡ (q ≡ p))
  // ≡ { sym assoc }
  //   p ≡ ((q ≡ q) ≡ p))
  // ≡ { ≡-ident }
  //   p ≡ (true ≡ p)
  // ≡ { ≡-sym }
  //   p ≡ (p ≡ true)
  // ≡ { sym assoc }
  //   (p ≡ p) ≡ true
  // ≡ { ≡-ident, ≡-ident }
  //   true
  let idLaws (xs: Law list) =
    xs |> List.map (fun l -> l.id, l) |> List.unzip

  let id0, laws0 = [ ``≡ assoc``; sym ``≡ assoc``; ``≡ ident`` ] |> idLaws

  let limits: StepExpansion.GenerationLimits =
    { maxAlternatives = 1
      maxAlternativeLength = 7 }

  let generator0 =
    { id = id0 |> String.concat ", "
      generator = fun _ _ -> seq { laws0 }
      limits = limits }

  let id1, laws1 = [ ``≡ sym``; sym ``≡ assoc``; ``≡ ident``; ``≡ ident`` ] |> idLaws

  let generator1 =
    { id = id1 |> String.concat ", "
      generator = fun _ _ -> seq { laws1 }
      limits = limits }

  let steps =
    [| { expr = (p === q) === (q === p) |> getTypedExpr
         hint =
           Hint.Law
             { op = equivSymbol
               lawGenerator = generator0 } }
       { expr = p === (True === p) |> getTypedExpr
         hint =
           Hint.Law
             { op = equivSymbol
               lawGenerator = generator1 } }
       { expr = p === (True === p) |> getTypedExpr
         hint = Hint.End } |]

  { demonstrandum = True |> axiom "true-theorem"
    leibniz = [ ``≡ leibniz`` ]
    transitivity = [ ``≡ transitivity`` ]
    applyToResult = [ ``≡ sym`` ]
    steps = steps }

let trueTheorem =
  proof () {
    Theorem("true_theorem", True)
    WithLaws [ ``≡ sym`` ]
    p === q === (q === p)

    ``≡`` {
      ``≡ assoc``
      sym ``≡ assoc``
      ``≡ ident``
    }

    p === (True === p)

    ``≡`` {
      ``≡ sym``
      sym ``≡ assoc``
      ``≡ ident``
      ``≡ ident``
    }

    True
  }
