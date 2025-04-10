module Inference

open ExpressionMatch
open StepExpansion
open TypedExpression
open FsToolkit.ErrorHandling

type Law = { expr: TypedExpr; id: string }

type CompilationError =
  | WrongLeibniz of Law
  | WrongTransitivity of Law
  | EmptyCalculation

type Leibniz = TypedSymbol -> Law -> Rewriter<TypedSymbol> option

// leibniz: a predicate like x <eq0> y  ↦  f.x <eq1> f.y
// stepOp: equal to <eq1>, for the step to match with f.x <eq1> f.y
// hint: a law that matches with x <eq0> y
// the resulting rule should be able to check a step in the form
//   f.x
// <eq1> { law0 }
//   f.y
// where law0 matches x <eq0> y
let makeLeibnizRule (leibniz: Law) : Result<Leibniz, CompilationError> =
  result {
    let! xEqY, fxEqFy =
      match leibniz.expr with
      | { node = { signature = s }
          subtrees = [ xEqY; fxEqFy ] } when s = boolId -> Ok(xEqY, fxEqFy)
      | _ -> WrongLeibniz leibniz |> Error

    let rule stepOp (hint: Law) =
      match stepOp with
      | { signature = Fun [ _; _; last ] } when fxEqFy.node.symbol = stepOp.symbol && last = boolId ->
        let m = matchTree matchSymbol xEqY hint.expr

        match m with
        | (_, fx) :: (_, fy) :: _ ->
          Some
            { lhs = fx
              rhs = fy
              isNodeMatch = matchSymbol
              id = hint.id }
        | _ -> None
      | _ -> None

    return rule
  }

type Transitivity = TypedExpr -> TypedExpr -> TypedExpr option

// transitivity: a predicate in the form (x <imp0> y) ∧ (y <imp1> z) ↦ x <imp2> z
// returns a function that matches two expressions like (x <imp0> y), (y <imp1> z)
// and returns a result expression like x <imp2> z
let makeTransitivityRule (transitivity: Law) : Result<Transitivity, CompilationError> =
  result {
    let! t0, t1, imp2 =
      match transitivity.expr with
      | { subtrees = [ { subtrees = [ { subtrees = [ x; y ] } as t0; { subtrees = [ y'; z ] } as t1 ] }
                       { node = imp2; subtrees = [ x'; z' ] } ] } when x = x' && y = y' && z = z' -> Ok(t0, t1, imp2)
      | _ -> WrongTransitivity transitivity |> Error

    let rule s0 s1 =
      let t0 = matchTree matchSymbol t0 s0
      let t1 = matchTree matchSymbol t1 s1

      match t0, t1 with
      | [ _, x; _, y ], [ _, y'; _, z ] when y = y' -> Some { node = imp2; subtrees = [ x; z ] }
      | _ -> None

    return rule
  }

type StepOp =
  { step: Step<TypedSymbol>
    op: TypedSymbol option }

let fold1Until (f: 'a -> 'a -> 'a option) (xs: 'a list) =
  let rec loop (acc: 'a) (xs: 'a list) =
    match xs with
    | [] -> true, acc
    | y :: ys ->
      match f acc y with
      | Some z -> loop z ys
      | None -> false, acc

  match xs with
  | [] -> failwith "expecting non-empty list"
  | y :: ys -> loop y ys

// creates an expression joining consecutive pairs of steps with the operator of the first
// expressions are reduced using one of the applicable transitivity rules
let transitiveReduction (ts: Transitivity list) (steps: StepOp array) =
  steps
  |> Array.pairwise
  |> Array.mapi (fun i (x, y) ->
    let joined =
      { node = { x.op.Value with signature = boolId }
        subtrees = [ x.step.expr; y.step.expr ] }

    i, joined)
  |> Array.toList
  |> fold1Until (fun (_, acc) (j, y) ->
    ts
    |> List.choose (fun transitivity -> transitivity acc y)
    |> List.tryHead
    |> function
      | Some r -> Some(j, r)
      | None -> None)


type Evidence =
  | DemonstrandumEqualLaw of dem: TypedExpr * Law: TypedExpr
  | ReductionEqualTheorem
  | ReductionImpliesDemonstrandum of TypedExpr

// checks if the reduction resulting of transitivity proves the demonstrandum, returning found evidence
let provesTheorem (availableLaws: Law list) (expectedTheorem: Law) (transitivityReduction: TypedExpr) =
  let demonstrandum = expectedTheorem.expr
  let laws = availableLaws |> List.map _.expr

  let matchesLaw x =
    laws |> List.exists (fun l -> matchTree matchSymbol l x |> _.IsEmpty |> not)

  let impliesDemonstrandum = false // TODO implement

  match transitivityReduction with
  | _ when transitivityReduction = demonstrandum -> Some ReductionEqualTheorem
  | { node = { symbol = Fixed "≡" }
      subtrees = [ x; y ] } when x = demonstrandum && matchesLaw y -> Some(DemonstrandumEqualLaw(x, y))
  | { node = { symbol = Fixed "≡" }
      subtrees = [ x; y ] } when y = demonstrandum && matchesLaw x -> Some(DemonstrandumEqualLaw(y, x))
  | _ when impliesDemonstrandum -> Some(ReductionImpliesDemonstrandum transitivityReduction)
  | _ -> None


type LawGenerator =
  { id: string
    generator: TypedExpr -> TypedExpr option -> Law seq seq
    limits: GenerationLimits }

type LawHint =
  { op: TypedSymbol
    lawGenerator: LawGenerator }

[<RequireQualifiedAccess>]
type Hint =
  | Law of LawHint
  | End

type CalcStep = { expr: TypedExpr; hint: Hint }

type Calculation =
  { leibniz: Law list
    transitivity: Law list
    applyToResult: Law list
    demonstrandum: Law
    steps: CalcStep array }

let countFits (matcher: Expression<'a>) (target: Expression<'a>) =
  let rec treeHeight t =
    match t with
    | { subtrees = [] } -> 1
    | _ -> t.subtrees |> List.map treeHeight |> List.max |> ((+) 1)

  let heightTarget = treeHeight target
  let heightMatcher = treeHeight matcher

  match true with
  | _ when heightMatcher > heightTarget -> 0
  | _ -> heightTarget - heightMatcher + 1

type CalcChecker<'a when 'a: equality> =
  { transitivity: Transitivity list
    steps: StepOp array
    getEvidence: TypedExpr -> Evidence option }

let compileCalculation (c: Calculation) =
  result {
    let! leibniz = c.leibniz |> List.map makeLeibnizRule |> List.sequenceResultM
    let! transitivity = c.transitivity |> List.map makeTransitivityRule |> List.sequenceResultM

    let getLeibnizRewriters (op: TypedSymbol) (laws: Law seq) =
      laws |> Seq.collect (fun y -> leibniz |> List.choose (fun l -> l op y))

    let getEvidence reduction =
      provesTheorem c.applyToResult c.demonstrandum reduction

    return
      { transitivity = transitivity
        steps =
          c.steps
          |> Array.map (fun s ->

            let op, rewriters, limits =
              match s.hint with
              | Hint.End ->
                None,
                seq { },
                { maxAlternatives = 0
                  maxAlternativeLength = 0 }
              | Hint.Law l ->
                // TODO pass the next expression if no end, instead of always None
                // with the current and next expression the generator can use a tactic to propose
                // alternative sequences of laws that could check the step
                let nextExpr = None

                let rs =
                  l.lawGenerator.generator s.expr nextExpr |> Seq.map (getLeibnizRewriters l.op)

                Some l.op, rs, l.lawGenerator.limits

            { step =
                { rewriters = rewriters
                  expr = s.expr
                  limits = limits }
              op = op })
        getEvidence = getEvidence }
  }


type Check =
  { transitiveReduction: int * TypedExpr
    expandedSteps: StepExpansion<TypedSymbol> array
    evidence: Evidence option
    okReduction: bool
    okSteps: bool
    isOk: bool }

let checkSteps (checker: CalcChecker<'a>) =
  let okReduction, (stepIndex, reduction) =
    assert (checker.steps.Length <> 0)
    transitiveReduction checker.transitivity checker.steps

  let expandedAndMarkedSteps =
    applyRewritersAndMarkPathToSolution (checker.steps |> Array.map _.step)

  let okSteps =
    expandedAndMarkedSteps
    |> Array.forall (fun expansions -> expansions |> Seq.exists _.expansion.node.path.IsSome)

  let evidence = if okReduction then checker.getEvidence reduction else None

  let isOk = okReduction && okSteps && evidence.IsSome

  { transitiveReduction = stepIndex, reduction
    expandedSteps = expandedAndMarkedSteps
    evidence = evidence
    okReduction = okReduction
    okSteps = okSteps
    isOk = isOk }

type CheckedCalculation =
  { calculation: Calculation
    check: Check }

let check (c: Calculation) =
  result {
    do! if c.steps.Length = 0 then Error EmptyCalculation else Ok()

    let! compiled = compileCalculation c

    return
      { calculation = c
        check = checkSteps compiled }
  }

let axiom id (e: Pred<'a>) : Law = { expr = getTypedExpr e; id = id }
