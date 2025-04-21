module Inference

open ExpressionMatch
open StepExpansion
open TypedExpression
open FsToolkit.ErrorHandling
open FSharp.Core

type Law = { expr: TypedExpr; id: string }

type CheckError =
  // expression given for extracting a Leibniz inference rule doesn't match with `x = y ⇒ f.x = f.y`
  | IncompatibleLawWithLeibniz of Law
  // expression given for extracting a transitivity inference rule doesn't match with `x = y ∧ y = z ⇒ x = z`
  | WrongTransitivity of Law
  | EmptyCalculation
  // The RHS in a Leibniz expression `x = y ⇒ f.x = f.y`, has operator `=`, which has to coincide with the operator in a step like
  //   f.x
  // = {}
  //  f.y
  | NoTransitivityBetween of TypedExpr * TypedExpr

type CheckWarning =
  | NoLeibnizLhsHintLawMatch of leibnizLhs: TypedExpr * lawExpr: TypedExpr
  | NoOperatorLeibnizRhsMatch of op: TypedSymbol * TypedExpr

type CheckResult =
  { errors: CheckError list
    warnings: CheckWarning list }

type LeibnizResult =
  { checkResult: CheckResult
    leibniz: Rewriter<TypedSymbol> option }

type LeibnizRule =
  { ``x = y``: TypedExpr
    ``f.x = f.y``: TypedExpr }

  member this.apply(hintOp: TypedSymbol, hintLaw: Law) =
    match true with
    | _ when this.``f.x = f.y``.node = hintOp ->
      let m = matchTree matchSymbol this.``x = y`` hintLaw.expr

      match m with
      | (_, x) :: (_, y) :: _ ->
        { checkResult = { errors = []; warnings = [] }
          leibniz =
            Some
              { lhs = x
                rhs = y
                isNodeMatch = matchSymbol
                id = hintLaw.id } }
      | _ ->
        { checkResult =
            { errors = []
              warnings = [ NoLeibnizLhsHintLawMatch(this.``x = y``, hintLaw.expr) ] }
          leibniz = None }
    | _ ->
      { checkResult =
          { errors = []
            warnings = [ NoOperatorLeibnizRhsMatch(hintOp, this.``f.x = f.y``) ] }
        leibniz = None }

// leibniz: a predicate like x <eq0> y  ↦  f.x <eq1> f.y
// stepOp: equal to <eq1>, for the step to match with f.x <eq1> f.y
// hint: a law that matches with x <eq0> y
// the resulting rule should be able to check a step in the form
//   f.x
// <eq1> { law0 }
//   f.y
// where law0 matches x <eq0> y
let makeLeibnizRule (leibnizLaw: Law) : Result<LeibnizRule, CheckError> =
  match leibnizLaw.expr with
  | { node = { signature = s }
      subtrees = [ ``x = y``; ``f.x = f.y`` ] } when s = boolId ->
    Ok
      { ``x = y`` = ``x = y``
        ``f.x = f.y`` = ``f.x = f.y`` }

  | _ -> Error(IncompatibleLawWithLeibniz leibnizLaw)

type TransitivityResult =
  { checkResult: CheckResult
    resultExpr: TypedExpr option }

type TransitivityRule =
  { ``x = y``: TypedExpr
    ``y = z``: TypedExpr
    ``x <op> z``: TypedSymbol }

  // given two expressions like (x <imp0> y), (y <imp1> z)
  // returns a result expression like x <resultExprOp> z
  member this.reduceExprs(``x = y``: TypedExpr, ``y = z``: TypedExpr) =
    let t0 = matchTree matchSymbol this.``x = y`` ``x = y``
    let t1 = matchTree matchSymbol this.``y = z`` ``y = z``

    match t0, t1 with
    | [ _, x; _, y ], [ _, y'; _, z ] when y = y' ->
      { checkResult = { errors = []; warnings = [] }
        resultExpr =
          Some
            { node = this.``x <op> z``
              subtrees = [ x; z ] } }
    | _ ->
      { checkResult =
          { errors = [ NoTransitivityBetween(``x = y``, ``y = z``) ]
            warnings = [] }
        resultExpr = None }

let makeTransitivityRule (transitivity: Law) : Result<TransitivityRule, CheckError> =
  match transitivity.expr with
  | { subtrees = [ { subtrees = [ { subtrees = [ x; y ] } as t0; { subtrees = [ y'; z ] } as t1 ] }
                   { node = imp2; subtrees = [ x'; z' ] } ] } when x = x' && y = y' && z = z' ->
    { ``x = y`` = t0
      ``y = z`` = t1
      ``x <op> z`` = imp2 }
    |> Ok
  | _ -> WrongTransitivity transitivity |> Error

type CheckableStep =
  { step: Step<TypedSymbol>
    op: TypedSymbol option }

// creates an expression joining consecutive pairs of steps with the operator of the first
// expressions are reduced using one of the applicable transitivity rules
let checkTransitivity (ts: TransitivityRule list) (steps: CheckableStep array) =
  assert (steps.Length > 0)

  let joinedSteps =
    steps
    |> Array.pairwise
    |> Array.map (fun (x, y) ->
      { node = { x.op.Value with signature = boolId }
        subtrees = [ x.step.expr; y.step.expr ] })
  // joinedSteps has the shape: (expr0 op0 expr1)+

  let folder (acc: TransitivityResult) s =
    match acc with
    | { resultExpr = Some exp } ->
      let transitivityResult = ts |> List.map (fun t -> t.reduceExprs (exp, s))

      let errors =
        transitivityResult |> List.collect (fun { checkResult = { errors = es } } -> es)

      let resultExpr = transitivityResult |> List.tryFind (fun r -> r.resultExpr.IsSome)

      match resultExpr with
      | Some r -> r
      | None ->
        { resultExpr = None
          checkResult = { errors = errors; warnings = [] } }
    | _ -> acc

  joinedSteps
  |> Seq.tail
  |> Seq.scan
    folder
    { resultExpr = Some joinedSteps[0]
      checkResult = { warnings = []; errors = [] } }


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

  let impliesDemonstrandum = false

  match transitivityReduction with
  | _ when transitivityReduction = demonstrandum -> Some ReductionEqualTheorem
  | { node = { symbol = Fixed "≡" }
      subtrees = [ x; y ] } when x = demonstrandum && matchesLaw y -> Some(DemonstrandumEqualLaw(x, y))
  | { node = { symbol = Fixed "≡" }
      subtrees = [ x; y ] } when y = demonstrandum && matchesLaw x -> Some(DemonstrandumEqualLaw(y, x))
  | _ when impliesDemonstrandum -> Some(ReductionImpliesDemonstrandum transitivityReduction)
  | { node = { symbol = Fixed "≡"; signature = s }
      subtrees = [ x; y ] } ->
    let symmetric =
      { node = { symbol = Fixed "≡"; signature = s }
        subtrees = [ y; x ] }

    if symmetric = demonstrandum then
      Some ReductionEqualTheorem
    else
      None
  | _ -> None

type StepContext =
  { currentStep: TypedExpr
    nextStep: TypedExpr }

type LawGenerator =
  { id: string
    generator: StepContext -> Law seq seq
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
    transitivity: Law list // laws used to check the transitivity of steps
    contextLaws: Law list // these laws are applied between each step and to the expression resulting of joining the calculation steps
    demonstrandum: Law
    steps: CalcStep array }

type CheckContext =
  { mutable issues: CheckResult list
    rules: LeibnizRule list
    contextLaws: Law list }

  member this.addIssues(issue: CheckResult) =
    match issue with
    | { warnings = []; errors = [] } -> ()
    | _ -> this.issues <- issue :: this.issues

  member this.addIssues(issues: CheckResult list) =
    let xs =
      issues
      |> List.filter (function
        | { warnings = []; errors = [] } -> false
        | _ -> true)

    this.issues <- xs @ this.issues

  member this.leibnizRewriter (op: TypedSymbol) (law: Law) =
    this.rules
    |> List.choose (fun x ->
      let r = x.apply (op, law)
      this.addIssues r.checkResult
      r.leibniz)
    |> List.tryHead


type CompiledCalculation =
  { calculation: Calculation
    transitivity: TransitivityRule list
    steps: CheckableStep array
    getEvidence: TypedExpr -> Evidence option
    checkContext: CheckContext }

let expandGeneratedLaws (ctx: CheckContext) (op: TypedSymbol) (generated: Law seq seq) =
  // list of alternative versions to lawExpr resulting from transforming it with contextLaws
  let alternativesTo op (law: Law) =
    let rewriters = ctx.contextLaws |> List.choose (ctx.leibnizRewriter op)

    rewriters
    |> appyAllRewritersPermutations law.expr
    |> List.concat
    |> Seq.map (fun expr -> { expr = expr; id = law.id })

  let expandWithAlternatives op (hintLaws: Law seq) =
    // for each alternative found creates a sequence with the original laws and the new alternative replaced
    hintLaws
    |> Seq.map (fun l ->
      let alts = alternativesTo op l

      alts
      |> Seq.map (fun alt ->
        hintLaws
        |> Seq.map (function
          | hl when hl = l -> alt
          | hl -> hl)))

  let rss =
    generated
    |> Seq.collect (expandWithAlternatives op)
    |> Seq.concat
    |> Seq.append generated

  rss


let makeCheckableSteps (ctx: CheckContext) (steps: CalcStep array) =
  let makeCheckable (current: CalcStep, nextExpr: TypedExpr option) =
    match current.hint with
    | Hint.End ->
      { op = None
        step =
          { expr = current.expr
            rewriters = []
            limits =
              { maxAlternatives = 0
                maxAlternativeLength = 0 } } }
    | Hint.Law l ->
      let generatedLaws =
        l.lawGenerator.generator
          { currentStep = current.expr
            nextStep = nextExpr |> Option.get }

      let rewriters =
        generatedLaws
        |> expandGeneratedLaws ctx l.op
        |> Seq.mapi (fun i xs ->
          xs
          |> Seq.choose (fun x ->
            let s = ctx.leibnizRewriter l.op x
            s))

      { op = Some l.op
        step =
          { expr = current.expr
            rewriters = rewriters
            limits =
              { maxAlternatives = 10
                maxAlternativeLength = 10 } } }

  let successors =
    Array.append (steps |> Array.tail |> Array.map (_.expr >> Some)) [| None |]

  let consecutivePairs = Array.zip steps successors
  consecutivePairs |> Array.map makeCheckable

let compileCalculation (c: Calculation) =
  result {
    let! leibniz = c.leibniz |> List.map makeLeibnizRule |> List.sequenceResultM

    let ctx =
      { issues = []
        contextLaws = c.contextLaws
        rules = leibniz }

    let! transitivity = c.transitivity |> List.map makeTransitivityRule |> List.sequenceResultM

    let getEvidence reduction =
      provesTheorem c.contextLaws c.demonstrandum reduction

    let steps = makeCheckableSteps ctx c.steps

    return
      { calculation = c
        transitivity = transitivity
        steps = steps
        getEvidence = getEvidence
        checkContext = ctx }
  }


type Check =
  { transitivityReduction: list<TransitivityResult>
    expandedSteps: StepExpansion<TypedSymbol> array
    evidence: Evidence option
    okReduction: bool
    okSteps: bool
    isOk: bool }

let checkSteps (checker: CompiledCalculation) =
  assert (checker.steps.Length <> 0)
  let reduction = checkTransitivity checker.transitivity checker.steps |> Seq.toList
  assert (reduction.Length = checker.steps.Length - 1)
  let transitivityResult = reduction |> List.last

  let expandedAndMarkedSteps =
    applyRewritersAndMarkPathToSolution (checker.steps |> Array.map _.step)

  let okSteps =
    expandedAndMarkedSteps
    |> Array.forall (fun expansions -> expansions |> Seq.exists _.expansion.node.path.IsSome)

  let evidence = transitivityResult.resultExpr |> Option.bind checker.getEvidence

  let isOk = okSteps && evidence.IsSome

  { transitivityReduction = reduction
    expandedSteps = expandedAndMarkedSteps
    evidence = evidence
    okReduction = transitivityResult.resultExpr.IsSome
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
