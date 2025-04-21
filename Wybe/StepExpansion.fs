module StepExpansion

open ExpressionMatch

// given a list of transformers and a starting value, generates a tree
// by successively applying transformers to each node in a level until
// there are no more transformers
let rec expand (builder: TreeBuilder<'t, 'a, 'b>) (start: 'b) (transformers: 't list) =
  match transformers with
  | t :: ts ->
    { node = start
      subtrees =
        builder.build t (builder.extract start)
        |> List.map (fun n -> expand builder n ts) }
  | [] -> { node = start; subtrees = [] }

type Mark<'a> = { path: int option; value: 'a }

let mark (f: 'a -> bool) (t: Tree<'a>) =
  let rec loop (t: Tree<'a>, current: int) =
    let n, current =
      if f t.node then
        Some current, current + 1
      else
        None, current

    let node = { value = t.node; path = n }

    let newSubtrees, newCurrent =
      t.subtrees
      |> Seq.fold
        (fun (subs, curr) s ->
          let nt, newCurr = loop (s, curr)
          nt :: subs, newCurr)
        ([], current)

    { node =
        if newCurrent <> current then
          { node with path = Some current }
        else
          node
      subtrees = newSubtrees |> List.rev },
    newCurrent

  loop (t, 0) |> fst

type MarkedTree<'a when 'a: equality> = Tree<Mark<'a>>

let expandAndMarkPathToSolution
  (target: Tree<'a>, expected: Tree<'a>)
  (rewriters: Rewriter<'a> list)
  : MarkedTree<Expression<'a>> =
  expand { build = yieldRewrites; extract = id } target rewriters
  |> mark ((=) expected)

type ExprExpansion<'a when 'a: equality> =
  { rewriters: Rewriter<'a> list
    expansion: MarkedTree<Expression<'a>> }

type GenerationLimits =
  { maxAlternativeLength: int
    maxAlternatives: int }

let mapExpansions (limits: GenerationLimits) (prev: Expression<'a>) (curr: Expression<'a>) (xss: Rewriter<'a> seq seq) =
  xss
  |> Seq.truncate limits.maxAlternatives
  |> Seq.mapi (fun i xs ->
    let xs = xs |> Seq.truncate limits.maxAlternativeLength |> Seq.toList
    let expansion = expandAndMarkPathToSolution (prev, curr) xs

    { rewriters = xs
      expansion = expansion })

// each step contains a list of alternative rewriters, one of them could validate the
// transition from one step to the next in a calculation
// an alternative (a list of rewriters) take the previous step expression and creates a tree of expressions
// with the root on it, if one of the branches has the next step expression, then the step is valid
type Step<'a when 'a: equality> =
  { expr: Expression<'a>
    rewriters: Rewriter<'a> seq seq
    limits: GenerationLimits }

type StepExpansion<'a when 'a: equality> = ExprExpansion<'a> seq

let applyRewritersAndMarkPathToSolution (steps: Step<'a> array) : StepExpansion<'a> array =
  steps
  |> Array.pairwise
  |> Array.map (fun (x, y) -> mapExpansions x.limits x.expr y.expr x.rewriters)


// applies rewriters to the expression, yielding all intermediate expressions excluding the original
let applyRewriters (exp: Expression<'a>) (rewriters: Rewriter<'a> list) =
  let tree = expand { build = yieldRewrites; extract = id } exp rewriters

  let rec treeToList (t: Tree<Expression<'a>>) =
    [ yield t.node

      for x in t.subtrees do
        yield! treeToList x ]

  let lawSet = tree |> treeToList |> Set.ofList

  let withoutOriginal = lawSet - Set [ exp ]
  withoutOriginal |> Set.toList

let rec permutations list =
  match list with
  | [] -> [ [] ]
  | _ ->
    list
    |> List.collect (fun x ->
      let sublist = List.filter ((<>) x) list
      permutations sublist |> List.map (fun perm -> x :: perm))

// applies to all permutations of rewriters to the expression
let appyAllRewritersPermutations (exp: Expression<'a>) (rewriters: Rewriter<'a> list) =
  let xss = [ 0 .. rewriters.Length - 1 ] |> permutations

  xss
  |> List.map (fun xs -> rewriters |> List.permute (fun n -> xs[n]) |> applyRewriters exp)
