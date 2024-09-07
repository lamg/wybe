module Checker

open Tree

type ResultType = ResultType of string
type Identifier = Identifier of string
type TypedVar = Identifier * ResultType
type TypedOperator = TypedOperator of string * ResultType

type TypedExpr = Tree<TypedOperator, TypedVar>
type Binding = Identifier * TypedExpr

type Matcher =
  { freeVars: TypedVar list
    expr: TypedExpr }

type MatchResult =
  { valid: Binding list
    conflicts: Binding list }

type FreeNonFreeResult =
  { free: MatchResult
    nonFree: MatchResult }

let typedExprStringer =
  { new StringerContext<TypedOperator, TypedVar> with
      member _.sameLevel (TypedOperator(op0, _)) (TypedOperator(op1, _)) = op0 = op1
      member _.branchToString(TypedOperator(op, _)) = op
      member _.leafToString((Identifier i, _)) = i }


let exprToString (t: TypedExpr) = treeToString typedExprStringer t

// matches two roots if they have the same operator or, in case of an identifier as matcher and a root as target,
// they match if their result types are the same
let matchByType (matcher: TypedExpr) (target: TypedExpr) =
  let rec loop (acc: Binding list) (matcher: TypedExpr, target: TypedExpr) =
    let sameResultType x y = x = y

    match matcher, target with
    | Branch x, Branch y when x.value = y.value && x.children.Length = y.children.Length ->
      Seq.zip x.children y.children |> Seq.fold loop acc |> Seq.toList
    | Leaf(v, r0), Branch { value = TypedOperator(_, r1) } when sameResultType r0 r1 -> (v, target) :: acc
    | Leaf(x, r0), Leaf(_, r1) when sameResultType r0 r1 -> (x, target) :: acc
    | _ -> acc

  loop [] (matcher, target) |> List.rev


// for each free identifier x, all expressions e bound to x are equal
// otherwise is a conflict
let splitFreeConflicts (freeBindings: Binding list) =
  let valid, conflicts =
    freeBindings
    |> List.groupBy fst
    |> List.partition (fun (_, allBoundToSameId) ->
      let allEqual =
        function
        | [] -> true
        | e :: rs -> rs |> List.forall (fun r -> e = r)

      allBoundToSameId |> allEqual)

  let getBindings = List.map snd >> List.concat

  { valid = getBindings valid
    conflicts = getBindings conflicts }

// each non-free identifier is bound to a variable with an identifier equal to itself
// otherwise is a conflict
let splitNonFreeConflicts (nonFreeBindings: Binding list) =
  let valid, conflicts =
    nonFreeBindings
    |> List.partition (function
      | x, Leaf(y, _) -> x = y
      | _ -> false)

  { valid = valid; conflicts = conflicts }

// splits the matched bindings between free and non-free identifiers
let splitMatched (free: TypedVar list) (matchedTypes: Binding list) =
  matchedTypes
  |> List.partition (fun (x, _) -> free |> List.exists (fun (y, _) -> x = y))

// given a matcher (a pair of free variables and expression) finds matches and conflicts in the
// root of the target expression
// For example `a ∧ a` matches `(x ≡ y) ∧ (x ≡ y)` with a ≔ x ≡ y,
// `a ∧ a` matches `x ∧ (x ≡ y) ∧ (x ≡ y)` with a conflict between a ≔ x and a ≔ x ≡ y
let bindByTypeAtRoot (matcher: Matcher) (root: TypedExpr) =
  let bindings = matchByType matcher.expr root

  let freeBindings, nonFreeBindings = splitMatched matcher.freeVars bindings

  let freeMatch = splitFreeConflicts freeBindings
  let nonFreeMatch = splitNonFreeConflicts nonFreeBindings

  { free = freeMatch
    nonFree = nonFreeMatch }

// rewrite an expression by changing its leafs by the associated expression in the
// binding list
let rewriteWith (expr: TypedExpr) (bindings: Binding list) : TypedExpr =
  let rewriteLeaf (x: TypedVar) =
    let id = fst x

    match bindings |> List.tryFind (fun (v, _) -> v = id) with
    | Some(_, e) -> e
    | _ -> Leaf x

  mapLeafs rewriteLeaf expr

type Transformer =
  { name: string
    freeVars: TypedVar list
    lhs: TypedExpr
    rhs: TypedExpr }

let printBindings (xs: Binding list) =
  xs
  |> List.map (fun (Identifier x, expr) -> $"{x} ≔ {treeToString typedExprStringer expr}")


let tryBindRoot (t: Transformer) (target: TypedExpr) =
  match bindByTypeAtRoot { freeVars = t.freeVars; expr = t.lhs } target with
  | { free = { valid = [] } } -> None
  | { free = { valid = bindings; conflicts = [] }
      nonFree = { conflicts = [] } } ->

    Some(bindings, rewriteWith t.rhs bindings)
  | _ -> None

type BindingsTR =
  { bindings: Binding list
    transformResult: TypedExpr }

// returns a sequence of trees
// each one has a list of bindings if one of its subtrees was transformed
// in the sequence each tree has a single subtree transformation
let transformations (target: TypedExpr) (t: Transformer) =
  roots target
  |> Seq.choose (fun (r, path) ->
    match tryBindRoot t r with
    | Some(bs, v) ->
      Some
        { bindings = bs
          transformResult = replaceAt target (v, path) }
    | _ -> None)

let transformationTree (target: TypedExpr) (ts: Transformer list) =
  let rec loop rs t =
    match rs with
    | [] -> Leaf t
    | x :: xs ->
      let ns = transformations t.transformResult x |> Seq.toArray

      Branch
        { value = (t, x)
          children = ns |> Array.map (loop xs) }

  loop
    ts
    { bindings = []
      transformResult = target }

let bindingsTrStringer =
  let format b =
    let bs = printBindings b.bindings
    let e = exprToString b.transformResult
    $"{e} {bs}"

  { new PrinterContext<BindingsTR * Transformer, BindingsTR> with
      member _.leafToString x = format x
      member _.branchToString((x, t)) = $"{format x} {t.name}" }

type TransformPath = Path<BindingsTR * Transformer, BindingsTR>

// applies the transformers to target generating a tree of transformations
// then finds the expected expression in that tree
// finally returning all paths of expressions and transformers that lead to it
let checkExpression (target: TypedExpr, expected: TypedExpr) (ts: Transformer list) : TransformPath list =
  let t = transformationTree target ts

  let _, paths =
    findValuePaths t (function
      | Left(bindings, _) -> bindings.transformResult = expected
      | Right bindings -> bindings.transformResult = expected)
    |> Seq.toList
    |> List.unzip

  paths |> List.map (collectPath t)

let printTransformationChain (xss: TransformPath list) =
  let eitherToStr =
    function
    | Left x -> bindingsTrStringer.branchToString x
    | Right x -> bindingsTrStringer.leafToString x

  xss
  |> List.map (List.map eitherToStr >> String.concat "  -->  ")
  |> String.concat "\n"
