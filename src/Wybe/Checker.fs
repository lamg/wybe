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

// matches two roots if they have the same operator or, in case of an identifier as matcher and a root as target,
// they match if their result types are the same
let matchByType (matcher: TypedExpr) (target: TypedExpr) =
  let rec loop (acc: Binding list) (matcher: TypedExpr, target: TypedExpr) =
    let sameResultType x y = x = y

    match matcher, target with
    | Branch x, Branch y when x.value = y.value && Seq.length x.children = Seq.length y.children ->
      Seq.zip x.children y.children |> Seq.fold loop acc
    | Leaf(v, r0), Branch { value = TypedOperator(_, r1) } when sameResultType r0 r1 -> (v, target) :: acc
    | Leaf(x, r0), Leaf(_, r1) when sameResultType r0 r1 -> (x, target) :: acc
    | _ -> acc

  loop [] (matcher, target) |> List.rev


// for each free identifier x, all expressions e bound to x are equal
// otherwise is a conflict
let splitFreeConflicts (free: TypedVar list) (freeBindings: Binding list) =
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

// given a list of free variables says if there's a match or not between the matcher and the target
// expressions. For example `a ∧ a` matches `(x ≡ y) ∧ (x ≡ y)` with a ≔ x ≡ y
let findBindings (matcher: Matcher) (target: TypedExpr) =
  let bindings = matchByType matcher.expr target

  let freeBindings, nonFreeBindings = splitMatched matcher.freeVars bindings

  let freeMatch = splitFreeConflicts matcher.freeVars freeBindings
  let nonFreeMatch = splitNonFreeConflicts nonFreeBindings

  { free = freeMatch
    nonFree = nonFreeMatch }

let allRootsFreeBindings (matcher: Matcher) (expr: TypedExpr) =
  expr
  |> roots
  |> Seq.choose (fun r ->
    match findBindings matcher r with
    | { free = {valid = []} } -> None
    | { free = { valid = xs; conflicts = [] }
        nonFree = { conflicts = [] } } -> Some xs
    | _ -> None)

let rewriteWith (expr: TypedExpr) (bindings: Binding list) : TypedExpr =
  let rewriteLeaf (x: TypedVar) =
    let id = fst x

    match bindings |> List.tryFind (fun (v, _) -> v = id) with
    | Some(_, e) -> e
    | _ -> Leaf x

  mapLeafs rewriteLeaf expr

type Transformer =
  { freeVars: TypedVar list
    lhs: TypedExpr
    rhs: TypedExpr }

let transformations (t: Transformer) (target: TypedExpr) =
  target
  |> allRootsFreeBindings { freeVars = t.freeVars; expr = t.lhs }
  |> Seq.map (rewriteWith t.rhs)

// the children of target are segmented the following way
// 0: apply each transformer once
// 1: apply each transformer twice
// 2: apply each transformer twice, then foreach ...
// TODO create an abstraction for generating transformations
let transformationTree (ts: Transformer list) (target: TypedExpr) = []
