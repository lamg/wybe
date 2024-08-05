module Checker

type Branch<'a, 'b> =
  { value: 'a
    children: Tree<'a, 'b> seq }

and Tree<'a, 'b> =
  | Branch of Branch<'a, 'b>
  | Leaf of 'b

let rec lazyTree (f: 'a -> 'a seq) (value: 'a) =
  let xs = f value

  if xs = Seq.empty then
    Leaf value
  else
    Branch
      { value = value
        children = xs |> Seq.map (lazyTree f) }

// how to find type matches

type ResultType = ResultType of string
type Identifier = Identifier of string
type TypedVar = Identifier * ResultType
type TypedOperator = TypedOperator of string * ResultType

type TypedExpr = Tree<TypedOperator, TypedVar>

type Bound = { variable: TypedVar; expr: TypedExpr }

type MatchResult =
  { free: TypedVar list
    bounds: Bound list }

let rec matchFree (acc: MatchResult) (matcher: TypedExpr, target: TypedExpr) =
  let sameResultType x y = x = y

  let removeFree v =
    let rs = acc.free |> List.filter (fun x -> x <> v)
    rs.Length <> acc.free.Length, rs

  let addBound v =
    let ok =
      acc.bounds
      |> List.forall (function
        | { variable = u; expr = e } when v.variable = u -> v.expr = e
        | _ -> true)

    ok, v :: acc.bounds

  let newMatchResult var =
    match removeFree var with
    | true, newFree ->
      match addBound { variable = var; expr = target } with
      | true, newBounds -> { free = newFree; bounds = newBounds }
      | false, _ -> acc
    | false, _ -> acc

  match matcher, target with
  | Branch x, Branch y when x.value = y.value && Seq.length x.children = Seq.length y.children ->
    x.children |> Seq.zip y.children |> Seq.fold matchFree acc
  | Leaf(v, r0), Branch { value = TypedOperator(_, r1) } when sameResultType r0 r1 -> newMatchResult (v,r0)
  | Leaf(x, r0), Leaf(_, r1) when sameResultType r0 r1 -> newMatchResult (x,r0)
  | _ -> acc
