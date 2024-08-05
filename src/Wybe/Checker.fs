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

type ResultType = ResultType of string
type Identifier = Identifier of string
type TypedVar = Identifier * ResultType
type TypedOperator = TypedOperator of string * ResultType

type TypedExpr = Tree<TypedOperator, TypedVar>
type Binding = Identifier * TypedExpr

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


// for each free var x, all expressions e bound to x are equal
let okFree free freeBindings =
  free
  |> List.forall (fun (x, _) ->
    freeBindings
    |> List.choose (function
      | y, e when x = y -> Some e
      | _ -> None)
    |> function
      | [] -> false
      | e :: rs -> rs |> List.forall (fun r -> e = r))

// each non-free identifier is bound to an identifier equal to itself
let okNonFree nonFreeBindings =
  nonFreeBindings
  |> List.forall (function
    | x, Leaf(y, _) -> x = y
    | _ -> false)

let splitMatched free matchedTypes =
  matchedTypes
  |> List.partition (fun (x, _) -> free |> List.exists (fun (y, _) -> x = y))

let matchFree (free: TypedVar list) (matcher: TypedExpr) (target: TypedExpr) =
  let matchedTypes = matchByType matcher target

  let freeBindings, nonFreeBindings = splitMatched free matchedTypes

  okFree free freeBindings && okNonFree nonFreeBindings
