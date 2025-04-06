module ExpressionMatch

open FSharpPlus

type Tree<'a when 'a: equality> = { node: 'a; subtrees: Tree<'a> list }

type Expression<'a when 'a: equality> = Tree<'a>

// Implementing basic Leibniz expression rewrite:
// given an equality LHS = RHS
// match LHS with an expression at its root (the target)
// with the found matches rewrite RHS and return the resulting expression
// for each subtree in the target expression return a subtree rewrite if possible

// node matcher: says if there's a match between two tree nodes match
// where the left is the matcher and the right is the target
type Matcher<'a> = 'a -> 'a -> bool

let rec matchTree (matcher: Matcher<'a>) (pattern: Tree<'a>) (target: Tree<'a>) =
  let rec loop acc pattern target =
    let patSubtrees = Seq.length pattern.subtrees

    let leafOrSameLength =
      pattern.subtrees = [] || pattern.subtrees.Length = target.subtrees.Length

    let isMatch = leafOrSameLength && matcher pattern.node target.node

    let hasConflict =
      isMatch && List.exists (fun (m, t) -> m = pattern.node && t <> target) acc

    match true with
    | _ when hasConflict -> None
    | _ when isMatch && patSubtrees = 0 -> Some((pattern.node, target) :: acc)

    | _ when isMatch ->
      target.subtrees
      |> Seq.zip pattern.subtrees
      |> Seq.fold
        (function
        | Some acc -> uncurry (loop acc)
        | None -> fun _ -> None)
        (Some acc)
    | _ -> None

  loop [] pattern target |> Option.map List.rev |> Option.defaultValue []

let rec rewrite (matches: ('a * Tree<'a>) list) (rhs: Tree<'a>) =
  let r = matches |> List.tryFind (fun (n, _) -> n = rhs.node)

  match r with
  | Some(_, t) when rhs.subtrees = [] -> t
  | _ ->
    { rhs with
        subtrees = rhs.subtrees |> List.map (rewrite matches) }

type Rewriter<'a when 'a: equality> =
  { isNodeMatch: 'a -> 'a -> bool
    lhs: Tree<'a>
    rhs: Tree<'a>
    id: string }

let rewriteTree (r: Rewriter<'a>) (target: Tree<'a>) =
  match matchTree r.isNodeMatch r.lhs target with
  | [] -> None
  | matches -> Some(rewrite matches r.rhs)

// for each found match creates a tree rewriting that match with the rest of the original
// tree untouched
let rec yieldRewrites (r: Rewriter<'a>) (target: Tree<'a>) =
  [ match rewriteTree r target with
    | Some r -> yield r
    | None -> ()

    let xss =
      target.subtrees
      |> List.mapi (fun i x -> yieldRewrites r x |> List.map (fun x -> List.updateAt i x target.subtrees))
      |> List.concat

    yield! xss |> List.map (fun xs -> { target with subtrees = xs }) ]

type TreeBuilder<'t, 'a, 'b> =
  { build: 't -> 'a -> 'b list
    extract: 'b -> 'a }
