module Tree

open FSharpPlus

type Branch<'a, 'b> =
  { value: 'a
    children: Tree<'a, 'b> array }

and Tree<'a, 'b> =
  | Branch of Branch<'a, 'b>
  | Leaf of 'b

let roots expr =
  let rec loop t path =
    seq {
      yield t, path

      match t with
      | Leaf _ -> ()
      | Branch { children = xs } -> yield! xs |> Seq.mapi (fun i x -> loop x (path @ [ i ])) |> Seq.concat
    }

  loop expr []

let rec replaceAt root (t, path) =
  match path with
  | [] -> t
  | x :: xs ->
    match root with
    | Branch { value = a; children = ys } ->
      let newAtX = replaceAt (ys |> Seq.item x) (t, xs)

      Branch
        { value = a
          children = Array.updateAt x newAtX ys }

    | _ -> failwith "invalid path"

let rec mapLeafs (f: 'b -> Tree<'a, 'b>) (t: Tree<'a, 'b>) =
  match t with
  | Branch({ children = xs } as r) ->
    Branch
      { r with
          children = xs |> Array.map (mapLeafs f) }
  | Leaf x -> f x

type ValueLength<'a> = { value: 'a; length: int }

type Diff<'a, 'b> =
  | DiffBranch of ValueLength<'a> * ValueLength<'a>
  | DiffLeaf of 'b * 'b
  | BranchLeaf of 'a * 'b
  | LeafBranch of 'b * 'a

let rec diffTrees (x: Tree<'a, 'b>, y: Tree<'a, 'b>) =
  match x, y with
  | Branch { value = m; children = xs }, Branch { value = n; children = ys } when m = n && Seq.length xs = Seq.length ys ->
    Seq.zip xs ys |> Seq.choose diffTrees |> Seq.tryHead
  | Branch { value = m; children = xs }, Branch { value = n; children = ys } ->
    let l = { value = m; length = Seq.length xs }
    let r = { value = n; length = Seq.length ys }

    Some(DiffBranch(l, r))
  | Leaf m, Leaf n when m = n -> None
  | Leaf m, Leaf n -> Some(DiffLeaf(m, n))
  | Branch { value = m }, Leaf n -> Some(BranchLeaf(m, n))
  | Leaf m, Branch { value = n } -> Some(LeafBranch(m, n))

type SameLeveler<'a> =
  abstract member sameLevel: 'a -> 'a -> bool

type PrinterContext<'a, 'b> =
  abstract member branchToString: 'a -> string
  abstract member leafToString: 'b -> string

type StringerContext<'a, 'b> =
  inherit SameLeveler<'a>
  inherit PrinterContext<'a, 'b>

// flattens a tree into a string representation
let treeToString (ctx: StringerContext<'a, 'b>) (t: Tree<'a, 'b>) =
  let rec loop (t: Tree<'a, 'b>) =
    match t with
    | Branch { value = v; children = xs } ->
      let rs =
        xs
        |> Seq.map (fun x ->
          let subString = loop x

          match x with
          | Branch { value = w } when ctx.sameLevel v w -> subString
          | Branch _ -> $"({subString})"
          | Leaf _ -> subString)

      rs |> String.concat $" {ctx.branchToString v} "

    | Leaf v -> ctx.leafToString v

  loop t

// creates a string that represents the tree structure
let printTree (ctx: PrinterContext<'a, 'b>) (t: Tree<'a, 'b>) =
  let connectIndent (isLast: bool) (child: string, grandChild: string list) =
    let childConn, colConn = if isLast then "└── ", "   " else "├── ", "│   "
    let connected = childConn + child
    let indented = grandChild |> List.map (fun x -> colConn + x)
    connected :: indented

  let rec treeToLines t =
    match t with
    | Branch { value = v; children = xs } ->
      let l = Seq.length xs

      let root = ctx.branchToString v

      let children =
        xs
        |> Seq.mapi (fun i c -> treeToLines c |> connectIndent (i = l - 1))
        |> Seq.concat
        |> Seq.toList

      (root, children)
    | Leaf v -> ctx.leafToString v, []

  let r, chl = treeToLines t
  r :: chl |> String.concat "\n"


type Either<'a, 'b> =
  | Left of 'a
  | Right of 'b

let findValuePaths (t: Tree<'a, 'b>) (ok: Either<'a, 'b> -> bool) =
  t
  |> roots
  |> Seq.choose (function
    | (Branch { value = a }, path) when ok (Left a) -> Some(Left a, path)
    | (Leaf a, path) when ok (Right a) -> Some(Right a, path)
    | _ -> None)

type Path<'a, 'b> = Either<'a, 'b> list

let collectPath (t: Tree<'a, 'b>) (path: list<int>) : Path<'a, 'b> =
  let treeValue t =
    match t with
    | Branch b -> Left b.value, b.children
    | Leaf v -> Right v, [||]

  let v, chl = treeValue t

  path
  |> List.fold
    (fun (vs, children) i ->
      let v, chl = children |> Seq.item i |> treeValue
      v :: vs, chl)
    ([ v ], chl)
  |> fst
  |> List.rev
