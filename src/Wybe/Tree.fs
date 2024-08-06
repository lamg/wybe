module Tree

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

let rec roots expr =
  seq {
    yield expr

    match expr with
    | Leaf _ -> ()
    | Branch { children = xs } ->
      for x in xs do
        yield! roots x
  }

let rec mapLeafs (f: 'b -> Tree<'a, 'b>) (t: Tree<'a, 'b>) =
  match t with
  | Branch({ children = xs } as r) ->
    Branch
      { r with
          children = xs |> Seq.map (mapLeafs f) }
  | Leaf x -> f x
