module Inspect.Formatters

open Inference
open TypedExpression
open ExpressionMatch
open StepExpansion
open ColorMessages
open FSharpPlus

let indentLine n line = String.replicate n " " + line

let printHint =
  function
  | Hint.End -> "▢"
  | Hint.Law h -> $"{h.op.symbol} " + "{ " + h.lawGenerator.id + " }"

let printCalculation (c: Calculation) =
  let header = info "demonstrandum" (c.demonstrandum.expr |> printTypedExpr)

  c.steps
  |> Array.collect (fun x -> [| $"  {printTypedExpr x.expr}"; printHint x.hint |])
  |> Array.append [| header |]

let printTree (f: 'a -> string) (t: Tree<'a>) =
  let connectIndent (isLast: bool) (child: string, grandChild: string list) =
    let childConn, colConn = if isLast then "└── ", "   " else "├── ", "│   "
    let connected = childConn + child
    let indented = grandChild |> List.map (fun x -> colConn + x)
    connected :: indented

  let rec treeToLines t =
    let l = Seq.length t.subtrees

    let root = f t.node

    let children =
      t.subtrees
      |> Seq.mapi (fun i c -> treeToLines c |> connectIndent (i = l - 1))
      |> Seq.concat
      |> Seq.toList

    root, children


  let r, chl = treeToLines t
  r :: chl |> List.toArray

let printExpansion (m: MarkedTree<TypedExpr>) =
  let printTreeValue x =
    let pathMarker =
      match x.path with
      | Some i -> $"✅{i}"
      | None -> "❌"

    $"{printTypedExpr x.value} {pathMarker}"

  printTree printTreeValue m

let printRewriters (xs: Rewriter<TypedSymbol> seq) =
  xs
  |> Seq.map (fun r -> $"{printTypedExpr r.lhs} ↦ {printTypedExpr r.rhs}")
  |> Seq.toArray

let prepend (xs: 'a array) (x: 'a) = Array.append [| x |] xs

let formatExpansion i m =
  info $"expansion_{i}" "" |> prepend (printExpansion m.expansion)

let expansionToStrList xs =
  xs |> Seq.mapi formatExpansion |> Seq.toArray |> Array.concat

let formatRewrite (i: int) (m: ExprExpansion<TypedSymbol>) =
  let rws = printRewriters m.rewriters
  info $"rewriter_{i}" "" |> prepend rws

let rewritersToStrList (xs: StepExpansion.StepExpansion<TypedSymbol>) =
  xs |> Seq.mapi formatRewrite |> Seq.toArray |> Array.concat

let formatAlternative (i: int) (m: ExprExpansion<TypedSymbol>) =
  let exp = info "expansion" "" |> prepend (printExpansion m.expansion)
  let rw = info "rewriter" "" |> prepend (printRewriters m.rewriters)
  let body = Array.append rw exp |> Array.map (indentLine 2)
  info $"alt_{i}" "" |> prepend body

let alternativesToStrList (xs: ExprExpansion<TypedSymbol> seq) =
  xs |> Seq.mapi formatAlternative |> Seq.toArray |> Array.concat

let successfulAlternativesToStrList (xs: ExprExpansion<TypedSymbol> seq) =
  let formatSuccessful (i: int) (m: ExprExpansion<TypedSymbol>) =
    if m.expansion.node.path.IsSome then
      formatAlternative i m |> Some
    else
      None

  xs |> Seq.choosei formatSuccessful |> Seq.toArray |> Array.concat
