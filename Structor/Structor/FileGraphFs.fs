module Structor.FileGraphFs

open System
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Text
open FSharp.Compiler.Syntax
open QuikGraph
open QuikGraph.Graphviz
open QuikGraph.Graphviz.Dot


let getUntypedTree (file, input) =
  let checker = FSharpChecker.Create()

  let projOptions, diagnostics =
    checker.GetProjectOptionsFromScript(file, input, assumeDotNetFramework = false)
    |> Async.RunSynchronously

  let parsingOptions, _errors =
    checker.GetParsingOptionsFromProjectOptions projOptions

  let parseFileResults =
    checker.ParseFile(file, input, parsingOptions) |> Async.RunSynchronously

  parseFileResults.ParseTree

let rec visitPattern pat =
  match pat with
  | SynPat.LongIdent(longDotId = SynLongIdent(id = ident)) ->
    let names = String.concat "." [ for i in ident -> i.idText ]
    names
  | SynPat.Named(SynIdent(ident, _), _, _, _) -> ident.idText
  | _ -> failwith $"expecting something, got {pat}"

let rec visitExpression e =
  seq {
    match e with
    | SynExpr.IfThenElse(ifExpr = cond; thenExpr = trueBranch; elseExpr = falseBranchOpt) ->
      yield! visitExpression cond
      yield! visitExpression trueBranch

      match falseBranchOpt with
      | Some e -> yield! visitExpression e
      | _ -> ()
    | SynExpr.ComputationExpr(_, expr, _) -> yield! visitExpression expr
    | SynExpr.LetOrUse(_, _, bindings, body, _, _) ->
      for binding in bindings do
        let SynBinding(headPat = pat; expr = init) = binding
        yield visitPattern pat
        yield! visitExpression init
        yield! visitExpression body
    | SynExpr.Ident ident -> yield ident.idText
    | SynExpr.LongIdent(_, synLongIdent, _, _) -> yield synLongIdent.LongIdent |> List.map _.idText |> String.concat "."
    | SynExpr.App(_, _, funcExpr, argExpr, _) ->
      yield! visitExpression funcExpr
      yield! visitExpression argExpr
    | SynExpr.New(_, _, synExpr, _) ->
      // printfn $"targetType {targetType}"
      yield! visitExpression synExpr
    | SynExpr.While(_, whileExpr, synExpr, _) ->
      yield! visitExpression whileExpr
      yield! visitExpression synExpr
    | SynExpr.Match(_, synExpr, _, _, _) -> yield! visitExpression synExpr
    | SynExpr.ArrayOrListComputed(_, synExpr, _) -> yield! visitExpression synExpr
    | SynExpr.Sequential(_, _, synExpr, expr2, _, _) ->
      yield! visitExpression synExpr
      yield! visitExpression expr2
    | SynExpr.LetOrUseBang(_, _, _, pat, rhs, _, body, _, _) ->
      yield visitPattern pat
      yield! visitExpression rhs
      yield! visitExpression body
    | SynExpr.TryWith(tryExpr, _, _, _, _, _) -> yield! visitExpression tryExpr
    | SynExpr.YieldOrReturn(_, synExpr, _, _) -> yield! visitExpression synExpr
    | e ->
      //printfn $"expr {e}"
      ()
  }


let visitDeclarations
  (graph: AdjacencyGraph<string, Edge<string>>)
  (exclude: List<string>)
  (includeVertices: List<string>)
  decls
  =
  let locals =
    decls
    |> List.collect (function
      | SynModuleDecl.Let(_, bindings, _) ->
        bindings
        |> List.map (fun b ->
          let SynBinding(headPat = pat) = b
          visitPattern pat)

      | _ -> [])

  let toInclude = locals @ includeVertices

  for declaration in decls do
    match declaration with
    | SynModuleDecl.Let(_, bindings, _) ->

      bindings
      |> List.iter (fun b ->
        let SynBinding(headPat = pat; expr = body) = b
        let name = visitPattern pat
        let calls = visitExpression body

        calls
        |> Seq.filter (fun c -> exclude |> List.exists c.StartsWith |> not && toInclude |> List.contains c)
        |> Seq.iter (fun c -> graph.AddVerticesAndEdge(Edge(name, c)) |> ignore))

    | SynModuleDecl.Open(SynOpenDeclTarget.ModuleOrNamespace(SynLongIdent(idents, _, _), _), _) ->
      printfn $"open {idents}"
    | _ -> ()



let visitModulesAndNamespaces modulesOrNss =
  let graph = AdjacencyGraph<string, Edge<string>>()

  for moduleOrNs in modulesOrNss do
    let SynModuleOrNamespace(longId = lid; decls = decls) = moduleOrNs
    printfn $"Namespace or module: %A{lid}"
    visitDeclarations graph [ "List."; "op_PipeRight"; "Option."; "Result."; "Seq." ] [] decls

  graph

let exportToGraphviz (graph: AdjacencyGraph<string, Edge<string>>) =
  let random = Random()
  let existingColors = []

  let colorDistance (color1: GraphvizColor) (color2: GraphvizColor) =
    let rMean = (int color1.R + int color2.R) / 2
    let r = int color1.R - int color2.R
    let g = int color1.G - int color2.G
    let b = int color1.B - int color2.B
    let lastTerm = (767 - rMean) * b * b >>> 8
    let gg4 = 4 * g * g
    let firstTerm = (512 + rMean) * r * r >>> 8
    Math.Sqrt(float (firstTerm + gg4 + lastTerm))

  let randomColor () =
    let rec generateColor () =
      let r = random.Next(0, 128) |> byte
      let g = random.Next(0, 128) |> byte
      let b = random.Next(0, 128) |> byte
      let newColor = GraphvizColor(255uy, r, g, b)

      if
        existingColors
        |> List.exists (fun color -> colorDistance color newColor < 100.0)
      then
        generateColor ()
      else
        newColor

    generateColor ()

  let graphviz = GraphvizAlgorithm<string, Edge<string>>(graph)

  graphviz.FormatVertex.Add(fun args ->
    args.VertexFormat.Label <- args.Vertex
    args.VertexFormat.FillColor <- randomColor ())

  graphviz.CommonVertexFormat.Style <- GraphvizVertexStyle.Filled
  graphviz.CommonVertexFormat.Shape <- GraphvizVertexShape.Box
  graphviz.CommonVertexFormat.FontColor <- GraphvizColor.WhiteSmoke
  graphviz.CommonEdgeFormat.Style <- GraphvizEdgeStyle.Solid
  graphviz.CommonEdgeFormat.PenWidth <- 1.5
  graphviz.CommonEdgeFormat.StrokeColor <- GraphvizColor.LightGray
  graphviz.CommonEdgeFormat.Font <- GraphvizFont("Helvetica", 10f)
  graphviz.CommonEdgeFormat.HeadArrow <- GraphvizArrow GraphvizArrowShape.Vee
  graphviz.CommonEdgeFormat.StrokeColor <- GraphvizColor.Azure

  graphviz.GraphFormat.BackgroundColor <- GraphvizColor(255uy, 46uy, 46uy, 46uy)
  graphviz.Generate()

let visitSource (sourcePath: string) =
  let input = IO.File.ReadAllText sourcePath
  let tree = getUntypedTree (sourcePath, SourceText.ofString input)

  match tree with
  | ParsedInput.ImplFile implFile ->
    let ParsedImplFileInput(contents = modules) = implFile
    let graph = visitModulesAndNamespaces modules
    exportToGraphviz graph
  | _ -> failwith "F# Interface file (*.fsi) not supported."
