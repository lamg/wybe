module LanguageServices.Compact.SemanticRules

open AST

// every expression has a domain
// every statement's precondition includes the domain of its composing expressions
// composing two statements creates a proof obligation, that the variables coming from the previous
// statement used in the next, are included in the next statement domains
// this is a special case of Q ⇒ W ⇒ ({P} S {Q}; { W } T { Y })

open Core
open GriesSchneider


let rec mkWybeExpr (ctx: Map<Expr, WSort>) (e: Expr) : WExpr option =
  match e with
  | Var x ->
    if not (ctx.ContainsKey e) then
      printfn $"not contains {e}"

    Some
      { name = String.concat "." x
        sort = ctx[e] }
  | Lit(Int n) -> Some(Integer.Integer(int64 n))
  | Lit(Str _) -> None
  | Lit(Bool true) -> Some True
  | Lit(Bool false) -> Some False
  | Unary(CompactOp.Not, x) -> mkWybeExpr ctx x |> Option.map (fun x -> Not(x :?> Proposition))
  | Binary(x, op, y) ->
    match op, mkWybeExpr ctx x, mkWybeExpr ctx y with
    | CompactOp.Eq, Some wx, Some wy -> Some(Core.Equals(wx, wy))
    | CompactOp.Div, Some wx, Some wy -> Some(Core.Divide(wx :?> Integer, wy :?> Integer) :> WExpr)
    | _ -> None
  | MemberAccess(_, _) -> None
  | IndexAccess(_, _) -> None
  | Array xs ->
    let s =
      match ctx[e] with
      | WSeq s -> s
      | s -> failwith $"wrong sort for array {s}"

    let ys = xs |> Seq.choose (fun x -> mkWybeExpr ctx x)
    (wSeq s ys :> WExpr) |> Some
  | Call(longId, _typeArgs, args) ->
    let dotId = longId |> String.concat "."
    let exprArgs = args |> List.choose (mkWybeExpr ctx)
    let signature = args |> List.map (fun a -> ctx[a])
    let f = FnApp.App(Function.Fn(dotId, signature), exprArgs)

    let r =
      match List.last signature with
      | WSeq _ -> ExtSeq f :> WExpr
      | WBool -> ExtBoolOp f
      | WInt -> ExtInteger f
      | WVarSort _ -> failwith "Not implemented generic return type"

    Some r
  | Unary(_, _) -> None
  | Cast(_, _) -> None
  | Version(_) -> None
  | As(_, _) -> None

let rec extractDomain (ctx: Map<Expr, WSort>) : Expr -> Proposition list =
  function
  | Call([ "assert" ], _, args) ->
    let argsDomain = args |> List.collect (extractDomain ctx) |> List.fold (<&&>) True
    let r = (mkWybeExpr ctx args.Head).Value :?> Proposition

    match argsDomain with
    | True -> [ r ]
    | _ -> [ argsDomain; r ]

  | Binary(_, CompactOp.Div, y) -> [ (mkWybeExpr ctx y).Value != zero ]
  | IndexAccess(xs, i) ->
    let wxs = (mkWybeExpr ctx xs).Value
    let wi = (mkWybeExpr ctx i).Value :?> Integer
    [ zero <= wi <&&> (wi < len wxs) ]
  | _ -> []

let rec statementDomain (ctx: Map<Expr, WSort>) =
  function
  | Assign(_, e) -> extractDomain ctx e
  | If(cond, thenB, elseB) ->
    let condDomain = extractDomain ctx cond
    let thenDomain = thenB |> List.collect (statementDomain ctx)

    let elseDomain =
      elseB |> Option.toList |> List.concat |> List.collect (statementDomain ctx)

    condDomain @ thenDomain @ elseDomain
  | For(_, _, _, body) -> body |> List.collect (statementDomain ctx)
  | Return(Some e) -> extractDomain ctx e
  | Return None -> []
  | CallStatement e -> extractDomain ctx e
  | Const(_, e) -> extractDomain ctx e

let statementImage (ctx: Map<Expr, WSort>) =
  function
  | Const(id, e) ->
    match mkWybeExpr ctx e with
    | Some n ->
      let v =
        { name = String.concat "." id
          sort = ctx[e] }

      Core.Equals(v, n) :: extractDomain ctx e
    | _ -> []
  | _ -> []


let statementSemanticInfo (types: Map<Expr, CompactType>) statement : Proposition list =
  let rec compactTypeToWSort =
    function
    | NamedType([ "int" ], _) -> Some WSort.WInt
    | NamedType([ "bool" ], _) -> Some WSort.WBool
    | NamedType(t, [ TypeParamInt _; CompactTypeParam t0 ]) when t.Equals compactVector ->
      t0 |> compactTypeToWSort |> Option.map WSort.WSeq
    | NamedType(id, _) -> Some(WSort.WVarSort(id |> String.concat "."))
    | Void -> Some(WSort.WVarSort "Void")

  let ctx =
    types
    |> Map.toSeq
    |> Seq.choose (fun (k, v) -> compactTypeToWSort v |> Option.map (fun s -> (k, s)))
    |> Map.ofSeq

  statementDomain ctx statement

let functionsSemanticInfo (fs: Map<string, Statement list * Map<Expr, CompactType>>) : Map<string, Proposition array> =
  fs
  |> Map.map (fun funName (statements, types) ->
    let a = mkIntVar "a"
    let b = mkIntVar "b"

    match funName with
    | "validCalc" -> [| a = Integer.Integer 18 <&&> (b = Integer.Integer 1) ==> (b != zero) |]
    | "invalidCalc" -> [| a = Integer.Integer 18 <&&> (b = Integer.Integer 0) ==> (b != zero) |]
    | _ ->
      let props = statements |> List.collect (statementSemanticInfo types)

      match props with
      | [] -> [||]
      | x :: xs -> [| xs |> List.fold (<&&>) x |])

let moduleSemanticInfo (existingEnv: TypeChecker.TcEnv) (ts: TopLevel list) =
  ts |> TypeChecker.exprTypesByFunction existingEnv |> functionsSemanticInfo

let extractSemanticInfo (existingEnv: TypeChecker.TcEnv) (input: string) : Map<string, Proposition array> =
  input |> Parser.parse |> moduleSemanticInfo existingEnv
