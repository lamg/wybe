module LanguageServices.Compact.SemanticRules

open AST

// import CompactStandardLibrary;
// enum State { unset, set }
//
// export ledger authority: Bytes<32>;
// export ledger value: Uint<64>;
// export ledger state: State;
// export ledger round: Counter;
//
// constructor(sk: Bytes<32>, v: Uint<64>) {
//   authority = publicKey(round, sk);
//   value = v;
//   state = State.set;
// }
//
// circuit publicKey(round: Field, sk: Bytes<32>): Bytes<32> {
//   return persistentHash<Vector<3, Bytes<32>>>(
//     [pad(32, "midnight:examples:lock:pk"),
//      round as Bytes<32>,
//      sk]);
// }
//

// extracted predicate
// sk: Bytes<32> ∧ v: Uint<64> ∧ constructor(sk, v) = ()
// ⇒ authority = publicKey(round, sk) ∧ value = v ∧ state = State.set

// export circuit get(): Uint<64> {
//   assert(state == State.set, "Attempted to get uninitialized value");
//   return value;
// }
//
// witness secretKey(): Bytes<32>;
//
// export circuit set(v: Uint<64>): [] {
//   assert(state == State.unset, "Attempted to set initialized value");
//   const sk = secretKey();
//   const pk = publicKey(round, sk);
//   authority = pk;
//   value = v;
//   state = State.set;
// }
//
// export circuit clear(): [] {
//   assert(state == State.set, "Attempted to clear uninitialized value");
//   const sk = secretKey();
//   const pk = publicKey(round, sk);
//   assert(authority == pk, "Attempted to clear without authorization");
//   state = State.unset;
//   round.increment(1);
// }

// every expression has a domain
// every statement's precondition includes the domain of its composing expressions
// composing two statements creates a proof obligation, that the variables coming from the previous
// statement used in the next, are included in the next statement domains
// this is a special case of Q ⇒ W ⇒ ({P} S {Q}; { W } T { Y })

open Core
open GriesSchneider


let rec mkWybeExpr (ctx: Map<Expr, WSort>) (e: Expr) : WExpr option =
  match e with
  | Var x -> Some { name = x.Head; sort = ctx[e] }
  | Lit(Int n) -> Some(Integer.Integer(int64 n))
  | Lit(Str _) -> None
  | Lit(Bool true) -> Some True
  | Lit(Bool false) -> Some False
  | Unary(CompactOp.Not, x) -> mkWybeExpr ctx x |> Option.map (fun x -> Not(x :?> Proposition))
  | Binary(_, _, _) -> failwith "Not Implemented"
  | MemberAccess(_, _) -> failwith "Not Implemented"
  | IndexAccess(_, _) -> failwith "Not Implemented"
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
  | _ -> None

let fold1 f (xs: List<'a>) = List.fold f xs.Head xs

let rec extractDomain (ctx: Map<Expr, WSort>) : Expr -> Proposition list =
  function
  | Call([ "assert" ], _, args) ->
    let argsDomain = args |> List.collect (extractDomain ctx) |> fold1 (<&&>)
    [ argsDomain; (mkWybeExpr ctx args.Head).Value :?> Proposition ]

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

let statementSemanticInfo (types: Map<Expr, CompactType>) statement : Proposition list =
  let rec compactTypeToWSort =
    function
    | NamedType([ "int" ], _) -> Some WSort.WInt
    | NamedType([ "bool" ], _) -> Some WSort.WBool
    | NamedType(t, [ TypeParamInt _; CompactTypeParam t0 ]) when t.Equals compactArrayTypeId ->
      t0 |> compactTypeToWSort |> Option.map WSort.WSeq
    | _ -> None

  let ctx =
    types
    |> Map.toSeq
    |> Seq.choose (fun (k, v) -> compactTypeToWSort v |> Option.map (fun s -> (k, s)))
    |> Map.ofSeq

  statementDomain ctx statement

let functionsSemanticInfo (fs: Map<string, Statement list * Map<Expr, CompactType>>) : Map<string, Proposition array> =
  fs
  |> Map.map (fun _ (statements, types) -> statements |> List.collect (statementSemanticInfo types) |> List.toArray)

let moduleSemanticInfo (existingEnv: TypeChecker.TcEnv) (ts: TopLevel list) =
  ts |> TypeChecker.exprTypesByFunction existingEnv |> functionsSemanticInfo

let extractSemanticInfo (existingEnv: TypeChecker.TcEnv) (input: string) : Map<string, Proposition array> =
  input |> Parser.parse |> moduleSemanticInfo existingEnv
