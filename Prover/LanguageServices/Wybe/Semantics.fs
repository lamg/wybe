module LanguageServices.Wybe.Semantics

open AST

type Expected =
  { expected: Type
    got: SemanticResult
    atChild: int }

and SemanticResult =
  | Typed of Type
  | TypedDomain of Type * domain: SemanticTree list
  | Expecting of Expected list
  | ExpectingSameType of got: Type list
  | NotRecognizedOperator of Op
  | NotFoundVar of string
  | Untyped
  | MalformedAssignment
  | MultipleResults of SemanticResult list
  | UndeclaredVariable of string

  member this.Type =
    match this with
    | Typed r -> Some r
    | TypedDomain(r, _) -> Some r
    | _ -> None

  member this.AddDomain(expr: SemanticTree) =
    match this with
    | Typed t -> TypedDomain(t, [ expr ])
    | TypedDomain(t, xs) -> TypedDomain(t, expr :: xs)
    | _ -> this

  member this.Domain =
    match this with
    | TypedDomain(_, xs) ->
      match xs with
      | [] -> None
      | y :: ys ->
        ys
        |> List.fold (fun acc x -> ST((Typed Type.Boolean, Binary(x.Expr, Op.And, acc.Expr)), [ acc; x ])) y
        |> Some
    | _ -> None

  member this.MismatchedTypes =
    match this with
    | Expecting xs -> xs
    | _ -> []

and SemanticTree =
  | ST of value: (SemanticResult * Expr) * children: SemanticTree list

  member this.AddDomain(expr: SemanticTree) =
    let (ST((r, e), xs)) = this
    ST((r.AddDomain expr, e), xs)

  member this.Expr =
    let (ST((_, expr), _)) = this
    expr

  member this.SemanticResult =
    let (ST((r, _), _)) = this
    r

  member this.Children =
    let (ST(_, children)) = this
    children

let rec checkChildrenFixedType
  (vars: Map<string, Type>)
  (e: Expr, resultType: Type)
  (expectedType: Type, children: Expr list)
  =
  let xs = children |> List.map (extractTypeAndDomain vars)

  xs
  |> List.mapi (fun i r ->
    match r.SemanticResult.Type with
    | Some t when t = expectedType -> None
    | Some t ->
      Some
        { expected = expectedType
          got = Typed t
          atChild = i }
    | _ -> None)
  |> List.choose id
  |> function
    | [] ->
      let childrenDomains = xs |> List.choose (fun x -> x.SemanticResult.Domain)

      match childrenDomains with
      | [] -> ST((Typed resultType, e), xs)
      | _ -> ST((TypedDomain(resultType, childrenDomains), e), xs)

    | rs -> ST((Expecting rs, e), xs)

and checkChildrenEqualType (vars: Map<string, Type>) (e: Expr, resultType: Type) (children: Expr list) =
  let xs = children |> List.map (extractTypeAndDomain vars)
  let types = xs |> List.choose _.SemanticResult.Type |> Set

  if Set.count types = 1 then
    let childrenDomains = xs |> List.choose (fun x -> x.SemanticResult.Domain)

    match childrenDomains with
    | [] -> ST((Typed resultType, e), xs)
    | _ -> ST((TypedDomain(resultType, childrenDomains), e), xs)
  else
    ST((ExpectingSameType(Set.toList types), e), xs)

and extractTypeAndDomain (vars: Map<string, Type>) (e: Expr) : SemanticTree =
  match e with
  | Binary(left, op, right) ->

    match op with
    | Op.Plus
    | Op.Minus
    | Op.Times -> checkChildrenFixedType vars (e, Type.Integer) (Type.Integer, [ left; right ])
    | Op.Div ->
      let r =
        checkChildrenFixedType vars (e, Type.Integer) (Type.Integer, [ left; right ])

      let zero = Lit(Int 0)
      let diffZero = Binary(right, Op.Differs, zero)
      let typedZero = ST((Typed Type.Integer, zero), [])

      let domain = ST((Typed Type.Boolean, diffZero), [ r.Children[1]; typedZero ])
      r.AddDomain domain
    | Op.Equals
    | Op.Differs -> checkChildrenEqualType vars (e, Type.Boolean) [ left; right ]
    | Op.AtMost
    | Op.AtLeast
    | Op.LessThan
    | Op.Exceeds -> checkChildrenFixedType vars (e, Type.Boolean) (Type.Integer, [ left; right ])
    | Op.Equiv
    | Op.Inequiv
    | Op.And
    | Op.Or
    | Op.Implies
    | Op.Follows -> checkChildrenFixedType vars (e, Type.Boolean) (Type.Boolean, [ left; right ])
    | Op.Cons ->
      let l, r = extractTypeAndDomain vars left, extractTypeAndDomain vars right

      match l.SemanticResult.Type, r.SemanticResult.Type with
      | Some t, Some(Type.Array u) when u = t -> ST((Typed(Type.Array t), e), [ l; r ])
      | _ -> ST((NotRecognizedOperator op, e), [ l; r ])
    | Op.Concat ->
      let l, r = extractTypeAndDomain vars left, extractTypeAndDomain vars right

      match l.SemanticResult.Type, r.SemanticResult.Type with
      | Some(Type.Array t), Some(Type.Array u) when u = t -> ST((Typed(Type.Array t), e), [ l; r ])
      | _ -> ST((NotRecognizedOperator op, e), [ l; r ])
    | Op.IsPrefix
    | Op.IsSuffix -> checkChildrenFixedType vars (e, Type.Boolean) (Type.Array(Type.VarType "a"), [ left; right ])
    | _ ->
      let l, r = extractTypeAndDomain vars left, extractTypeAndDomain vars right
      ST((NotRecognizedOperator op, e), [ l; r ])
  | Unary(op, right) ->
    match op with
    | Op.Not -> checkChildrenFixedType vars (e, Type.Boolean) (Type.Boolean, [ right ])
    | Op.UnaryMinus -> checkChildrenFixedType vars (e, Type.Integer) (Type.Integer, [ right ])
    | Op.Length -> checkChildrenFixedType vars (e, Type.Integer) (Type.Array(Type.VarType "a"), [ right ])
    | Op.Head ->
      let r = extractTypeAndDomain vars right

      match r.SemanticResult.Type with
      | Some(Type.Array t) -> ST((Typed t, e), [ r ])
      | _ -> ST((NotRecognizedOperator op, e), [ r ])
    | Op.Tail ->
      let r = extractTypeAndDomain vars right

      match r.SemanticResult.Type with
      | Some(Type.Array t) -> ST((Typed(Type.Array t), e), [ r ])
      | _ -> ST((NotRecognizedOperator op, e), [ r ])
    | _ ->
      let r = extractTypeAndDomain vars right
      ST((NotRecognizedOperator op, e), [ r ])
  | Var name ->
    match Map.tryFind name vars with
    | Some v -> ST((Typed v, e), [])
    | None -> ST((NotFoundVar name, e), [])
  | Lit v ->
    match v with
    | Int _ -> ST((Typed Type.Integer, e), [])
    | Bool _ -> ST((Typed Type.Boolean, e), [])
    | Str _ -> ST((Typed Type.String, e), [])
  | Array xs ->
    match xs with
    | [] -> ST((Untyped, e), [])
    | y :: ys ->
      let r = extractTypeAndDomain vars y
      let rs = ys |> List.map (extractTypeAndDomain vars)

      match r with
      | ST((Typed t, _), _) ->
        // this branch reports which array elements do not have the
        // same type as the first element
        // in case the list of different types is empty, then the array
        // is correctly typed
        let diffElemTypes =
          rs
          |> List.mapi (fun i ->
            function
            | ST((Typed u, _), _) when t = u -> None
            | ST((u, _), _) ->
              Some
                { expected = t
                  got = u
                  atChild = i + 1 })
          |> List.choose id

        match diffElemTypes with
        | [] -> ST((Typed(Type.Array t), e), r :: rs)
        | _ -> ST((Expecting diffElemTypes, e), r :: rs)
      | ST((v, _), _) -> ST((v, e), r :: rs)
  | ArrayElem(name, index) ->
    match Map.tryFind name vars with
    | Some(Type.Array t) ->
      let indexResult = extractTypeAndDomain vars index

      match indexResult with
      | ST((TypedDomain(Type.Integer, _), _), _)
      | ST((Typed Type.Integer, _), _) ->
        let domain = indexResult.SemanticResult.Domain |> Option.toList
        let r = ST((TypedDomain(t, domain), e), [ indexResult ])

        let arrayDomain =
          Binary(Binary(Lit(Int 0), Op.AtMost, index), Op.And, Binary(index, Op.LessThan, Unary(Op.Length, Var name)))
          |> extractTypeAndDomain vars

        r.AddDomain arrayDomain
      | _ -> ST((Typed t, e), [ indexResult ])
    | Some t ->
      ST(
        (Expecting
          [ { expected = Type.Array(Type.VarType "a")
              got = Typed t
              atChild = 0 } ],
         e),
        []
      )
    | None -> ST((Untyped, e), [])

open Core

let rec exprToTree: Expr -> SymbolTree =
  function
  | Binary(left, op, right) ->
    let l, r = exprToTree left, exprToTree right

    let opSymbol =
      match op with
      | Op.Plus -> Symbol.Op("+", 5)
      | Op.Minus -> Symbol.Op("-", 5)
      | Op.Times -> Symbol.Op("×", 5)
      | Op.Div -> Symbol.Op("÷", 5)
      | Op.Equals -> Symbol.Op("=", 4)
      | Op.Differs -> Symbol.Op("≠", 4)
      | Op.AtMost -> Symbol.Op("≤", 4)
      | Op.AtLeast -> Symbol.Op("≥", 4)
      | Op.LessThan -> Symbol.Op("<", 4)
      | Op.Exceeds -> Symbol.Op(">", 4)
      | Op.And -> Symbol.Op("∧", 2)
      | Op.Or -> Symbol.Op("∨", 2)
      | Op.Implies -> Symbol.Op("⇒", 1)
      | Op.Follows -> Symbol.Op("⇐", 1)
      | Op.Equiv -> Symbol.Op("≡", 0)
      | Op.Inequiv -> Symbol.Op("≢", 0)
      | Op.Not -> Symbol.Op("¬", 3)
      | Op.UnaryMinus -> Symbol.Op("-", 6)
      | Op.Length -> Symbol.Op("#", 6)
      | Op.HasType -> Symbol.Op(":", 0)
      | Op.Cons -> Symbol.Op("::", 6)
      | Op.Concat -> Symbol.Op("++", 6)
      | Op.IsPrefix -> Symbol.Op("◁", 6)
      | Op.IsSuffix -> Symbol.Op("▷", 6)
      | _ -> failwith $"unexpected binary operator {op}"

    SymbolTree.Node(opSymbol, [ l; r ])
  | Unary(op, inner) ->
    let t = exprToTree inner

    let sym =
      match op with
      | Op.Not -> Symbol.Op("¬", 3)
      | Op.UnaryMinus -> Symbol.Op("-", 6)
      | Op.Length -> Symbol.Op("#", 6)
      | Op.Head -> Symbol.Atom "head"
      | Op.Tail -> Symbol.Atom "tail"
      | _ -> Symbol.Op(string op, 7)

    SymbolTree.Node(sym, [ t ])
  | Expr.Var name -> SymbolTree.Node(Symbol.Var name, [])
  | Lit literal ->
    let txt =
      match literal with
      | Int i -> string i
      | Bool b -> if b then "true" else "false"
      | Str s -> $"\"{s}\""

    SymbolTree.Node(Symbol.Const txt, [])
  | Array elems ->
    let trees = elems |> List.map exprToTree

    match List.rev trees with
    | [] -> SymbolTree.Node(Symbol.Indexed, [])
    | x :: xs ->
      let commaTree =
        xs |> List.fold (fun acc e -> SymbolTree.Node(Symbol.Op(",", 0), [ e; acc ])) x

      SymbolTree.Node(Symbol.Indexed, [ commaTree ])
  | ArrayElem(name, index) ->
    SymbolTree.Node(Symbol.Atom name, [ SymbolTree.Node(Symbol.Indexed, [ exprToTree index ]) ])


let collectSemanticTreeInfo (e: SemanticTree) =
  let errorInfo (e: SemanticTree) =
    match e.SemanticResult with
    | Expecting xs -> xs |> List.map (fun x -> $"expecting {x.expected}, got {x.got}")
    | ExpectingSameType got -> [ $"expecting same type, got: {got |> List.map string}" ]
    | NotRecognizedOperator op -> [ $"not recognized operator {op}" ]
    | NotFoundVar v -> [ $"not found var {v}" ]
    | Untyped -> [ "failed to infer expression type" ]
    | _ -> []
    |> List.map (fun r -> $"{exprToTree e.Expr}: {r}")

  let rec innerInfo (e: SemanticTree) =
    let info = errorInfo e
    info @ (e.Children |> List.collect innerInfo)

  let rootMessage =
    match e.SemanticResult with
    | Typed t -> [ $"has type {t}" ]
    | TypedDomain _ ->
      [ $"has type {e.SemanticResult.Type.Value}"
        $"has domain {e.SemanticResult.Domain.Value.Expr |> exprToTree}" ]
    | _ -> innerInfo e

  $"info {exprToTree e.Expr}:" :: rootMessage

open GriesSchneider

type DomainWExpr =
  | DomainWExpr of domain: WExpr option * expr: WExpr

  member this.Expr =
    let (DomainWExpr(_, expr)) = this
    expr

  member this.Domain =
    let (DomainWExpr(domain, _)) = this
    domain

let semanticExprToWExpr (e: SemanticTree) : DomainWExpr =
  let rec typedToWExpr (e: SemanticTree) : WExpr =
    match e.SemanticResult.Type with
    | Some Type.Boolean ->
      match e.Expr, e.Children with
      | Binary(_, Op.And, _), [ l; r ] -> typedToWExpr l <&&> typedToWExpr r
      | Binary(_, Op.Or, _), [ l; r ] -> typedToWExpr l <||> typedToWExpr r
      | Binary(_, Op.Implies, _), [ l; r ] -> typedToWExpr l ==> typedToWExpr r
      | Binary(_, Op.Follows, _), [ l; r ] -> typedToWExpr l <== typedToWExpr r
      | Binary(_, Op.Equiv, _), [ l; r ] -> typedToWExpr l === typedToWExpr r
      | Binary(_, Op.Inequiv, _), [ l; r ] -> typedToWExpr l !== typedToWExpr r
      | Binary(_, Op.Equals, _), [ l; r ] -> Core.Equals(typedToWExpr l, typedToWExpr r)
      | Binary(_, Op.Differs, _), [ l; r ] -> typedToWExpr l != typedToWExpr r
      | Binary(_, Op.AtMost, _), [ l; r ] -> typedToWExpr l <= typedToWExpr r
      | Binary(_, Op.AtLeast, _), [ l; r ] -> typedToWExpr l >= typedToWExpr r
      | Binary(_, Op.LessThan, _), [ l; r ] -> typedToWExpr l < typedToWExpr r
      | Binary(_, Op.Exceeds, _), [ l; r ] -> typedToWExpr l > typedToWExpr r
      | Binary(_, Op.IsPrefix, _), [ l; r ] ->
        IsPrefix(typedToWExpr l :?> Sequence, typedToWExpr r :?> Sequence) :> WExpr
      | Binary(_, Op.IsSuffix, _), [ l; r ] ->
        IsSuffix(typedToWExpr l :?> Sequence, typedToWExpr r :?> Sequence) :> WExpr
      | Unary(Op.Not, _), [ c ] -> !(typedToWExpr c)
      | Lit(Bool b), [] -> if b then True else False
      | Expr.Var name, [] -> mkBoolVar name
      | _ -> failwith $"unexpected boolean expression: {exprToTree e.Expr}"
    | Some Type.Integer ->
      match e.Expr, e.Children with
      | Lit(Int i), [] -> Integer i :> WExpr
      | Unary(Op.UnaryMinus, _), [ c ] -> -(typedToWExpr c :?> Integer) :> WExpr
      | Unary(Op.Length, _), [ c ] -> len (typedToWExpr c) :> WExpr
      | Binary(_, Op.Plus, _), [ l; r ] -> (typedToWExpr l :?> Integer) + (typedToWExpr r :?> Integer) :> WExpr
      | Binary(_, Op.Minus, _), [ l; r ] -> (typedToWExpr l :?> Integer) - (typedToWExpr r :?> Integer) :> WExpr
      | Binary(_, Op.Times, _), [ l; r ] -> (typedToWExpr l :?> Integer) * (typedToWExpr r :?> Integer) :> WExpr
      | Binary(_, Op.Div, _), [ l; r ] -> (typedToWExpr l :?> Integer) / (typedToWExpr r :?> Integer) :> WExpr
      | Expr.Var name, [] -> mkIntVar name
      | _ -> failwith $"not implemented: {exprToTree e.Expr}"
    | Some(Type.Array inner) ->
      match e.Expr, e.Children with
      | Array _, elemsST ->
        let ws = elemsST |> List.map typedToWExpr

        let seqSort =
          match inner with
          | Type.Integer -> WSeq WInt
          | Type.Boolean -> WSeq WBool
          | _ -> failwith $"unsupported sequence element type: {inner}"

        List.rev ws |> List.fold (fun acc v -> Cons(v, acc)) (Empty seqSort) :> WExpr
      | Binary(_, Op.Cons, _), [ lST; rST ] -> Cons(typedToWExpr lST, typedToWExpr rST :?> Sequence) :> WExpr
      | Binary(_, Op.Concat, _), [ lST; rST ] ->
        Concat(typedToWExpr lST :?> Sequence, typedToWExpr rST :?> Sequence) :> WExpr
      | Unary(Op.Head, _), [ cST ] -> Head(typedToWExpr cST :?> Sequence) :> WExpr
      | Unary(Op.Tail, _), [ cST ] -> Tail(typedToWExpr cST :?> Sequence) :> WExpr
      | _ -> failwith $"not implemented sequence op: {exprToTree e.Expr}"
    | _ -> failwith $"not implemented: {exprToTree e.Expr}"

  let domain = e.SemanticResult.Domain |> Option.map typedToWExpr
  DomainWExpr(domain, typedToWExpr e)

type StateSpace =
  | StateSpace of Map<string, Type> * Proposition

  member this.Proposition =
    let (StateSpace(_, prop)) = this
    prop

  member this.Vars =
    let (StateSpace(vars, _)) = this
    vars

let makeWExpr vars (expected: Type) (expr: Expr) =
  match checkChildrenFixedType vars (expr, expected) (expected, [ expr ]) with
  | e when e.SemanticResult.Type.IsSome -> Ok(semanticExprToWExpr e)
  | e -> Error e.SemanticResult

let makeStateSpace vars (predicate: Expr) =
  match checkChildrenFixedType vars (predicate, Type.Boolean) (Type.Boolean, [ predicate ]) with
  | pred when pred.SemanticResult.Type.IsSome ->
    match semanticExprToWExpr pred with
    | wexpr when wexpr.Domain.IsSome -> Ok(StateSpace(vars, wexpr.Domain.Value <&&> wexpr.Expr))
    | wexpr -> Ok(StateSpace(vars, wexpr.Expr :?> Proposition))
  | r -> Error r

type Guard =
  | Guard of condition: WExpr * body: Statement

  member this.Condition =
    let (Guard(condition, _)) = this
    condition

  member this.Body =
    let (Guard(_, body)) = this
    body

and Statement =
  | VarDecl of SameTypeDecl list
  | Becomes of (string * DomainWExpr) list
  | If of Guard list
  | Do of Guard list
  | Assert of WExpr
  | Compose of Statement * Statement
  | Skip
  | Abort

// weakest precondition of assignemt
// wp.(x := E).P = defined.E ∧ P[x := E]
let wpAssignment (becomes: (string * DomainWExpr) list) (space: StateSpace) =
  let rec substitute (target: WExpr) ((var, expr): string * DomainWExpr) =
    target.TextualSubstitution var expr.Expr

  let expr = becomes |> List.fold substitute space.Proposition

  match becomes |> List.choose (snd >> _.Domain) with
  | [] -> StateSpace(space.Vars, expr :?> Proposition)
  | x :: xs ->
    let domain = xs |> List.fold (fun acc x -> acc <&&> x) (x :?> Proposition)
    StateSpace(space.Vars, domain <&&> expr)

let wpVarDecls (xs: SameTypeDecl list) (space: StateSpace) =
  let addVarType t (acc: Map<string, Type>) name = Map.add name t acc
  let addSameType vars t map = vars |> List.fold (addVarType t) map

  let newVars =
    xs |> List.fold (fun acc (vars, t) -> addSameType vars t acc) space.Vars

  StateSpace(newVars, space.Proposition)

let rec wpComposition (s: Statement, t: Statement) (space: StateSpace) = wpStatement s (wpStatement t space)
// wp.(if cond0 -> body0 | cond1 -> body1 fi).P = (cond0 ∨ cond1) ∧ (cond0 ⇒ wp.body0.P) ∧ (cond1 ⇒ wp.body1.P)
and wpAlternative (guards: Guard list) (space: StateSpace) =
  let conds, bodies =
    guards
    |> List.map (fun g -> g.Condition, g.Condition ==> (wpStatement g.Body space).Proposition)
    |> List.unzip

  let orConds =
    conds.Tail |> List.fold (fun acc c -> acc <||> c) (conds.Head :?> Proposition)

  let andBodies = bodies.Tail |> List.fold (fun acc c -> acc <&&> c) bodies.Head
  StateSpace(space.Vars, orConds <&&> andBodies)

// wlp.(do cond0 → body0 | cond1 → body1 od).P = (cond0 ∧ P ⇒ wp.body0.P) ∧ (cond1 ∧ P ⇒ wp.body1.P)
and wlpRepetition (guards: Guard list) (space: StateSpace) =
  let bodies =
    guards
    |> List.map (fun g -> g.Condition <&&> space.Proposition ==> (wpStatement g.Body space).Proposition)

  let andBodies = bodies.Tail |> List.fold (fun acc c -> acc <&&> c) bodies.Head
  StateSpace(space.Vars, andBodies <&&> space.Proposition)

and wpStatement (s: Statement) (space: StateSpace) =
  match s with
  | VarDecl xs -> wpVarDecls xs space
  | Becomes becomes -> wpAssignment becomes space
  | Compose(s, t) -> wpComposition (s, t) space
  | If guards -> wpAlternative guards space
  | Do guards -> wlpRepetition guards space
  | Assert expr -> StateSpace(space.Vars, expr ==> space.Proposition)
  | Skip -> space // wp.skip.P = P
  | Abort -> StateSpace(Map.empty, False)

let rec astStatementToSemantic (vars: Map<string, Type>) (s: AST.Statement) =
  let splitResult (rs: Result<'a, 'b> list) =
    let oks, errs = rs |> List.partition Result.isOk

    let oks =
      oks
      |> List.map (function
        | Ok x -> x
        | _ -> failwith "expecting ok")

    let errs =
      errs
      |> List.map (function
        | Error e -> e
        | _ -> failwith "expecting error")

    oks, errs

  let guardedBlock (guards: AST.Guard list) =
    let oks, errs =
      guards
      |> List.map (fun g ->
        match makeStateSpace vars g.Condition with
        | Ok e ->
          match astStatementToSemantic vars g.Body with
          | Ok body -> Ok(Guard(e.Proposition, body))
          | Error m -> Error m
        | Error m -> Error m)
      |> splitResult

    match errs with
    | [] -> Ok oks
    | errs ->
      let r = errs |> List.map _.SemanticResult |> MultipleResults
      Error(ST((r, Lit(Str "")), []))


  match s with
  | AST.VarDecl xs -> Ok(VarDecl xs)
  | AST.Abort -> Ok Abort
  | AST.Skip -> Ok Skip
  | AST.Assert expr ->
    match makeStateSpace vars expr with
    | Ok s -> Ok(Assert s.Proposition)
    | Error e -> Error e
  | AST.Becomes(vs, exprs) when vs.Length.Equals exprs.Length ->
    let oks, errs =
      exprs
      |> List.zip vs
      |> List.map (fun (v, e) ->
        match Map.tryFind v vars with
        | Some t -> makeWExpr vars t e |> Result.map (fun r -> v, r)
        | None -> Error(UndeclaredVariable v))
      |> splitResult

    match errs with
    | [] -> Ok(Becomes oks)
    | [ e ] -> Error(ST((e, Lit(Str "")), []))
    | _ -> Error(ST((MultipleResults errs, Lit(Str "")), []))
  | AST.Becomes _ -> Error(ST((MalformedAssignment, Lit(Str "")), []))
  | AST.Do guards -> guardedBlock guards |> Result.map Do
  | AST.If guards -> guardedBlock guards |> Result.map If
