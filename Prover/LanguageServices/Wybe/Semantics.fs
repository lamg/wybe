module LanguageServices.Wybe.Semantics

open AST

type Expected =
  { expected: Type
    got: TypingResult
    atChild: int }

and TypingResult =
  | Typed of Type
  | TypedDomain of Type * domain: TypedTree list
  | Expecting of Expected list
  | ExpectingSameType of got: Type list
  | NotRecognizedOperator of Op
  | NotFoundVar of string
  | Untyped
  | MalformedAssignment
  | MultipleResults of TypingResult list
  | UndeclaredVariable of string

  member this.Type =
    match this with
    | Typed r -> Some r
    | TypedDomain(r, _) -> Some r
    | _ -> None

  member this.AddDomain(expr: TypedTree) =
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
        |> List.fold (fun acc x -> TypedTree(Typed Type.Boolean, Binary(x.Expr, Op.And, acc.Expr), [ acc; x ])) y
        |> Some
    | _ -> None

  member this.MismatchedTypes =
    match this with
    | Expecting xs -> xs
    | _ -> []

and TypedTree =
  | TypedTree of result: TypingResult * expr: Expr * children: TypedTree list

  member this.AddDomain(expr: TypedTree) =
    let (TypedTree(r, e, xs)) = this
    TypedTree(r.AddDomain expr, e, xs)

  member this.Expr =
    let (TypedTree(_, expr, _)) = this
    expr

  member this.SemanticResult =
    let (TypedTree(r, _, _)) = this
    r

  member this.Children =
    let (TypedTree(_, _, children)) = this
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
      | [] -> TypedTree(Typed resultType, e, xs)
      | _ -> TypedTree(TypedDomain(resultType, childrenDomains), e, xs)

    | rs -> TypedTree(Expecting rs, e, xs)

and checkChildrenEqualType (vars: Map<string, Type>) (e: Expr, resultType: Type) (children: Expr list) =
  let xs = children |> List.map (extractTypeAndDomain vars)
  let types = xs |> List.choose _.SemanticResult.Type |> Set

  if Set.count types = 1 then
    let childrenDomains = xs |> List.choose (fun x -> x.SemanticResult.Domain)

    match childrenDomains with
    | [] -> TypedTree(Typed resultType, e, xs)
    | _ -> TypedTree(TypedDomain(resultType, childrenDomains), e, xs)
  else
    TypedTree(ExpectingSameType(Set.toList types), e, xs)

and extractTypeAndDomain (vars: Map<string, Type>) (e: Expr) : TypedTree =
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
      let typedZero = TypedTree(Typed Type.Integer, zero, [])

      let domain = TypedTree(Typed Type.Boolean, diffZero, [ r.Children[1]; typedZero ])
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
      | Some t, Some(Type.Array u) when u = t -> TypedTree(Typed(Type.Array t), e, [ l; r ])
      | _ -> TypedTree(NotRecognizedOperator op, e, [ l; r ])
    | Op.Concat ->
      let l, r = extractTypeAndDomain vars left, extractTypeAndDomain vars right

      match l.SemanticResult.Type, r.SemanticResult.Type with
      | Some(Type.Array t), Some(Type.Array u) when u = t -> TypedTree(Typed(Type.Array t), e, [ l; r ])
      | _ -> TypedTree(NotRecognizedOperator op, e, [ l; r ])
    | Op.IsPrefix
    | Op.IsSuffix -> checkChildrenFixedType vars (e, Type.Boolean) (Type.Array(Type.VarType "a"), [ left; right ])
    | _ ->
      let l, r = extractTypeAndDomain vars left, extractTypeAndDomain vars right
      TypedTree(NotRecognizedOperator op, e, [ l; r ])
  | Unary(op, right) ->
    match op with
    | Op.Not -> checkChildrenFixedType vars (e, Type.Boolean) (Type.Boolean, [ right ])
    | Op.UnaryMinus -> checkChildrenFixedType vars (e, Type.Integer) (Type.Integer, [ right ])
    | Op.Length -> checkChildrenFixedType vars (e, Type.Integer) (Type.Array(Type.VarType "a"), [ right ])
    | Op.Head ->
      let r = extractTypeAndDomain vars right

      match r.SemanticResult.Type with
      | Some(Type.Array t) -> TypedTree(Typed t, e, [ r ])
      | _ -> TypedTree(NotRecognizedOperator op, e, [ r ])
    | Op.Tail ->
      let r = extractTypeAndDomain vars right

      match r.SemanticResult.Type with
      | Some(Type.Array t) -> TypedTree(Typed(Type.Array t), e, [ r ])
      | _ -> TypedTree(NotRecognizedOperator op, e, [ r ])
    | _ ->
      let r = extractTypeAndDomain vars right
      TypedTree(NotRecognizedOperator op, e, [ r ])
  | Var name ->
    match Map.tryFind name vars with
    | Some v -> TypedTree(Typed v, e, [])
    | None -> TypedTree(NotFoundVar name, e, [])
  | Lit v ->
    match v with
    | Int _ -> TypedTree(Typed Type.Integer, e, [])
    | Bool _ -> TypedTree(Typed Type.Boolean, e, [])
    | Str _ -> TypedTree(Typed Type.String, e, [])
  | Array xs ->
    match xs with
    | [] -> TypedTree(Untyped, e, [])
    | y :: ys ->
      let r = extractTypeAndDomain vars y
      let rs = ys |> List.map (extractTypeAndDomain vars)

      match r with
      | TypedTree(Typed t, _, _) ->
        // this branch reports which array elements do not have the
        // same type as the first element
        // in case the list of different types is empty, then the array
        // is correctly typed
        let diffElemTypes =
          rs
          |> List.mapi (fun i ->
            function
            | TypedTree(Typed u, _, _) when t = u -> None
            | TypedTree(u, _, _) ->
              Some
                { expected = t
                  got = u
                  atChild = i + 1 })
          |> List.choose id

        match diffElemTypes with
        | [] -> TypedTree(Typed(Type.Array t), e, r :: rs)
        | _ -> TypedTree(Expecting diffElemTypes, e, r :: rs)
      | TypedTree(v, _, _) -> TypedTree(v, e, r :: rs)
  | ArrayElem(name, index) ->
    match Map.tryFind name vars with
    | Some(Type.Array t) ->
      let indexResult = extractTypeAndDomain vars index

      match indexResult with
      | TypedTree(TypedDomain(Type.Integer, _), _, _)
      | TypedTree(Typed Type.Integer, _, _) ->
        let domain = indexResult.SemanticResult.Domain |> Option.toList
        let r = TypedTree(TypedDomain(t, domain), e, [ indexResult ])

        let arrayDomain =
          Binary(Binary(Lit(Int 0), Op.AtMost, index), Op.And, Binary(index, Op.LessThan, Unary(Op.Length, Var name)))
          |> extractTypeAndDomain vars

        r.AddDomain arrayDomain
      | _ -> TypedTree(Typed t, e, [ indexResult ])
    | Some t ->
      TypedTree(
        Expecting
          [ { expected = Type.Array(Type.VarType "a")
              got = Typed t
              atChild = 0 } ],
        e,
        []
      )
    | None -> TypedTree(Untyped, e, [])

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


let collectSemanticTreeInfo (e: TypedTree) =
  let errorInfo (e: TypedTree) =
    match e.SemanticResult with
    | Expecting xs -> xs |> List.map (fun x -> $"expecting {x.expected}, got {x.got}")
    | ExpectingSameType got -> [ $"expecting same type, got: {got |> List.map string}" ]
    | NotRecognizedOperator op -> [ $"not recognized operator {op}" ]
    | NotFoundVar v -> [ $"not found var {v}" ]
    | Untyped -> [ "failed to infer expression type" ]
    | _ -> []
    |> List.map (fun r -> $"{exprToTree e.Expr}: {r}")

  let rec innerInfo (e: TypedTree) =
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

let semanticExprToWExpr (e: TypedTree) : DomainWExpr =
  let rec typedToWExpr (e: TypedTree) : WExpr =
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
      | _ -> failwith $"unexpected boolean expression: {exprToTree e.Expr} children length {e.Children.Length}"
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

let varsToString (vars: Map<string, Type>) =
  vars |> Map.toList |> List.map (fun (k, v) -> $"{k}: {v}") |> String.concat "\n"

let makeWExpr vars (expected: Type) (expr: Expr) =
  match checkChildrenFixedType vars (expr, expected) (expected, [ expr ]) with
  | e when e.SemanticResult.Type.IsSome -> Ok(semanticExprToWExpr e.Children.Head)
  | e -> Error e.SemanticResult

let makePredicate vars (predicate: Expr) =
  match checkChildrenFixedType vars (predicate, Type.Boolean) (Type.Boolean, [ predicate ]) with
  | pred when pred.SemanticResult.Type.IsSome ->
    match semanticExprToWExpr pred.Children.Head with
    | wexpr when wexpr.Domain.IsSome -> Ok(wexpr.Domain.Value <&&> wexpr.Expr)
    | wexpr -> Ok(wexpr.Expr :?> Proposition)
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
  | Becomes of (string * DomainWExpr) list
  | If of Guard list
  | Do of Guard list
  | Assert of Proposition
  | Compose of Statement * Statement
  | Skip
  | Abort

  override this.ToString() =
    let guardsToStr (guards: Guard list) =
      guards |> List.map (fun g -> $"{g.Condition} → {g.Body}") |> String.concat " ⫿ "

    match this with
    | Becomes xs ->
      let lhs, rhs = List.unzip xs
      let vars = lhs |> String.concat ", "
      let exprs = rhs |> List.map (_.Expr >> string) |> String.concat ", "
      $"{vars} ≔ {exprs}"
    | If guards -> $"if {guardsToStr guards} fi"
    | Do guards -> $"do {guardsToStr guards} od"
    | Assert p -> $"{{{p}}}"
    | Compose(s, t) -> $"{s};{t}"
    | Skip -> "skip"
    | Abort -> "abort"

// weakest precondition of assignemt
// wp.(x := E).P = defined.E ∧ P[x := E]
let wpAssignment (becomes: (string * DomainWExpr) list) (postcondition: Proposition) =
  let rec substitute (target: WExpr) ((var, expr): string * DomainWExpr) =
    target.TextualSubstitution var expr.Expr

  let expr = becomes |> List.fold substitute postcondition

  match becomes |> List.choose (snd >> _.Domain) with
  | [] -> expr :?> Proposition
  | x :: xs ->
    let domain = xs |> List.fold (fun acc x -> acc <&&> x) (x :?> Proposition)
    domain <&&> expr

let rec wpComposition (s: Statement, t: Statement) (postcondition: Proposition) =
  wpStatement s (wpStatement t postcondition)
// wp.(if cond0 -> body0 | cond1 -> body1 fi).P = (cond0 ∨ cond1) ∧ (cond0 ⇒ wp.body0.P) ∧ (cond1 ⇒ wp.body1.P)
and wpAlternative (guards: Guard list) (postcondition: Proposition) =
  let conds, bodies =
    guards
    |> List.map (fun g -> g.Condition, g.Condition ==> wpStatement g.Body postcondition)
    |> List.unzip

  let orConds =
    conds.Tail |> List.fold (fun acc c -> acc <||> c) (conds.Head :?> Proposition)

  let andBodies = bodies.Tail |> List.fold (fun acc c -> acc <&&> c) bodies.Head
  orConds <&&> andBodies

// wlp.(do cond0 → body0 | cond1 → body1 od).P = (cond0 ∧ P ⇒ wp.body0.P) ∧ (cond1 ∧ P ⇒ wp.body1.P)
and wlpRepetition (guards: Guard list) (postcondition: Proposition) =
  let bodies =
    guards
    |> List.map (fun g -> g.Condition <&&> postcondition ==> wpStatement g.Body postcondition)

  let andBodies = bodies.Tail |> List.fold (fun acc c -> acc <&&> c) bodies.Head
  andBodies

and wpStatement (s: Statement) (postcondition: Proposition) =
  match s with
  | Becomes becomes -> wpAssignment becomes postcondition
  | Compose(s, t) -> wpComposition (s, t) postcondition
  | If guards -> wpAlternative guards postcondition
  | Do guards -> wlpRepetition guards postcondition
  | Assert expr -> expr ==> postcondition
  | Skip -> postcondition // wp.skip.P = P
  | Abort -> False

type AstSemanticResult =
  | NewVars of Map<string, Type>
  | NewStatement of Statement
  | FailedSemantic of TypingResult

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

  let guardedBlock (constructor: Guard list -> Statement) (guards: AST.Guard list) =
    let oks, errs =
      guards
      |> List.fold
        (fun (oks, errs) g ->
          match makePredicate vars g.Condition with
          | Ok e ->
            match astStatementToSemantic vars g.Body with
            | NewStatement body -> Guard(e, body) :: oks, errs
            | FailedSemantic m -> oks, m :: errs
            | NewVars _ -> oks, errs
          | Error m -> oks, m.SemanticResult :: errs)
        ([], [])

    match errs with
    | [] -> constructor (List.rev oks) |> NewStatement
    | errs -> List.rev errs |> MultipleResults |> FailedSemantic

  match s with
  | AST.VarDecl xs ->
    let addVarType t (acc: Map<string, Type>) name = Map.add name t acc
    let addSameType vars t map = vars |> List.fold (addVarType t) map

    let newVars = xs |> List.fold (fun acc (vars, t) -> addSameType vars t acc) vars
    NewVars newVars
  | AST.Abort -> NewStatement Abort
  | AST.Skip -> NewStatement Skip
  | AST.Assert expr ->
    match makePredicate vars expr with
    | Ok s -> NewStatement(Assert s)
    | Error e -> FailedSemantic e.SemanticResult
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
    | [] -> NewStatement(Becomes oks)
    | [ e ] -> FailedSemantic e
    | _ -> FailedSemantic(MultipleResults errs)
  | AST.Becomes _ -> FailedSemantic MalformedAssignment
  | AST.Do guards -> guardedBlock Do guards
  | AST.If guards -> guardedBlock If guards

let astBlockToSemantic (xs: AST.Statement list) =
  xs
  |> List.fold
    (fun (vars, errs, s) x ->
      match astStatementToSemantic vars x with
      | NewVars newVars -> newVars, errs, s
      | NewStatement r when s.Equals Skip -> vars, errs, r
      | NewStatement r -> vars, errs, Compose(s, r)
      | FailedSemantic e -> vars, e :: errs, s)
    (Map.empty, [], Skip)
