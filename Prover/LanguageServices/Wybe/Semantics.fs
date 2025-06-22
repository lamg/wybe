module LanguageServices.Wybe.Semantics

open AST

type Expected =
  { expected: WybeType
    got: SemanticResult
    atChild: int }

and SemanticResult =
  | Typed of WybeType
  | TypedDomain of WybeType * domain: SemanticTree list
  | Expecting of Expected list
  | ExpectingSameType of got: WybeType list
  | NotRecognizedOperator of WybeOp
  | NotFoundVar of string
  | Untyped

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
        |> List.fold (fun acc x -> ST((Typed WybeType.Boolean, Binary(x.Expr, WybeOp.And, acc.Expr)), [ acc; x ])) y
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
  (vars: Map<string, WybeType>)
  (e: Expr, resultType: WybeType)
  (expectedType: WybeType, children: Expr list)
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
    | [] -> ST((Typed resultType, e), xs)
    | rs -> ST((Expecting rs, e), xs)

and checkChildrenEqualType (vars: Map<string, WybeType>) (e: Expr, resultType: WybeType) (children: Expr list) =
  let xs = children |> List.map (extractTypeAndDomain vars)
  let types = xs |> List.choose _.SemanticResult.Type |> Set

  if Set.count types = 1 then
    ST((Typed resultType, e), xs)
  else
    ST((ExpectingSameType(Set.toList types), e), xs)

and extractTypeAndDomain (vars: Map<string, WybeType>) (e: Expr) : SemanticTree =
  match e with
  | Binary(left, op, right) ->

    match op with
    | WybeOp.Plus
    | WybeOp.Minus
    | WybeOp.Times -> checkChildrenFixedType vars (e, WybeType.Integer) (WybeType.Integer, [ left; right ])
    | WybeOp.Div ->
      let r =
        checkChildrenFixedType vars (e, WybeType.Integer) (WybeType.Integer, [ left; right ])

      let divDomain = Binary(right, WybeOp.NotEq, Lit(Int 0)) |> extractTypeAndDomain vars
      r.AddDomain divDomain
    | WybeOp.Eq
    | WybeOp.NotEq -> checkChildrenEqualType vars (e, WybeType.Boolean) [ left; right ]
    | WybeOp.AtMost
    | WybeOp.AtLeast
    | WybeOp.LessThan
    | WybeOp.Exceeds -> checkChildrenFixedType vars (e, WybeType.Boolean) (WybeType.Integer, [ left; right ])
    | WybeOp.Equiv
    | WybeOp.NotEquiv
    | WybeOp.And
    | WybeOp.Or
    | WybeOp.Implies
    | WybeOp.Follows -> checkChildrenFixedType vars (e, WybeType.Boolean) (WybeType.Integer, [ left; right ])
    | WybeOp.Cons ->
      let l, r = extractTypeAndDomain vars left, extractTypeAndDomain vars right

      match l.SemanticResult.Type, r.SemanticResult.Type with
      | Some t, Some(WybeType.Array u) when u = t -> ST((Typed(WybeType.Array t), e), [ l; r ])
      | _ -> ST((NotRecognizedOperator op, e), [ l; r ])
    | WybeOp.Concat ->
      let l, r = extractTypeAndDomain vars left, extractTypeAndDomain vars right

      match l.SemanticResult.Type, r.SemanticResult.Type with
      | Some(WybeType.Array t), Some(WybeType.Array u) when u = t -> ST((Typed(WybeType.Array t), e), [ l; r ])
      | _ -> ST((NotRecognizedOperator op, e), [ l; r ])
    | WybeOp.IsPrefix
    | WybeOp.IsSuffix ->
      checkChildrenFixedType vars (e, WybeType.Boolean) (WybeType.Array(WybeType.VarType "a"), [ left; right ])
    | _ ->
      let l, r = extractTypeAndDomain vars left, extractTypeAndDomain vars right
      ST((NotRecognizedOperator op, e), [ l; r ])
  | Unary(op, right) ->
    match op with
    | WybeOp.Not -> checkChildrenFixedType vars (e, WybeType.Boolean) (WybeType.Boolean, [ right ])
    | WybeOp.UnaryMinus -> checkChildrenFixedType vars (e, WybeType.Integer) (WybeType.Integer, [ right ])
    | WybeOp.Length ->
      checkChildrenFixedType vars (e, WybeType.Integer) (WybeType.Array(WybeType.VarType "a"), [ right ])
    | WybeOp.Head ->
      let r = extractTypeAndDomain vars right

      match r.SemanticResult.Type with
      | Some(WybeType.Array t) -> ST((Typed t, e), [ r ])
      | _ -> ST((NotRecognizedOperator op, e), [ r ])
    | WybeOp.Tail ->
      let r = extractTypeAndDomain vars right

      match r.SemanticResult.Type with
      | Some(WybeType.Array t) -> ST((Typed(WybeType.Array t), e), [ r ])
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
    | Int _ -> ST((Typed WybeType.Integer, e), [])
    | Bool _ -> ST((Typed WybeType.Boolean, e), [])
    | Str _ -> ST((Typed WybeType.String, e), [])
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
        | [] -> ST((Typed(WybeType.Array t), e), r :: rs)
        | _ -> ST((Expecting diffElemTypes, e), r :: rs)
      | ST((v, _), _) -> ST((v, e), r :: rs)
  | ArrayElem(name, index) ->
    match Map.tryFind name vars with
    | Some(WybeType.Array t) ->
      let indexResult = extractTypeAndDomain vars index

      match indexResult with
      | ST((TypedDomain(WybeType.Integer, _), _), _)
      | ST((Typed WybeType.Integer, _), _) ->
        let domain = indexResult.SemanticResult.Domain |> Option.toList
        let r = ST((TypedDomain(t, domain), e), [ indexResult ])

        let arrayDomain =
          Binary(
            Binary(Lit(Int 0), WybeOp.AtMost, index),
            WybeOp.And,
            Binary(index, WybeOp.LessThan, Unary(WybeOp.Length, Var name))
          )
          |> extractTypeAndDomain vars

        r.AddDomain arrayDomain
      | _ -> ST((Typed t, e), [ indexResult ])
    | Some t ->
      ST(
        (Expecting
          [ { expected = WybeType.Array(WybeType.VarType "a")
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
      | WybeOp.Plus -> Symbol.Op("+", 5)
      | WybeOp.Minus -> Symbol.Op("-", 5)
      | WybeOp.Times -> Symbol.Op("×", 5)
      | WybeOp.Div -> Symbol.Op("÷", 5)
      | WybeOp.Eq -> Symbol.Op("=", 4)
      | WybeOp.NotEq -> Symbol.Op("≠", 4)
      | WybeOp.AtMost -> Symbol.Op("≤", 4)
      | WybeOp.AtLeast -> Symbol.Op("≥", 4)
      | WybeOp.LessThan -> Symbol.Op("<", 4)
      | WybeOp.Exceeds -> Symbol.Op(">", 4)
      | WybeOp.And -> Symbol.Op("∧", 2)
      | WybeOp.Or -> Symbol.Op("∨", 2)
      | WybeOp.Implies -> Symbol.Op("⇒", 1)
      | WybeOp.Follows -> Symbol.Op("⇐", 1)
      | WybeOp.Equiv -> Symbol.Op("≡", 0)
      | WybeOp.NotEquiv -> Symbol.Op("≢", 0)
      | WybeOp.Not -> Symbol.Op("¬", 3)
      | WybeOp.UnaryMinus -> Symbol.Op("-", 6)
      | WybeOp.Length -> Symbol.Op("#", 6)
      | WybeOp.HasType -> Symbol.Op(":", 0)
      | WybeOp.Cons -> Symbol.Op("::", 6)
      | WybeOp.Concat -> Symbol.Op("++", 6)
      | WybeOp.IsPrefix -> Symbol.Op("◁", 6)
      | WybeOp.IsSuffix -> Symbol.Op("▷", 6)
      | _ -> failwith $"unexpected binary operator {op}"

    SymbolTree.Node(opSymbol, [ l; r ])
  | Unary(op, inner) ->
    let t = exprToTree inner

    let sym =
      match op with
      | WybeOp.Not -> Symbol.Op("¬", 3)
      | WybeOp.UnaryMinus -> Symbol.Op("-", 6)
      | WybeOp.Length -> Symbol.Op("#", 6)
      | WybeOp.Head -> Symbol.Atom "head"
      | WybeOp.Tail -> Symbol.Atom "tail"
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


let collectSemanticTreeInfo (e: SemanticTree) : string list =
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

type DomainWExpr = DomainWExpr of domain: WExpr option * expr: WExpr

let semanticExprToWExpr (e: SemanticTree) : DomainWExpr option =
  let rec typedToWExpr (e: SemanticTree) : WExpr option =
    match e.SemanticResult.Type with
    | Some WybeType.Boolean ->
      match e.Expr, e.Children with
      | Binary(_, WybeOp.And, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some(a <&&> b)
        | _ -> None
      | Binary(_, WybeOp.Or, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some(a <||> b)
        | _ -> None
      | Binary(_, WybeOp.Implies, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some(a ==> b)
        | _ -> None
      | Binary(_, WybeOp.Follows, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some(a <== b)
        | _ -> None
      | Binary(_, WybeOp.Equiv, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some(a === b)
        | _ -> None
      | Binary(_, WybeOp.NotEquiv, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some(a !== b)
        | _ -> None
      | Binary(_, WybeOp.Eq, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some(Core.Equals(a, b))
        | _ -> None
      | Binary(_, WybeOp.NotEq, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some(a != b)
        | _ -> None
      | Binary(_, WybeOp.AtMost, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some(a <= b)
        | _ -> None
      | Binary(_, WybeOp.AtLeast, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some((a :?> Integer) >= (b :?> Integer))
        | _ -> None
      | Binary(_, WybeOp.LessThan, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some((a :?> Integer) < (b :?> Integer))
        | _ -> None
      | Binary(_, WybeOp.Exceeds, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some((a :?> Integer) > (b :?> Integer))
        | _ -> None
      | Binary(_, WybeOp.IsPrefix, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some lW, Some rW -> Some(IsPrefix(lW :?> Sequence, rW :?> Sequence) :> WExpr)
        | _ -> None
      | Binary(_, WybeOp.IsSuffix, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some lW, Some rW -> Some(IsSuffix(lW :?> Sequence, rW :?> Sequence) :> WExpr)
        | _ -> None
      | Unary(WybeOp.Not, _), [ c ] ->
        match typedToWExpr c with
        | Some a -> Some(!a)
        | None -> None
      | Lit(Bool b), [] -> Some(if b then True else False)
      | Expr.Var name, [] -> Some(mkBoolVar name)
      | _ -> failwith $"not implemented: {exprToTree e.Expr}"
    | Some WybeType.Integer ->
      match e.Expr, e.Children with
      | Lit(Int i), [] -> Some(Integer i)
      | Unary(WybeOp.UnaryMinus, _), [ c ] ->
        match typedToWExpr c with
        | Some a -> Some(-(a :?> Integer))
        | None -> None
      | Unary(WybeOp.Length, _), [ c ] ->
        match typedToWExpr c with
        | Some a -> Some(len a)
        | None -> None
      | Binary(_, WybeOp.Plus, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some((a :?> Integer) + (b :?> Integer) :> WExpr)
        | _ -> None
      | Binary(_, WybeOp.Minus, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some((a :?> Integer) - (b :?> Integer) :> WExpr)
        | _ -> None
      | Binary(_, WybeOp.Times, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some((a :?> Integer) * (b :?> Integer) :> WExpr)
        | _ -> None
      | Binary(_, WybeOp.Div, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some((a :?> Integer) / (b :?> Integer) :> WExpr)
        | _ -> None
      | Expr.Var name, [] -> Some(mkIntVar name)
      | _ -> failwith $"not implemented: {exprToTree e.Expr}"
    | Some(WybeType.Array inner) ->
      // sequence operations and literals for integer or boolean sequences
      match e.Expr, e.Children with
      // literal array
      | Array _, elemsST ->
        let elems = elemsST |> List.map typedToWExpr

        if List.exists Option.isNone elems then
          None
        else
          let ws = elems |> List.map Option.get

          let seqSort =
            match inner with
            | WybeType.Integer -> WSeq WInt
            | WybeType.Boolean -> WSeq WBool
            | _ -> failwith $"unsupported sequence element type: {inner}"

          let seqW = List.rev ws |> List.fold (fun acc v -> Cons(v, acc)) (Empty seqSort)
          Some(seqW :> WExpr)
      // cons operator
      | Binary(_, WybeOp.Cons, _), [ lST; rST ] ->
        match typedToWExpr lST, typedToWExpr rST with
        | Some v, Some s -> Some(Cons(v, s :?> Sequence) :> WExpr)
        | _ -> None
      // concat operator
      | Binary(_, WybeOp.Concat, _), [ lST; rST ] ->
        match typedToWExpr lST, typedToWExpr rST with
        | Some lW, Some rW -> Some(Concat(lW :?> Sequence, rW :?> Sequence) :> WExpr)
        | _ -> None
      // head and tail
      | Unary(WybeOp.Head, _), [ cST ] ->
        match typedToWExpr cST with
        | Some s -> Some(Head(s :?> Sequence) :> WExpr)
        | None -> None
      | Unary(WybeOp.Tail, _), [ cST ] ->
        match typedToWExpr cST with
        | Some s -> Some(Tail(s :?> Sequence) :> WExpr)
        | None -> None
      | _ -> failwith $"not implemented sequence op: {exprToTree e.Expr}"
    | None -> None
    | _ -> None

  let domain = e.SemanticResult.Domain |> Option.bind typedToWExpr
  typedToWExpr e |> Option.map (fun r -> DomainWExpr(domain, r))
