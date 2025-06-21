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
    | TypedDomain(_, []) -> None
    | TypedDomain(_, x :: xs) ->
      xs
      |> List.fold (fun acc x -> ST((Typed WybeType.Boolean, Binary(x.Expr, WybeOp.And, acc.Expr)), [ acc; x ])) x
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

let rec checkChildrenFixedType
  (vars: Map<string, WybeType>)
  (e: Expr, resultType: WybeType)
  (expectedType: WybeType, children: Expr list)
  =
  let xs = children |> List.map (extractSemantics vars)

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
  let xs = children |> List.map (extractSemantics vars)
  let types = xs |> List.choose _.SemanticResult.Type |> Set

  if Set.count types = 1 then
    ST((Typed resultType, e), xs)
  else
    ST((ExpectingSameType(Set.toList types), e), xs)

and extractSemantics (vars: Map<string, WybeType>) (e: Expr) : SemanticTree =
  match e with
  | Binary(left, op, right) ->

    match op with
    | WybeOp.Plus
    | WybeOp.Minus
    | WybeOp.Times -> checkChildrenFixedType vars (e, WybeType.Integer) (WybeType.Integer, [ left; right ])
    | WybeOp.Div ->
      let r =
        checkChildrenFixedType vars (e, WybeType.Integer) (WybeType.Integer, [ left; right ])

      let divDomain = Binary(right, WybeOp.NotEq, Lit(Int 0)) |> extractSemantics vars
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
    | _ ->
      let l, r = extractSemantics vars left, extractSemantics vars right
      ST((NotRecognizedOperator op, e), [ l; r ])
  | Unary(op, right) ->
    match op with
    | WybeOp.Not -> checkChildrenFixedType vars (e, WybeType.Boolean) (WybeType.Boolean, [ right ])
    | WybeOp.UnaryMinus -> checkChildrenFixedType vars (e, WybeType.Integer) (WybeType.Integer, [ right ])
    | WybeOp.Length ->
      checkChildrenFixedType vars (e, WybeType.Integer) (WybeType.Array(WybeType.VarType "a"), [ right ])
    | _ ->
      let r = extractSemantics vars right
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
      let r = extractSemantics vars y
      let rs = ys |> List.map (extractSemantics vars)

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
    | Some t ->
      let indexResult = extractSemantics vars index

      match indexResult with
      | ST((Typed WybeType.Integer, _), _) ->
        let r = ST((Typed t, e), [ indexResult ])

        let arrayDomain =
          Binary(
            Binary(Lit(Int 0), WybeOp.AtMost, index),
            WybeOp.And,
            Binary(index, WybeOp.LessThan, Unary(WybeOp.Length, Var name))
          )
          |> extractSemantics vars

        r.AddDomain arrayDomain
      | _ -> ST((Typed t, e), [ indexResult ])
    | None -> ST((Untyped, e), [])

let rec exprToTree: Expr -> Core.SymbolTree =
  function
  | Binary(left, op, right) ->
    let l = exprToTree left
    let r = exprToTree right

    let opSymbol =
      match op with
      | WybeOp.Plus -> Core.Symbol.Op("+", 5)
      | WybeOp.Minus -> Core.Symbol.Op("-", 5)
      | WybeOp.Times -> Core.Symbol.Op("×", 5)
      | WybeOp.Div -> Core.Symbol.Op("÷", 5)
      | WybeOp.Eq -> Core.Symbol.Op("=", 4)
      | WybeOp.NotEq -> Core.Symbol.Op("≠", 4)
      | WybeOp.AtMost -> Core.Symbol.Op("≤", 4)
      | WybeOp.AtLeast -> Core.Symbol.Op("≥", 4)
      | WybeOp.LessThan -> Core.Symbol.Op("<", 4)
      | WybeOp.Exceeds -> Core.Symbol.Op(">", 4)
      | WybeOp.And -> Core.Symbol.Op("∧", 2)
      | WybeOp.Or -> Core.Symbol.Op("∨", 2)
      | WybeOp.Implies -> Core.Symbol.Op("⇒", 1)
      | WybeOp.Follows -> Core.Symbol.Op("⇐", 1)
      | WybeOp.Equiv -> Core.Symbol.Op("≡", 0)
      | WybeOp.NotEquiv -> Core.Symbol.Op("≢", 0)
      | WybeOp.Not -> Core.Symbol.Op("¬", 3)
      | WybeOp.UnaryMinus -> Core.Symbol.Op("-", 6)
      | WybeOp.Length -> Core.Symbol.Op("#", 6)

    Core.SymbolTree.Node(opSymbol, [ l; r ])
  | Unary(op, inner) ->
    let t = exprToTree inner

    let sym =
      match op with
      | WybeOp.Not -> Core.Symbol.Op("¬", 3)
      | WybeOp.UnaryMinus -> Core.Symbol.Op("-", 6)
      | WybeOp.Length -> Core.Symbol.Op("#", 6)
      | _ -> Core.Symbol.Op(string op, 7)

    Core.SymbolTree.Node(sym, [ t ])
  | Var name -> Core.SymbolTree.Node(Core.Symbol.Var name, [])
  | Lit literal ->
    let txt =
      match literal with
      | Int i -> string i
      | Bool b -> if b then "true" else "false"
      | Str s -> $"\"{s}\""

    Core.SymbolTree.Node(Core.Symbol.Const txt, [])
  | Array elems ->
    let trees = elems |> List.map exprToTree
    let arraySymbol = Core.Symbol.Enclosed("[", "]")

    match List.rev trees with
    | [] -> Core.SymbolTree.Node(arraySymbol, [])
    | x :: xs ->
      let commaTree =
        xs
        |> List.fold (fun acc e -> Core.SymbolTree.Node(Core.Symbol.Op(",", 0), [ e; acc ])) x

      Core.SymbolTree.Node(arraySymbol, [ commaTree ])
  | ArrayElem(name, index) -> Core.SymbolTree.Node(Core.Symbol.Atom name, [ exprToTree index ])
