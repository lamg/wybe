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
    | [] -> ST((Typed resultType, e), xs)
    | rs -> ST((Expecting rs, e), xs)

and checkChildrenEqualType (vars: Map<string, Type>) (e: Expr, resultType: Type) (children: Expr list) =
  let xs = children |> List.map (extractTypeAndDomain vars)
  let types = xs |> List.choose _.SemanticResult.Type |> Set

  if Set.count types = 1 then
    ST((Typed resultType, e), xs)
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

      let divDomain = Binary(right, Op.Differs, Lit(Int 0)) |> extractTypeAndDomain vars
      r.AddDomain divDomain
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

type DomainWExpr =
  | DomainWExpr of domain: WExpr option * expr: WExpr

  member this.Expr =
    let (DomainWExpr(_, expr)) = this
    expr

  member this.Domain =
    let (DomainWExpr(domain, _)) = this
    domain

let semanticExprToWExpr (e: SemanticTree) : DomainWExpr option =
  let rec typedToWExpr (e: SemanticTree) : WExpr option =
    match e.SemanticResult.Type with
    | Some Type.Boolean ->
      match e.Expr, e.Children with
      | Binary(_, Op.And, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some(a <&&> b)
        | _ -> None
      | Binary(_, Op.Or, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some(a <||> b)
        | _ -> None
      | Binary(_, Op.Implies, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some(a ==> b)
        | _ -> None
      | Binary(_, Op.Follows, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some(a <== b)
        | _ -> None
      | Binary(_, Op.Equiv, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some(a === b)
        | _ -> None
      | Binary(_, Op.Inequiv, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some(a !== b)
        | _ -> None
      | Binary(_, Op.Equals, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some(Core.Equals(a, b))
        | _ -> None
      | Binary(_, Op.Differs, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some(a != b)
        | _ -> None
      | Binary(_, Op.AtMost, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some(a <= b)
        | _ -> None
      | Binary(_, Op.AtLeast, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some((a :?> Integer) >= (b :?> Integer))
        | _ -> None
      | Binary(_, Op.LessThan, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some((a :?> Integer) < (b :?> Integer))
        | _ -> None
      | Binary(_, Op.Exceeds, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some((a :?> Integer) > (b :?> Integer))
        | _ -> None
      | Binary(_, Op.IsPrefix, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some lW, Some rW -> Some(IsPrefix(lW :?> Sequence, rW :?> Sequence) :> WExpr)
        | _ -> None
      | Binary(_, Op.IsSuffix, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some lW, Some rW -> Some(IsSuffix(lW :?> Sequence, rW :?> Sequence) :> WExpr)
        | _ -> None
      | Unary(Op.Not, _), [ c ] ->
        match typedToWExpr c with
        | Some a -> Some(!a)
        | None -> None
      | Lit(Bool b), [] -> Some(if b then True else False)
      | Expr.Var name, [] -> Some(mkBoolVar name)
      | _ -> failwith $"not implemented: {exprToTree e.Expr}"
    | Some Type.Integer ->
      match e.Expr, e.Children with
      | Lit(Int i), [] -> Some(Integer i)
      | Unary(Op.UnaryMinus, _), [ c ] ->
        match typedToWExpr c with
        | Some a -> Some(-(a :?> Integer))
        | None -> None
      | Unary(Op.Length, _), [ c ] ->
        match typedToWExpr c with
        | Some a -> Some(len a)
        | None -> None
      | Binary(_, Op.Plus, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some((a :?> Integer) + (b :?> Integer) :> WExpr)
        | _ -> None
      | Binary(_, Op.Minus, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some((a :?> Integer) - (b :?> Integer) :> WExpr)
        | _ -> None
      | Binary(_, Op.Times, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some((a :?> Integer) * (b :?> Integer) :> WExpr)
        | _ -> None
      | Binary(_, Op.Div, _), [ l; r ] ->
        match typedToWExpr l, typedToWExpr r with
        | Some a, Some b -> Some((a :?> Integer) / (b :?> Integer) :> WExpr)
        | _ -> None
      | Expr.Var name, [] -> Some(mkIntVar name)
      | _ -> failwith $"not implemented: {exprToTree e.Expr}"
    | Some(Type.Array inner) ->
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
            | Type.Integer -> WSeq WInt
            | Type.Boolean -> WSeq WBool
            | _ -> failwith $"unsupported sequence element type: {inner}"

          let seqW = List.rev ws |> List.fold (fun acc v -> Cons(v, acc)) (Empty seqSort)
          Some(seqW :> WExpr)
      // cons operator
      | Binary(_, Op.Cons, _), [ lST; rST ] ->
        match typedToWExpr lST, typedToWExpr rST with
        | Some v, Some s -> Some(Cons(v, s :?> Sequence) :> WExpr)
        | _ -> None
      // concat operator
      | Binary(_, Op.Concat, _), [ lST; rST ] ->
        match typedToWExpr lST, typedToWExpr rST with
        | Some lW, Some rW -> Some(Concat(lW :?> Sequence, rW :?> Sequence) :> WExpr)
        | _ -> None
      // head and tail
      | Unary(Op.Head, _), [ cST ] ->
        match typedToWExpr cST with
        | Some s -> Some(Head(s :?> Sequence) :> WExpr)
        | None -> None
      | Unary(Op.Tail, _), [ cST ] ->
        match typedToWExpr cST with
        | Some s -> Some(Tail(s :?> Sequence) :> WExpr)
        | None -> None
      | _ -> failwith $"not implemented sequence op: {exprToTree e.Expr}"
    | None -> None
    | _ -> None

  let domain = e.SemanticResult.Domain |> Option.bind typedToWExpr
  typedToWExpr e |> Option.map (fun r -> DomainWExpr(domain, r))
