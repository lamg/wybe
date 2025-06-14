module LanguageServices.Compact.TypeChecker

open AST
exception TypeError of string

type TcEnv =
  { variables: Map<Identifier, CompactType>
    functions: Map<Identifier, Signature>
    enums: Map<Identifier, Identifier list> }

let private fail msg = raise (TypeError msg)

let rec private equalTypes t1 t2 =
  match t1, t2 with
  | Void, Void -> true
  | NamedType(n1, ps1), NamedType(n2, ps2) when n1 = n2 && List.length ps1 = List.length ps2 ->
    List.forall2 equalTypeParam ps1 ps2
  | _ -> false

and private equalTypeParam p1 p2 =
  match p1, p2 with
  | TypeParamInt i1, TypeParamInt i2 -> i1 = i2
  | CompactTypeParam t1, CompactTypeParam t2 -> equalTypes t1 t2
  | _ -> false

let private typeOfLiteral =
  function
  | Int _ -> NamedType([ "int" ], [])
  | Bool _ -> NamedType([ "bool" ], [])
  | Str _ -> NamedType([ "string" ], [])

let rec private typeOfExpr (env: TcEnv) (expr: Expr) : CompactType =
  match expr with
  | Var id ->
    match env.variables.TryFind id with
    | Some t -> t
    | None -> fail "Unbound variable %A" id
  | Lit lit -> typeOfLiteral lit
  | Version _ -> NamedType([ "version" ], [])
  | Unary(op, x) ->
    let tx = typeOfExpr env x in

    match op with
    | CompactOp.Not when equalTypes tx (NamedType([ "bool" ], [])) -> NamedType([ "bool" ], [])
    | _ -> fail "Invalid operand type %A for unary '%s'" tx op
  | Binary(l, op, r) ->
    let tl = typeOfExpr env l
    let tr = typeOfExpr env r in

    match op with
    | CompactOp.Times
    | CompactOp.Div
    | CompactOp.Plus
    | CompactOp.Minus ->
      if
        equalTypes tl (NamedType([ "int" ], []))
        && equalTypes tr (NamedType([ "int" ], []))
      then
        NamedType([ "int" ], [])
      else
        fail "Operator '%s' requires int operands, got %A and %A" op tl tr
    | CompactOp.And
    | CompactOp.Or ->
      if
        equalTypes tl (NamedType([ "bool" ], []))
        && equalTypes tr (NamedType([ "bool" ], []))
      then
        NamedType([ "bool" ], [])
      else
        fail "Operator '%s' requires bool operands, got %A and %A" op tl tr
    | CompactOp.NotEq ->
      if equalTypes tl tr then
        NamedType([ "bool" ], [])
      else
        fail "Cannot compare differing types %A and %A" tl tr
    | CompactOp.Lt
    | CompactOp.Gt
    | CompactOp.Lte
    | CompactOp.Gte ->
      if
        equalTypes tl (NamedType([ "int" ], []))
        && equalTypes tr (NamedType([ "int" ], []))
      then
        NamedType([ "bool" ], [])
      else
        fail "Operator '%s' requires int operands, got %A and %A" op tl tr
    | _ -> fail "Unknown binary operator '%s'" op
  | MemberAccess(e, fld) ->
    let te = typeOfExpr env e in

    match te with
    | NamedType(name, _) ->
      match env.enums.TryFind name with
      | Some members when List.exists ((=) fld) members -> NamedType(name, [])
      | Some _ -> fail "Unknown member %A of enum %A" fld name
      | None -> fail "Type %A is not an enum" name
    | _ -> fail "Cannot access member %A on non-enum type %A" fld te
  | IndexAccess(a, i) ->
    let ta = typeOfExpr env a
    let ti = typeOfExpr env i in

    if not (equalTypes ti (NamedType([ "int" ], []))) then
      fail "Index must be int, got %A" ti

    match ta with
    | NamedType(_, ps) ->
      match
        List.tryPick
          (function
          | CompactTypeParam t -> Some t
          | _ -> None)
          ps
      with
      | Some elem -> elem
      | None -> fail "Type %A is not indexable" ta
    | _ -> fail "Type %A is not indexable" ta
  | Array elems ->
    let types = List.map (typeOfExpr env) elems in

    match types with
    | [] -> fail "Cannot infer type of empty array literal"
    | t0 :: ts ->
      for t in ts do
        if not (equalTypes t0 t) then
          fail "Array literal has mismatched types %A and %A" t0 t

      let len = List.length types in
      NamedType(compactArrayTypeId, [ TypeParamInt len; CompactTypeParam t0 ])
  | Call(id, _typeArgs, args) ->
    let fsig =
      match env.functions.TryFind id with
      | Some s -> s
      | None -> fail $"Unknown function {id}"

    if List.length args <> List.length fsig.args then
      fail $"Function {id} expects {List.length fsig.args} args but got {List.length args}"

    List.iter2
      (fun param arg ->
        let ta = typeOfExpr env arg in

        if not (equalTypes ta param.paramType) then
          fail $"Function {id} argument '{param.paramName}' expects {param.paramType} but got {ta}")
      fsig.args
      args

    fsig.returnType
  | Cast(tname, e) -> let _ = typeOfExpr env e in NamedType([ tname ], [])
  | As(varId, ctype) ->
    let _ =
      match env.variables.TryFind varId with
      | Some _ -> ()
      | None -> fail "Unbound variable in cast: %A" varId

    ctype

let rec private typeCheckStmt (env: TcEnv) (retType: CompactType) (stmt: Statement) : TcEnv =
  match stmt with
  | Const(name, expr) ->
    let t = typeOfExpr env expr in

    { env with
        variables = env.variables.Add(name, t) }
  | Assign(target, expr) ->

    let tTarget = typeOfExpr env target
    let tExpr = typeOfExpr env expr in

    if not (equalTypes tTarget tExpr) then
      fail $"Assign type mismatch: {tTarget} := {tExpr}"

    env
  | If(cond, thenB, elseB) ->
    let tc = typeOfExpr env cond in

    if not (equalTypes tc (NamedType([ "bool" ], []))) then
      fail $"If condition must be bool, got {tc}"

    thenB |> List.iter (fun s -> ignore (typeCheckStmt env retType s))

    match elseB with
    | Some bs -> bs |> List.iter (fun s -> ignore (typeCheckStmt env retType s))
    | None -> ()

    env
  | For(i, lo, hiOpt, body) ->
    let tLo = typeOfExpr env lo in

    let elemType =
      match hiOpt with
      | Some hi ->
        let tHi = typeOfExpr env hi in

        if
          not (equalTypes tLo (NamedType([ "int" ], [])))
          || not (equalTypes tHi (NamedType([ "int" ], [])))
        then
          fail $"For range bounds must be int, got {tLo} and {tHi}"

        NamedType([ "int" ], [])
      | None ->
        match tLo with
        | NamedType(_, ps) ->
          (match
            List.tryPick
              (function
              | CompactTypeParam t -> Some t
              | _ -> None)
              ps
           with
           | Some e -> e
           | None -> fail $"Cannot iterate over non-indexable type {tLo}")
        | _ -> fail $"Cannot iterate over non-indexable type {tLo}"

    let env' =
      { env with
          variables = env.variables.Add(i, elemType) } in

    body |> List.iter (fun s -> ignore (typeCheckStmt env' retType s))
    env
  | Return exprOpt ->
    (match exprOpt with
     | Some e ->
       let te = typeOfExpr env e in

       if not (equalTypes te retType) then
         fail $"Return type mismatch: expected {retType} but got {te}"
     | None ->
       if not (equalTypes retType Void) then
         fail $"Return without value in non-void function {retType}")

    env
  | CallStatement e ->
    let te = typeOfExpr env e in

    if not (equalTypes te Void) then
      fail $"Call statement must be void, got {te}"

    env

let private mkEnv (program: Program) : TcEnv =
  let ledgerVars =
    program
    |> List.choose (function
      | Ledger(_, p) -> Some(p.paramName, p.paramType)
      | _ -> None)
    |> Map.ofList

  let enumDefs =
    program
    |> List.choose (function
      | Enum(_, name, members) -> Some(name, members)
      | _ -> None)
    |> Map.ofList

  let funcSigs =
    program
    |> List.choose (function
      | Circuit(_, name, sigt, _) -> Some(name, sigt)
      | Witness(_, name, sigt) -> Some(name, sigt)
      | _ -> None)
    |> Map.ofList

  { variables = ledgerVars
    functions = funcSigs
    enums = enumDefs }

let check (program: Program) : unit =
  let env = mkEnv program

  program
  |> List.iter (function
    | Constructor(args, body) ->
      let env0 =
        List.fold
          (fun e p ->
            { e with
                variables = e.variables.Add(p.paramName, p.paramType) })
          env
          args in

      body |> List.fold (fun e stmt -> typeCheckStmt e Void stmt) env0 |> ignore
    | _ -> ())

  program
  |> List.iter (function
    | Circuit(_, _, sigt, body) ->
      let env0 =
        List.fold
          (fun e p ->
            { e with
                variables = e.variables.Add(p.paramName, p.paramType) })
          env
          sigt.args in

      body
      |> List.fold (fun e stmt -> typeCheckStmt e sigt.returnType stmt) env0
      |> ignore
    | _ -> ())

/// Compute a map from function names to maps of expressions in their bodies to their inferred types.
let exprTypesByFunction
  (inheritedEnv: TcEnv)
  (program: Program)
  : Map<string, Statement list * Map<Expr, CompactType>> =
  let env = mkEnv program

  let env =
    { enums = Map.toList inheritedEnv.enums @ Map.toList env.enums |> Map.ofList
      functions = Map.toList inheritedEnv.functions @ Map.toList env.functions |> Map.ofList
      variables = Map.toList inheritedEnv.variables @ Map.toList env.variables |> Map.ofList }

  let rec collectExprs (expr: Expr) : Expr list =
    expr
    :: (match expr with
        | Var _
        | Lit _
        | Version _ -> []
        | Unary(_, e) -> collectExprs e
        | Binary(l, _, r) -> collectExprs l @ collectExprs r
        | MemberAccess(e, _) -> collectExprs e
        | IndexAccess(a, i) -> collectExprs a @ collectExprs i
        | Array elems -> elems |> List.collect collectExprs
        | Call(_, _, args) -> args |> List.collect collectExprs
        | Cast(_, e) -> collectExprs e
        | As(_, _) -> [])

  let rec collectStmtExprs (stmt: Statement) : Expr list =
    match stmt with
    | Const(_, expr) -> collectExprs expr
    | Assign(tgt, expr) -> collectExprs tgt @ collectExprs expr
    | If(cond, thenB, elseBOpt) ->
      collectExprs cond
      @ (thenB |> List.collect collectStmtExprs)
      @ (match elseBOpt with
         | Some bs -> bs |> List.collect collectStmtExprs
         | None -> [])
    | For(_, lo, hiOpt, body) ->
      collectExprs lo
      @ (match hiOpt with
         | Some hi -> collectExprs hi
         | None -> [])
      @ (body |> List.collect collectStmtExprs)
    | Return exprOpt ->
      (match exprOpt with
       | Some e -> collectExprs e
       | None -> [])
    | CallStatement e -> collectExprs e

  program
  |> List.choose (function
    | Circuit(_, name, sigt, body) ->
      let key = String.concat "." name

      let env0 =
        sigt.args
        |> List.fold
          (fun e p ->
            { e with
                variables = e.variables.Add(p.paramName, p.paramType) })
          env

      let exprs = body |> List.collect collectStmtExprs |> List.distinct
      let mapping = exprs |> List.map (fun e -> e, typeOfExpr env0 e) |> Map.ofList
      Some(key, (body, mapping))
    | Witness(_, name, sigt) ->
      let key = String.concat "." name

      let _env0 =
        sigt.args
        |> List.fold
          (fun e p ->
            { e with
                variables = e.variables.Add(p.paramName, p.paramType) })
          env

      Some(key, ([], Map.empty))
    | _ -> None)
  |> Map.ofList
