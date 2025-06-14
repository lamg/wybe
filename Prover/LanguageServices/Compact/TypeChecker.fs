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
    | None ->
      // enum type or member lookup, e.g. State or State.set
      match env.enums |> Map.tryPick (fun enumName members ->
        if enumName = id then Some enumName
        else if members |> List.exists (fun m -> enumName @ m = id) then Some enumName
        else None) with
      | Some enumName -> NamedType(enumName, [])
      | None -> fail $"Unbound variable {id}"
  | Lit lit -> typeOfLiteral lit
  | Version _ -> NamedType([ "version" ], [])
  | Unary(op, x) ->
    let tx = typeOfExpr env x in

    match op with
    | CompactOp.Not when equalTypes tx (NamedType([ "bool" ], [])) -> NamedType([ "bool" ], [])
    | _ -> fail $"Invalid operand type {tx} for unary '{op}'"
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
        fail $"Operator '{op}' requires int operands, got {tl} and {tr}"
    | CompactOp.And
    | CompactOp.Or ->
      if
        equalTypes tl (NamedType([ "bool" ], []))
        && equalTypes tr (NamedType([ "bool" ], []))
      then
        NamedType([ "bool" ], [])
      else
        fail $"Operator '{op}' requires bool operands, got {tl} and {tr}"
    | CompactOp.Eq
    | CompactOp.NotEq ->
      if equalTypes tl tr then
        NamedType([ "bool" ], [])
      else
        fail $"Cannot compare differing types {tl} and {tr}"
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
        fail $"Operator '{op}' requires int operands, got {tl} and {tr}"
    | _ -> fail $"Unknown binary operator '{op}'"
  | MemberAccess(e, fld) ->
    let te = typeOfExpr env e in

    match te with
    | NamedType(name, _) ->
      match env.enums.TryFind name with
      | Some members when List.exists ((=) fld) members -> NamedType(name, [])
      | Some _ -> fail $"Unknown member {fld} of enum {name}"
      | None -> fail $"Type {name} is not an enum"
    | _ -> fail $"Cannot access member {fld} on non-enum type {te}"
  | IndexAccess(a, i) ->
    let ta = typeOfExpr env a
    let ti = typeOfExpr env i in

    if not (equalTypes ti (NamedType([ "int" ], []))) then
      fail $"Index must be int, got {ti}"

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
      | None -> fail $"Type {ta} is not indexable"
    | _ -> fail $"Type {ta} is not indexable"
  | Array elems ->
    let types = List.map (typeOfExpr env) elems in

    match types with
    | [] -> fail "Cannot infer type of empty array literal"
    | t0 :: ts ->
      for t in ts do
          if not (equalTypes t0 t) then
            fail $"Array literal has mismatched types {t0} and {t}"

      let len = List.length types in
      NamedType(compactVector, [ TypeParamInt len; CompactTypeParam t0 ])
  | Call(id, _typeArgs, args) ->
    let fsig =
      match env.functions.TryFind id with
      | Some s -> s
      | None -> fail $"Unknown function {id}"

    if List.length args <> List.length fsig.args then
      fail $"Function {id} expects {List.length fsig.args} args but got {List.length args}"

    // Recurse into argument expressions, but do not enforce their exact types for semantic extraction
    do args |> List.iter (fun e -> ignore (typeOfExpr env e))
    fsig.returnType
  | Cast(tname, e) -> let _ = typeOfExpr env e in NamedType([ tname ], [])
  | As(varId, ctype) ->
    let _ =
      match env.variables.TryFind varId with
      | Some _ -> ()
      | None -> fail $"Unbound variable in cast: {varId}"

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

  // Expose enum types and their members as variables:
  // - The enum name itself (State) as type NamedType(name, [])
  // - Each member (State.set) as NamedType(name, [])
  let enumTypeVars =
    enumDefs
    |> Map.toList
    |> List.map (fun (name, _) -> (name, NamedType(name, [])))
    |> Map.ofList
  let enumMemberVars =
    enumDefs
    |> Map.toList
    |> List.collect (fun (name, members) ->
         members |> List.map (fun m -> (name @ m, NamedType(name, []))))
    |> Map.ofList

  let vars =
    Map.toList ledgerVars
    @ Map.toList enumTypeVars
    @ Map.toList enumMemberVars
    |> Map.ofList

  { variables = vars
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

  // Combine inherited and program enums/functions/variables
  let env =
    { enums = Map.ofList (Map.toList inheritedEnv.enums @ Map.toList env.enums)
      functions = Map.ofList (Map.toList inheritedEnv.functions @ Map.toList env.functions)
      variables = Map.ofList (Map.toList inheritedEnv.variables @ Map.toList env.variables) }

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

      // Incorporate local 'const' declarations into the environment so subsequent expressions can refer to them
      let varEnv =
        body
        |> List.fold (fun e stmt ->
             match stmt with
             | Const(name, expr) ->
               let t = typeOfExpr e expr in
               { e with variables = e.variables.Add(name, t) }
             | _ -> e)
          env0
      let exprs = body |> List.collect collectStmtExprs |> List.distinct
      let mapping = exprs |> List.map (fun e -> e, typeOfExpr varEnv e) |> Map.ofList
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
