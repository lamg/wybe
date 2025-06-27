#r "nuget: Microsoft.Z3, 4.8.11"
open Microsoft.Z3

let ctx = new Context()

try
  let x = ctx.MkIntConst "x"
  let y = ctx.MkIntConst "y"

  // Define the predicate: x is even and x < 10
  let predicate (n: Microsoft.Z3.IntExpr) =
    ctx.MkAnd(ctx.MkEq(ctx.MkMod(n, ctx.MkInt 2), ctx.MkInt 0), ctx.MkLt(n, ctx.MkInt 10))

  let solver = ctx.MkSolver()

  // 1. Assert that there exists an x that satisfies the predicate
  solver.Add(predicate x)

  // 2. Assert maximality: for any y > x, y does NOT satisfy the predicate
  // This is equivalent to: ForAll y (y > x => Not (predicate y))
  let forAllY =
    ctx.MkForall(
      [| y :> Expr |],
      ctx.MkImplies(ctx.MkGt(y, x), ctx.MkNot(predicate y)),
      1u, // weight (uint32)
      [||], // patterns (empty array)
      [||], // noPatterns (empty array)
      null, // quantifierID (Symbol)
      null
    ) // skolemID (Symbol)

  solver.Add(forAllY)

  // Check if the assertions are satisfiable
  match solver.Check() with
  | Status.SATISFIABLE ->
    printfn "Found a maximum element:"
    let model = solver.Model
    printfn "x = %s" (model.Evaluate(x).ToString())
  | Status.UNSATISFIABLE -> printfn "No such maximum element exists (or the constraints are contradictory)."
  | Status.UNKNOWN ->
    printfn "Z3 could not determine satisfiability."
    printfn "Reason: %s" (solver.ReasonUnknown)
  | v -> failwith $"unexpected enum value {v}"

finally
  ctx.Dispose()
  ctx.Dispose()
