#r "nuget: Microsoft.Z3.x64"
open Microsoft.Z3

let ctx = new Context()
let x = ctx.MkIntConst "x"
let y = ctx.MkIntConst "y"

// Define the premise: x > 0 && y > 0
let premise = ctx.MkAnd(ctx.MkGt(x, ctx.MkInt 0), ctx.MkGt(y, ctx.MkInt 0))

// Define the conclusion: x + y > 0
let conclusion = ctx.MkGt(ctx.MkAdd(x, y), ctx.MkInt 0)

// Define the implication: premise => conclusion
let implication = ctx.MkImplies(premise, conclusion)

let solver = ctx.MkSolver()

// Add the negation of the implication to the solver
// If the negation is satisfiable, the implication does not hold universally
solver.Add(ctx.MkNot implication)

// Check if the negation of the implication is satisfiable
match solver.Check() with
| Status.SATISFIABLE ->
  printfn "The implication does NOT hold universally."
  printfn "Counterexample:"
  let model = solver.Model
  printfn "x = %s" (model.Evaluate(x).ToString())
  printfn "y = %s" (model.Evaluate(y).ToString())
| Status.UNSATISFIABLE -> printfn "The implication holds universally."
| Status.UNKNOWN -> printfn "The status of the implication is unknown."
| v -> failwith $"unexpected enum valeu {v}"

ctx.Dispose()
