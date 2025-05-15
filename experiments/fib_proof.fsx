// fib_proof.fsx
#r "nuget: Microsoft.Z3,4.8.11"
open Microsoft.Z3

// 1) Create Z3 context (with model generation on)
let cfg = System.Collections.Generic.Dictionary()
cfg.Add("model", "true")
let ctx = new Context(cfg)
// 2) Declare fibonacci : Int -> Int
let intS = ctx.IntSort :> Sort
let fibDecl = ctx.MkFuncDecl("fibonacci", [| intS |], intS)
(* 3) Build the recurrence axiom: ∀ n. fib(n) + fib(n+1) = fib(n+2)
   using a bound variable for pattern instantiation *)
let bv = ctx.MkBound(0u, intS) :?> IntExpr
let fib_bv = fibDecl.Apply [| bv :> Expr |] :?> IntExpr
let fib_bv1 = fibDecl.Apply [| ctx.MkAdd(bv, ctx.MkInt 1) :> Expr |] :?> IntExpr
let fib_bv2 = fibDecl.Apply [| ctx.MkAdd(bv, ctx.MkInt 2) :> Expr |] :?> IntExpr
let recBody = ctx.MkEq(ctx.MkAdd(fib_bv, fib_bv1), fib_bv2)

// explicit trigger: match fib(n) and fib(n+1)
let trig = ctx.MkPattern [| fib_bv :> Expr; fib_bv1 :> Expr |]

// quantifier: forall n:Int . fib(n) + fib(n+1) = fib(n+2)
let recurrence =
  ctx.MkForall([| intS |], [| ctx.MkSymbol "n" :> Symbol |], recBody, patterns = [| trig |])
// 4) Set up the solver and assert:
//    - the axiom
//    - base cases fib(0)=0, fib(1)=1
let solver = ctx.MkSolver()
solver.Assert recurrence
solver.Assert(ctx.MkEq(fibDecl.Apply [| ctx.MkInt 0 :> Expr |], ctx.MkInt 0))
solver.Assert(ctx.MkEq(fibDecl.Apply [| ctx.MkInt 1 :> Expr |], ctx.MkInt 1))
// 5) Encode the goal: fib(3) + fib(4) = fib(5)
let f3 = fibDecl.Apply [| ctx.MkInt 3 :> Expr |] :?> IntExpr
let f4 = fibDecl.Apply [| ctx.MkInt 4 :> Expr |] :?> IntExpr
let f5 = fibDecl.Apply [| ctx.MkInt 5 :> Expr |] :?> IntExpr
let goal = ctx.MkEq(ctx.MkAdd(f3, f4), f5)
// 6) Assert ¬goal and check UNSAT
solver.Assert(ctx.MkNot goal)

match solver.Check() with
| Status.UNSATISFIABLE -> printfn "✔ Proved: fibonacci(3) + fibonacci(4) = fibonacci(5)"
| Status.SATISFIABLE -> printfn "✘ Countermodel found:\n%s" (solver.Model.ToString())
| Status.UNKNOWN -> printfn "?! Z3 gave UNKNOWN"
| r -> printfn "Unexpected result: %A" r

0
