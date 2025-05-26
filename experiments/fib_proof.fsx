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


// ## What is a “pattern” (aka a trigger) in Z3?

// Z3 is a DPLL(T)-based SMT solver, and quantifiers (∀/∃) are handled by instantiation rather than by higher‑order proof
// search.  In order to know when to instantiate a universally‑quantified formula, Z3 uses patterns (also called triggers).


// A pattern is simply a collection of terms from your quantified formula that contain the bound variables.  Intuitively,
// you tell Z3:

//     “Whenever you see a ground term matching one of these patterns in your context, instantiate the quantifier by
// equating the bound variable(s) to the argument(s) of that ground term.”

// Without a good pattern, Z3 either

//     1. tries to pick its own (often sub‑optimal) default trigger,
//     2. or gives up instantiating that quantifier altogether,
//     3. leading to *no proof* (or non‑termination or spurious “unknown”).

// -----------------------------------------------------------------------------------------------------------------------

// ## Why we need an explicit pattern in this Fibonacci proof

// Our recurrence axiom is (∀n -> fib n + fib (n+1) = fib(n+1))

// To prove that fib 3 + fib 4 = fib 5, Z3 must “unfold” the recurrence at (n=3) (to relate
// (fib 3, fib 4, fib 5) and also at (n=4) (to relate
// (fib 4,fib 5, fib 6), etc.  By supplying the pattern

//     [| fib n; fib n+1 |]


// we are telling Z3:

//     “As soon as you see a term of the form fib(…) or fib(…+1) in the proof context, instantiate this ∀‑axiom with that
// value of n.”

// In particular:

//     * When we later assert `fib(3)` and `fib(4)`, those ground terms match our trigger, so Z3 instantiates the
// quantifier at \(n=3\) and at \(n=4\).
//     * That gives us the equations needed to derive \(\mathit{fib}(3)+\mathit{fib}(4)=\mathit{fib}(5)\).
//     * **Without** that explicit pattern, Z3’s automatic trigger selection might *not* pick `fib(n)` or `fib(n+1)`, and
// the recurrence axiom would never fire on the terms we actually care about.

// -----------------------------------------------------------------------------------------------------------------------

// ### Summary

//     1. **Patterns = triggers for quantifier instantiation.**
//     2. You create one via `ctx.MkPattern`, passing the sub‑terms (here `fib(n)` and `fib(n+1)`) that contain *all* bound
//  variables.
//     3. You supply that pattern to `MkForall` so Z3 knows *when* to instantiate the quantifier.
//     4. In the Fibonacci example, we need the trigger so that Z3 will actually unfold the recurrence for the specific
// numeric arguments (3 and 4) used in the proof.

// Hope this clarifies why ctx.MkPattern is needed here! Let me know if you’d like to dive deeper into Z3’s
// quantifier‐instantiation heuristics.
