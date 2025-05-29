#r "nuget: Microsoft.Z3, 4.8.11"
open Microsoft.Z3

// This script proves the equation insert(5, [6]) = [5;6]
// from the axiom ∀n,xs. insert(n,xs) = n :: xs, using Z3.

// 1) Create Z3 context with model generation enabled
let cfg = System.Collections.Generic.Dictionary<string, string>()
cfg.Add("model", "true")
let ctx = new Context(cfg)

// 2) Declare sorts: integer and sequence of integers
let intS = ctx.IntSort :> Sort
let seqIntS = ctx.MkSeqSort(intS) :> Sort

// 3) Declare the uninterpreted function insert: Int × Seq Int → Seq Int
let insertDecl = ctx.MkFuncDecl("insert", [| intS; seqIntS |], seqIntS)

// 4) Axiom: ∀n,xs. insert(n,xs) = n :: xs
let n = ctx.MkBound(0u, intS) :?> IntExpr
let xs = ctx.MkBound(1u, seqIntS) :?> SeqExpr
let consNx = ctx.MkConcat(ctx.MkUnit(n), xs)
let insertNx = insertDecl.Apply [| n :> Expr; xs :> Expr |] :?> SeqExpr
let axiomBody = ctx.MkEq(insertNx, consNx)

let axiom =
  ctx.MkForall([| intS; seqIntS |], [| ctx.MkSymbol("n") :> Symbol; ctx.MkSymbol("xs") :> Symbol |], axiomBody)

// 5) Set up the solver and assert the axiom
let solver = ctx.MkSolver()
solver.Assert(axiom)

// 6) Build the concrete sequence [6]
let six = ctx.MkInt 6
let emptySeq = ctx.MkEmptySeq(ctx.MkSeqSort intS)
let seq6 = ctx.MkConcat(ctx.MkUnit(six), emptySeq)

// 7) Form the goal: insert(5, [6]) = [5;6]
let five = ctx.MkInt 5
let insert5Seq6 = insertDecl.Apply [| five :> Expr; seq6 :> Expr |] :?> SeqExpr
let seq5Seq6 = ctx.MkConcat(ctx.MkUnit(five), seq6)
let goal = ctx.MkEq(insert5Seq6, seq5Seq6)

// 8) Prove the goal by checking unsatisfiability of its negation
solver.Assert(ctx.MkNot(goal))

match solver.Check() with
| Status.UNSATISFIABLE -> printfn "✔ insert(5, [6]) = [5;6] proved."
| Status.SATISFIABLE -> printfn "✘ Counterexample:\n%s" (solver.Model.ToString())
| Status.UNKNOWN -> printfn "?! Z3 returned UNKNOWN"
| r -> printfn "Unexpected result: %A" r
