module Tests

open AVM.VirtualMachine
open Xunit

let emptyCtx =
  { instructions = [||]
    programCounter = 0ul
    stack = []
    returnStack = []
    scratch = Map.empty }

[<Fact>]
let ``add 1 2 = 3`` () =
  let ctx =
    { emptyCtx with
        instructions = [| Add |]
        stack = [ Num 1UL; Num 2UL ]
        returnStack = [] }
    |> execute

  Assert.Equal<Value list>([ Num 3UL ], ctx.stack)
  Assert.Equal(1ul, ctx.programCounter)

[<Fact>]
let ``fst (18,19)`` () =
  let ctx =
    { emptyCtx with
        instructions = [| B "main"; Label "fst"; Pop; Loads; Retsub; Label "main"; Callsub "fst" |]
        stack = [ Num 1UL; Num 0UL ]
        scratch = [ 0UL, Num 18UL; 1UL, Num 19UL ] |> Map.ofList }
    |> execute

  Assert.Equal<Value list>([ Num 18UL ], ctx.stack)

[<Fact>]
let ``snd (18,19)`` () =
  let ctx =
    { emptyCtx with
        instructions =
          [| B "main"
             Label "snd"
             Swap
             Pop
             Loads
             Retsub
             Label "main"
             Callsub "snd" |]
        stack = [ Num 1UL; Num 0UL ]
        scratch = [ 0UL, Num 18UL; 1UL, Num 19UL ] |> Map.ofList }
    |> execute

  Assert.Equal<Value list>([ Num 19UL ], ctx.stack)

[<Fact>]
let ``let a = 1 in a + 2`` () =
  let ctx =
    { emptyCtx with
        instructions = [| PushInt 2UL; Load 0UL; Add |]
        scratch = [ 0UL, Num 1UL ] |> Map.ofList }
    |> execute

  Assert.Equal<Value list>([ Num 3UL ], ctx.stack)

[<Fact>]
let ``let rec fac acc n = if n = 0 then acc else fac (acc*n) (n-1)`` () =
  let fac =
    [| B "main"
       // fac acc n
       Label "fac"
       Dup
       Bz "end"
       Dup
       PushInt 1UL
       Sub
       Store 0UL
       Mul
       Load 0UL
       B "fac"
       Label "end"
       Pop
       Retsub
       // main
       Label "main"
       PushInt 1UL
       PushInt 5UL
       // stack = [n;acc] since arguments are reversed when pushing to the stack
       Callsub "fac" |]

  let ctx =
    { emptyCtx with
        instructions = fac
        stack = []
        scratch = [ 0UL, Num 0UL ] |> Map.ofList }
    |> execute

  Assert.Equal<Value list>([ Num 120UL ], ctx.stack)
