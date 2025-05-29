module FunctionTest

open Xunit
open Core
open Inspect
open GriesSchneider.Functions
open GriesSchneider.Integers
open GriesSchneider.Sequences

[<Fact>]
let ``test fibonacci function`` () =
  let two = Integer 2

  proof {
    lemma (fib two = fib one + fib zero)

    fib two
    ``==`` { fibProp }
    fib one + fib zero
  }
  |> inspect
  |> failIfNotProved

[<Fact>]
let ``test fibonacci invariant`` () =
  let i, a, b = mkIntVar "i", mkIntVar "a", mkIntVar "b"

  // a = fibonacci (i - 1) ∧ b = fibonacci i ⇒ a + b = fibonacci (i + 1)
  // TODO shouldn't this proof fail because there's no i > 0 restriction?
  proof {
    lemma ((a = fib (i - 1)) <&&> (b = fib i) ==> (a + b = fib (i + 1)))
    a = fib (i - 1) <&&> (b = fib i)
    ``⇒`` { fibProp }
    a + b = fib (i + 1)
  }
  |> inspect
  |> failIfNotProved

[<Fact>]
let ``test factorial invariant`` () =
  let i = mkIntVar "i"
  let result = mkIntVar "result"

  proof {
    lemma (result = fact i ==> (result * i = fact (i + one)))
    result = fact i
    ``⇒`` { factProp }
    result * i = fact (i + 1)
  }
  |> inspect
  |> failIfNotProved

[<Fact>]
let ``print functions`` () =
  let ackermann (x, y) =
    let decl = Fn("ackermann", [ WInt; WInt; WInt ])
    ExtInteger(App(decl, [ x; y ]))

  [ fib zero, "fib(0)"
    fib (n + 1), "fib(n + 1)"
    ackermann (zero, zero), "ackermann(0, 0)"
    ackermann (n + 1, n + 1), "ackermann(n + 1, n + 1)" ]
  |> List.iter (fun (f, r) -> Assert.Equal(f.ToString(), r))

[<Fact>]
let ``insert(5, ϵ) = [5]`` () =
  let decl = Fn("insert", [ WInt; WSeq WInt; WSeq WInt ])
  let insert (n, xs) = ExtSeq(App(decl, [ n; xs ]))

  let ins0 = ``∀`` [ n ] (insert (n, Empty WInt) = Cons(n, Empty WInt))
  let five = Integer 5

  proof {
    lemma (insert (five, wList []) = wList [ 5 ])
    insert (five, wList [])
    ``==`` { ins0 }
    wList [ 5 ]
  }
  |> inspect
  |> failIfNotProved


[<Fact>]
let ``insert function`` () =
  // let rec insert (n: int) =
  //  function
  //  | [] -> [ n ]
  //  | x :: xs when n <= x -> n :: x :: xs
  //  | x :: xs -> x :: insert n xs
  //
  //  insert 5 [1; 4; 6]
  // = { insert.branch.2 }
  //  1 :: insert 5 [4;6]
  // = { insert.branch.2 }
  //  1 :: 4 :: insert 5 [6]
  // = { insert.branch.1 }
  //  1 :: 4 :: 5 :: 6 :: []
  // = { cons operator }
  //  [1; 4; 5; 6]


  let decl = Fn("insert", [ WInt; WSeq WInt; WSeq WInt ])
  let insert (n, xs) = ExtSeq(App(decl, [ n; xs ]))

  let xs = ExtSeq(Var("xs", WSeq WInt))
  let ys = ExtSeq(Var("ys", WSeq WInt))
  let y = ExtSeq(Var("y", WInt))
  let y' = mkIntVar "y"
  let five = Integer 5

  let ins0 = ``∀`` [ n ] (insert (n, Empty WInt) = Cons(n, Empty WInt))

  let ins1 =
    ``∀`` [ n; xs ] (xs = (y <. ys)) <&&> (n <= y') ==> (insert (n, xs) = (n <. xs))
    |> axiom "ins1"

  let ins2 =
    ``∀`` [ n; xs ] (xs = (y <. ys) <&&> (n > y') ==> (insert (n, xs) = (y <. insert (n, ys))))
    |> axiom "ins2"

  proof {
    lemma (insert (five, wList [ 1; 4; 6 ]) = wList [ 1; 4; 5; 6 ])
    insert (five, wList [ 1; 4; 5 ])
    ``==`` { ins2 }
    one <. insert (five, wList [ 4; 6 ])
    ``==`` { ins2 }
    one <. (Integer 4 <. insert (five, wList [ 6 ]))
    ``==`` { ins1 }
    wList [ 1; 4; 5; 6 ]
  }
  |> inspect
  |> stepPropAt 0
  |> summary
  |> print
