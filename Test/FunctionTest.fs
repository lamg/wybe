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


  let insert (n, xs) =
    let decl = Fn("insert", [ WInt; WSeq WInt; WSeq WInt ])
    ExtSeq(App(decl, [ n; xs ]))

  let xs = ExtSeq(Var("xs", WSeq WInt))
  let ys = ExtSeq(Var("ys", WSeq WInt))
  let y = ExtSeq(Var("y", WInt))
  let y' = mkIntVar "y"
  // let ins0 = ``∀`` [ n; x ] (xs = Empty ==> insert (n, xs) = Cons(n, xs))

  let ins1 =
    ``∀`` [ n; xs ] (xs = Cons(y, ys)) <&&> (n <= y')
    ==> (insert (n, xs) = Cons(n, xs))

  let ins2 =
    ``∀`` [ n; xs;ys ] (xs = Cons(y, ys) <&&> (n > y') ==> (insert (n, xs) = Cons(y, insert (n, ys))))

  let five = Integer 5
  // WARNING: (0,0): pattern does not contain all quantified variables.
  // length 1; ps [(insert (:var 0) ys)]
  proof {
    lemma (insert (five, wList [ 1; 4; 6 ]) = wList [ 1; 4; 5; 6 ])
    insert (five, wList [ 1; 4; 5 ])
    ``==`` { ins2 }
    Cons(one, insert (five, wList [ 4; 6 ]))
    ``==`` { ins2 }
    Cons(Integer 1, Cons(Integer 4, insert (five, wList [ 6 ])))
    ``==`` { ins1 }
    wList [ 1; 4; 5; 6 ]
  }
  |> inspect
  |> summary
  |> print
