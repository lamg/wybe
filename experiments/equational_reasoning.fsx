let rec insert (n: int) =
  function
  | [] -> [ n ]
  | x :: xs when n <= x -> n :: x :: xs
  | x :: xs -> x :: insert n xs

// possible feature of Wybe:
// parse this file and check a proof that looks like the one below
(*
 insert 5 [1; 4; 6]
= { insert.branch.2 }
 1 :: insert 5 [4;6]
= { insert.branch.2 }
 1 :: 4 :: insert 5 [6]
= { insert.branch.1 }
 1 :: 4 :: 5 :: 6 :: []
= { cons operator }
 [1; 4; 5; 6]
*)
// for correctly checking the calculation above the following
// definitions are needed
// insert.branch.2: len xs > 0 && head xs < n  ⇒  insert n xs  =  (head xs) :: insert n (tail xs)
// other theorems Wybe could check
// TODO implement recurrence relations and a type provider to extract Wybe expressions from F# code
(*
 len (insert n xs) = len xs + 1
 ∀x → x ∈ xs ∧ x < n ⇒ index x xs < index n (insert n xs)
*)

// in general is needed a notation for referring to target language elements, and its correct
// implementation to be used in proofs

insert 5 [ 1; 4; 6 ] |> printfn "%A"
