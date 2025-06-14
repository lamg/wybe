module GriesSchneider

open Core

#nowarn 86

// Propositions

let private toProposition (x: WExpr) =
  match x with
  | :? Var as x ->
    match x.sort with
    | WBool -> ExtBoolOp x
    | _ -> failwith $"expecting boolean variable {x}"
  | :? Proposition as x -> x
  | _ -> failwith $"expecting proposition {x}"

let (!) x = Not(toProposition x)

let (===) (x: WExpr) (y: WExpr) = Equiv(toProposition x, toProposition y)

let (!==) x y =
  Inequiv(toProposition x, toProposition y)

let (==>) x y =
  Implies(toProposition x, toProposition y)

let (<==) x y =
  Follows(toProposition x, toProposition y)

let (<&&>) x y = And(toProposition x, toProposition y)
let (<||>) x y = Or(toProposition x, toProposition y)
let ``∀`` vars f = Quantifier(Forall, vars, f)
let ``∃`` vars f = Quantifier(Exists, vars, f)

let axiom name (pred: Proposition) = { identifier = name; body = pred }

let theorem name pred =
  Theorem { identifier = name; body = pred }

let lemma pred =
  Theorem
    { identifier = pred.ToString()
      body = pred }

/// NOTE: redefining the operator `=` in F# is not recommended, but for most Wybe scripts
/// this would make the proofs look closer to syntax we are used to
let (=) x y = Equals(x, y)
let (!=) x y = Differs(x, y)

let mkBoolVar n = ExtBoolOp { name = n; sort = WBool }

let x, y, z = mkBoolVar "x", mkBoolVar "y", mkBoolVar "z"

// NOTE: axioms are defined without adding an unit parameter, which delays the computation,
// since there's no call to Z3 in their definition

// (x ≡ y) ∧ (y ≡ z)  ⇒  (x ≡ z)
let ``≡ transitivity`` =
  x === y <&&> (y === z) ==> (x === z) |> axiom "≡ transitivity"

// x ≡ y ≡ y ≡ x
let ``≡ sym`` = x === y === (y === x) |> axiom "≡ sym"

// (x ≡ x) ≡ true
let ``≡ ident`` = x === x === True |> axiom "≡ ident"

// false ≡ ¬true
let ``false def`` = False === !True |> axiom "false def"

// ¬(x ≡ y) ≡ ¬x ≡ y
let ``¬ over ≡`` = !(x === y) === (!x === y) |> axiom "¬ over ≡"

// x ≢ y ≡ ¬(x ≡ y)
let ``≢ def`` = x !== y === !(x === y) |> axiom "≢ def"

// (x ≡ y) ≡ z  ≡  x ≡ (y ≡ z)
let ``≡ assoc`` =
  let lhs = x === y === z
  let rhs = x === (y === z)
  lhs === rhs |> axiom "≡ assoc"

// GS 3.4 Disjunction
let ``∨ sym`` = x <||> y === (y <||> x) |> axiom "∨ sym"

let ``∨ assoc`` = x <||> y <||> z === (x <||> (y <||> z)) |> axiom "∨ assoc"

let ``∨ idempotency`` = x <||> x === x |> axiom "∨ idempotency"

let ``∨ over ≡`` =
  x <||> (y === z) === (x <||> y === (x <||> z)) |> axiom "∨ over ≡"

let ``excluded middle`` = x <||> !x |> axiom "excluded middle"

let twice x = [ x; x ]

// GS 3.5

let ``golden rule`` = x <&&> y === (x === y === (x <||> y)) |> axiom "golden rule"

let ``true theorem`` () = proof { theorem "true theorem" True }

// GS = "A Logical Approach to Discrete Math, by David Gries and Fred B. Schneider"
let ``GS 3.11`` () =
  proof { theorem "GS 3.11" (!x === y === (x === !y)) }

let ``double negation`` () =
  proof { theorem "double negation" (!(!x) === x) }

let ``negation of false`` () =
  proof { theorem "negation of false" (!False === True) }

let ``GS 3.14`` () =
  proof { theorem "GS 3.14" (x !== y === (!x === y)) }

let ``symmetry of ≢`` () =
  proof { theorem "symmetry of ≢" (x !== y === (y !== x)) }

let ``associativity of ≢`` () =
  proof { theorem "associativity of ≢" (x !== y !== z === (x !== (y !== z))) }

let ``mutual associativity`` () =
  proof { theorem "mutual associativity" (x !== y === z === (x !== (y === z))) }

let ``mutual interchangeability`` () =
  proof { theorem "mutual interchangeability" (x !== y === z === (x === (y !== z))) }

// GS 3.4 Disjunction

let ``∨ zero`` () =
  proof { theorem "∨ zero" (x <||> True === True) }

let ``∨ identity`` () =
  proof { theorem "∨ identity" (x <||> False === x) }

let ``∨ over ∨`` () =
  proof { theorem "∨ over ∨" (x <||> (y <||> z) === (x <||> y <||> (x <||> z))) }

let ``GS 3.32`` () =
  proof { theorem "GS 3.32" (x <||> y === (x <||> !y) === x) }

// GS 3.5 conjuction

let ``∧ sym`` () =
  proof { theorem "∧ sym" (x <&&> y === (y <&&> x)) }

let ``∧ assoc`` () =
  proof { theorem "∧ assoc" (x <&&> y <&&> z === (x <&&> (y <&&> z))) }

let ``∧ idempotency`` () =
  proof { theorem "∧ idempotency" (x <&&> x === x) }

let ``∧ zero`` () =
  proof { theorem "∧ zero" (x <&&> False === False) }

let ``∧ over ∧`` () =
  proof { theorem "∧ over ∧" (x <&&> (y <&&> z) === (x <&&> y <&&> (x <&&> z))) }

let contradiction () =
  proof { theorem "contradiction" (x <&&> !x === False) }

let ``∧ ∨ absorption`` () =
  proof { theorem "∧ ∨ absorption" (x <&&> (x <||> y) === x) }


let ``∨ ∧ absorption`` () =
  proof { theorem "∨ ∧ absorption" (x <||> (x <&&> y) === x) }

// 3.6 implication

let ``⇒ definition`` = x ==> y === (x <||> y === x) |> axiom "⇒ definition"
let consequence = x <== y === (y ==> x) |> axiom "consquence"

// 9 Predicate Calculus

let ``∨ over ∀`` (vars: WExpr list, p: Proposition) =
  y <||> ``∀`` vars p === ``∀`` vars (y <||> p) |> axiom "∨ over ∀"

let ``De Morgan`` (vars: WExpr list, p: Proposition) =
  !(``∀`` vars p) === ``∃`` vars !p |> axiom "De Morgan"


// Integers

let mkIntVar x = ExtInteger { name = x; sort = WInt }

let n, m, p = mkIntVar "n", mkIntVar "m", mkIntVar "p"
let zero = Integer 0
let one = Integer 1

let extractIntegers (name: string) (x: WExpr, y: WExpr) =
  match x, y with
  | (:? Integer as x), (:? Integer as y) -> x, y
  | (:? Var as x), (:? Var as y) when x.sort.Equals WInt && y.sort.Equals WInt -> ExtInteger x, ExtInteger y
  | (:? Var as x), (:? Integer as y) -> ExtInteger x, y
  | (:? Integer as x), (:? Var as y) -> x, ExtInteger y
  | _ -> failwith $"unexpected {x} {y} for {name}"

let (>=) (x: Integer) (y: Integer) = ExtBoolOp(AtLeast(x, y))

let (<=) (x: WExpr) (y: WExpr) =
  ExtBoolOp(AtMost(extractIntegers "≥" (x, y)))

let (<) (x: Integer) (y: Integer) = ExtBoolOp(LessThan(x, y))
let (>) (x: Integer) (y: Integer) = ExtBoolOp(Exceeds(x, y))

let ``+ associativity`` = n + m + p = n + m + p |> axiom "+ associativity"

let ``× associativity`` = (n * m) * p = n * (m * p) |> axiom "× associativity"

let ``+ symmetry`` = n + m = m + n |> axiom "+ symmetry"

let ``× symmetry`` = n * m = m * n |> axiom "× symmetry"

let ``+ identity`` = n + zero = n |> axiom "+ identity"
let ``× identity`` = n * one = n |> axiom "× identity"

let ``+ over ×`` = n * (m + p) = n * m + n * p |> axiom "+ over ×"

let ``+ inverse`` = ``∃`` [ n ] (n + m = zero) |> axiom "+ inverse"

let ``× cancellation`` =
  p != zero ==> (p * n = p * m === (n = m)) |> axiom "× cancellation"

let ``+ cancellation`` () =
  proof { theorem "+ cancellation" (n + m = n + p === (m = p)) }

let ``× zero`` () =
  proof { theorem "× zero" (n * zero = zero) }

let pos x = x > zero

let ``GS 15.23`` () = proof { lemma (-n * -m = n * m) }

let ``GS 15.34`` () =
  proof { lemma (n != zero ==> pos (n * n)) }

let ``GS 15.35`` () =
  proof { lemma (pos n ==> (pos m === pos (n * m))) }

let monotonicity () =
  proof { lemma (n < m ==> (n + p < m + p)) }

// Sequences

let sortA = WVarSort "a"
let mkSeqElem a = ExtSeq { name = a; sort = sortA }
let mkSeq x = ExtSeq { name = x; sort = WSeq sortA }

let wList (xs: int list) =
  xs |> Seq.rev |> Seq.fold (fun acc x -> Cons(Integer x, acc)) (Empty WInt)

let wSeq s (xs: WExpr seq) =
  xs |> Seq.rev |> Seq.fold (fun acc x -> Cons(x, acc)) (Empty s)

let a, b = mkSeqElem "a", mkSeqElem "b"

let ws, xs, ys, zs = mkSeq "ws", mkSeq "xs", mkSeq "ys", mkSeq "zs"

let ``ϵ`` = Empty sortA

let (<.) x (xs: WExpr) =
  match xs with
  | :? Sequence as xs -> Cons(x, xs)
  | :? Var as v when v.sort.IsWSeq -> Cons(x, ExtSeq v)
  | :? FnApp as f ->
    let (App(Fn(_, signature), args)) = f

    if (List.last signature).IsWSeq && args.Length.Equals(signature.Length - 1) then
      Cons(x, ExtSeq f)
    else
      failwith $"wrong function signature {f}"
  | _ -> failwith $"expecting a sequence, got {xs}"

let (++) xs ys = Concat(xs, ys)

let len (x: WExpr) =
  match x with
  | :? Sequence as x -> ExtInteger(Length x)
  | :? Var as x when x.sort.IsWSeq -> ExtInteger(Length(ExtSeq x))
  | _ -> failwith $"len expects a sequence, instead it got {x}"

let singleton (n: WExpr) =
  let x =
    match n with
    | :? Integer as n ->
      match n with
      | ExtInteger e ->
        match e with
        | :? Var as v -> v
        | _ -> failwith "not implemented"
      | _ -> failwith "not implemented"
    | _ -> failwith "not implemented"

  Cons(x, Empty x.sort)

let prepend = a <. ``ϵ`` != ``ϵ`` |> axiom "prepend"

let ``non empty`` = a <. xs != ``ϵ``

let equality = a <. xs = (b <. ys) === (a = b <&&> (xs = ys)) |> axiom "equality"

let ``GS 13.7`` () =
  proof { theorem "GS 13.7" (a <. xs != xs) }

let ``length of ϵ`` = len ``ϵ`` = zero |> axiom "length of ϵ"

let ``length of cons`` = len (a <. xs) = one + len xs |> axiom "length of cons"

let ``length of concat`` () =
  proof { theorem "length of concat" (len (xs ++ ys) = len xs + len ys) }

// Functions

/// fibonacci function
let fib (x: WExpr) =
  let declFib = Fn("fib", [ WInt; WInt ])
  ExtInteger(App(declFib, [ x ]))

let fibProp = ``∀`` [ n ] (n >= zero <&&> (fib (n + 2) = fib n + fib (n + 1)))

/// factorial function
let fact (x: WExpr) =
  let declFact = Fn("fact", [ WInt; WInt ])
  ExtInteger(App(declFact, [ x ]))

let factProp =
  ``∀`` [ n ] (n >= zero <&&> (fact (n + 1) = fact n * (n + 1)) <&&> (fact zero = one))
