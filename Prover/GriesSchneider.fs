module GriesSchneider

open Core

#nowarn 86

// Propositions
let private toProp (x: WExpr) =
  match x with
  | :? Var as x ->
    match x.Sort with
    | WBool -> Ok(ExtProposition x)
    | _ -> Error $"expecting boolean variable {x}"
  | :? Proposition as x -> Ok x
  | _ -> Error $"expecting proposition at {x}"

let private underline x =
  let str = x.ToString()
  let line = String.replicate str.Length "^"
  str, line

let private toBinaryProposition (op: string) (x: WExpr) (y: WExpr) =
  let strX, lineX = underline x
  let strY, lineY = underline y
  let separator = String.replicate $" {op} ".Length " "
  let opStr = $"{strX} {op} {strY}"

  match toProp x, toProp y with
  | Ok x, Ok y -> x, y
  | Error e, Error d -> failwith $"\n{opStr}\n{lineX}{separator}{lineY}\n{e}\n{d}"
  | Error e, Ok _ -> failwith $"\n{opStr}\n{lineX}\n{e}"
  | Ok _, Error d ->
    let blankX = String.replicate $"{strX} {op} ".Length " "
    failwith $"\n{opStr}\n{blankX}{lineY}\n{d}"

let private toUnaryProposition (op: string) (x: WExpr) =
  match toProp x with
  | Ok x -> x
  | Error e ->
    let strX, lineX = underline x
    let separator = String.replicate op.Length " "
    failwith $"{op}{strX}\n{separator}{lineX}"

let (!) x = Not(toUnaryProposition "¬" x)

let (===) (x: WExpr) (y: WExpr) = Equiv(toBinaryProposition "≡" x y)

let (!==) x y = Inequiv(toBinaryProposition "≢" x y)

let (==>) x y = Implies(toBinaryProposition "⇒" x y)

let (<==) x y = Follows(toBinaryProposition "⇐" x y)

let (<&&>) x y = And(toBinaryProposition "∧" x y)
let (<||>) x y = Or(toBinaryProposition "∨" x y)

let ``∀`` vars f =
  ExtProposition(Quantifier(Forall, vars, True, f))

let ``∃`` vars f =
  ExtProposition(Quantifier(Exists, vars, True, f))

let axiom name (pred: Proposition) = Law(name, pred)

let theorem name pred = Theorem(Law(name, pred))

let lemma pred = Theorem(Law(string pred, pred))

/// NOTE: redefining the operator `=` in F# is not recommended, but for most Wybe scripts
/// this would make the proofs look closer to syntax we are used to
let (=) x y = Equals(x, y)
let (!=) x y = Differs(x, y)

let mkBoolVar n = ExtProposition(Var(n, WBool))

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
let weakening = x <&&> y ==> x |> axiom "weakening"

let ``Leibniz as axiom`` f x y =
  x = y ==> (f x = f y) |> axiom "Leibniz as axiom"

// 9 Predicate Calculus

let ``∨ over ∀`` (vars: WExpr list, p: Proposition) =
  y <||> ``∀`` vars p === ``∀`` vars (y <||> p) |> axiom "∨ over ∀"

let ``De Morgan`` (vars: WExpr list, p: Proposition) =
  !(``∀`` vars p) === ``∃`` vars !p |> axiom "De Morgan"


// Integers

let mkIntVar x = ExtInteger(Var(x, WInt))

let n, m, p = mkIntVar "n", mkIntVar "m", mkIntVar "p"
let zero = Integer 0
let one = Integer 1

let extractIntegers (name: string) (x: WExpr, y: WExpr) =
  match x, y with
  | (:? Integer as x), (:? Integer as y) -> x, y
  | (:? Var as x), (:? Var as y) when x.Sort.Equals WInt && y.Sort.Equals WInt -> ExtInteger x, ExtInteger y
  | (:? Var as x), (:? Integer as y) -> ExtInteger x, y
  | (:? Integer as x), (:? Var as y) -> x, ExtInteger y
  | _ -> failwith $"unexpected {x} {y} for {name}"

let (>=) (x: WExpr) (y: WExpr) =
  ExtProposition(AtLeast(extractIntegers "≥" (x, y)))

let (<=) (x: WExpr) (y: WExpr) =
  ExtProposition(AtMost(extractIntegers "≤" (x, y)))

let (<) (x: WExpr) (y: WExpr) =
  ExtProposition(LessThan(extractIntegers "<" (x, y)))

let (>) (x: WExpr) (y: WExpr) =
  ExtProposition(Exceeds(extractIntegers ">" (x, y)))

let ``+ associativity`` = n + m + p = n + m + p |> axiom "+ associativity"

let ``× associativity`` = n * m * p = n * m * p |> axiom "× associativity"

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

let ``↓ symmetry`` () =
  proof { theorem "↓ symmetry" (Min(n, m) = Min(m, n)) }

let ``↑ symmetry`` () =
  proof { theorem "↑ symmetry" (Max(n, m) = Max(m, n)) }

let ``↓ associativity`` () =
  proof { theorem "↓ associativity" (Min(n, Min(m, p)) = Min(Min(n, m), p)) }

let ``↑ associativity`` () =
  proof { theorem "↑ associativity" (Max(n, Max(m, p)) = Max(Max(n, m), p)) }

let ``↑ idempotency`` () =
  proof { theorem "↑ idempotency" (Max(n, n) = n) }

let ``↓ idempotency`` () =
  proof { theorem "↓ idempotency" (Min(n, n) = n) }

let ``GS 15.58`` () =
  proof { theorem "GS 15.58" (n <= m === (Min(n, m) = n)) }

let ``+ over ↓`` () =
  proof { theorem "+ over ↓" (p + Min(n, m) = Min(p + n, p + m)) }

let ``+ over ↑`` () =
  proof { theorem "+ over ↑" (p + Max(n, m) = Max(p + n, p + m)) }


// Sequences

let sortA = WVarSort "a"
let mkSeqElem a = ExtSequence(Var(a, sortA))
let mkSeq x = ExtSequence(Var(x, WSeq sortA))

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
  | :? Var as v when v.Sort.IsWSeq -> Cons(x, ExtSequence v)
  | :? FnApp as f ->
    if
      (List.last f.FnDecl.Signature).IsWSeq
      && f.Args.Length.Equals(f.FnDecl.Signature.Length - 1)
    then
      Cons(x, ExtSequence f)
    else
      failwith $"wrong function signature {f}"
  | _ -> failwith $"expecting a sequence, got {xs}"

let (++) xs ys = Concat(xs, ys)

let len (x: WExpr) =
  match x with
  | :? Sequence as x -> ExtInteger(Length x)
  | :? Var as x when x.Sort.IsWSeq -> ExtInteger(Length(ExtSequence x))
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

  Cons(x, Empty x.Sort)

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
  let declFib = FnDecl("fib", [ WInt; WInt ])
  ExtInteger(FnApp(declFib, [ x ]))

let fibProp = ``∀`` [ n ] (n >= zero <&&> (fib (n + 2) = fib n + fib (n + 1)))

/// factorial function
let fact (x: WExpr) =
  let declFact = FnDecl("fact", [ WInt; WInt ])
  ExtInteger(FnApp(declFact, [ x ]))

let factProp =
  ``∀`` [ n ] (n >= zero <&&> (fact (n + 1) = fact n * (n + 1)) <&&> (fact zero = one))
