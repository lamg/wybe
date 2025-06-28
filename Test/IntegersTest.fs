module IntegerTests

open Xunit
open Core
open GriesSchneider

[<Fact>]
let ``check integer theorems`` () =
  [ ``× zero``
    ``+ cancellation``
    ``GS 15.23``
    ``GS 15.34``
    ``GS 15.35``
    monotonicity
    ``↓ symmetry``
    ``↑ symmetry``
    ``↑ associativity``
    ``↓ associativity``
    ``↓ idempotency``
    ``↑ idempotency``
    ``GS 15.58``
    ``+ over ↓`` ]
  |> Inspect.checkAll

[<Fact>]
let ``integer string representation`` () =
  [ n + m, "n + m"
    -n, "-n"
    n - m, "n - m"
    n * m, "n × m"
    n / m, "n ÷ m"
    IsDivisor(n, m), "n ∣ m"
    Exceeds(n, m), "n > m"
    AtLeast(n, m), "n ≥ m"
    LessThan(n, m), "n < m"
    AtMost(n, m), "n ≤ m" ]
  |> List.iter (fun (n, s) -> Assert.Equal(s, n.ToString()))

[<Fact>]
let ``gcd m n = gcd m (m - n)`` () =
  proof {
    lemma (gcd m n = gcd m (m - n))
    gcd m n
    ``==`` { ``GS 15.101`` }
    gcd (Abs m) (Abs n)
    ``==`` { ``GS 15.98`` }
    gcd (gcd m m) (Abs -n)
    ``==`` { ``GCD associativity`` }
    gcd m (gcd m (Abs -n))
    ``==`` { ``GS 15.98`` }
    gcd m (gcd m (gcd -n -n))
    ``==`` { ``GCD associativity`` }
    gcd m (gcd (gcd m -n) -n)
    ``==`` { ``GCD symmetry`` }
    gcd m (gcd -n (gcd m -n))
    ``==`` { ``GCD associativity`` }
    gcd (gcd m -n) (gcd m -n)
    ``==`` { ``GS 15.98`` }
    Abs (gcd m -n)
    ``==`` { ``GS 15.102``}
    Abs (gcd m (m - n))
  }
  |> Inspect.inspect
  |> Inspect.summary
  |> Inspect.print
