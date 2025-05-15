/// Adds one to the given integer.
fn add_one(x: i32) -> i32 {
    x + 1
    // { $e > x }
}

/// Computes the nth Fibonacci number iteratively.
fn fibonacci(n: u32) -> u32 {
    // def { fibonacci n + fibonacci (n + 1) = fibonacci (n + 2) }
    if n == 0 {
        return 0;
    }

    let mut a = 0;
    let mut b = 1;

    for _ in 1..n {
        // invariant { b = fibonacci i ∧ a = fibonacci (i - 1) }
        let temp = b;
        b = a + b;
        a = temp;
    }
    b
}

// proof obligation
// a = fibonacci (i - 1) ∧ b = fibonacci i ⇒ a + b = fibonacci (i + 1)

fn factorial(n: u32) -> u32 {
    // def { factorial n * (n + 1) = factorial (n + 1) }
    let mut result = 1;
    for i in 1..=n {
        // invariant i { result = factorial i }
        result *= i;
    }
    result
}

// proof obligation
// result = factorial i ⇒ result * i = factorial (i + 1)
