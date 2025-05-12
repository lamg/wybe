/// Adds one to the given integer.
fn add_one(x: i32) -> i32 {
    x + 1
    // { $e > x }
}

// proof
//   theorem $e > x
//   $e
// = { definition of $e }
//   x + 1
// > {  }
//   x
// ⬜

//   1 + 1
// = { because of the rules the teacher told you }
//   2

// 2 + 2
// = { oeuoeu }
// 4

// proof
//   theorem x + x + x = 3*x

//   x + x + x
// = { elementary algebra }
//   2*x + x
// = { elementary algebra }
//   3*x
// ⬜

/// Entry point demonstrating `add_one` functionality via CLI.
fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: {} <number>", args[0]);
        std::process::exit(1);
    }
    let x: i32 = args[1]
        .parse()
        .expect("Argument must be a valid 32-bit integer");
    let result = add_one(x);
    println!("{}", result);
}
