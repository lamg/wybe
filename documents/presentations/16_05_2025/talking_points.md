# Talking points

What is formal verification:

- Formal verification is a way of making sure that a program has no errors
- how is that possible?
- first we need to talk a little bit about Math
- we need to acknowledge that mathematical formulas are universally true
- this means mathematical formulas are true because they follow some rules that are independent of culture, epoch or any other particular circumstance
- we could argue that mathematical formulas capture something essential to being a human being
- for example, we could have a calculator that says that `2 + 2 = 5`, but rather than saying that from now on mathematics is different, we say the calculator is broken, because it failed to follow the rules of arithmetic

Programs can be represented as mathematical formulas

- we can also have an arithmetic that instead of numbers works with programs
- the results also follow simple rules that are not tied to a specific implementation
- and these rules are called formal semantics
- while some languages still use certain implementations as their "semantic" authorities, it's becoming more common to use such universally valid rules, which means they are independent of any implementation

Zero program errors, but no 100% security

- I'm implementing a calculator for computer programs, which can have errors
- This calculators are known as theorem provers
- The underlying computer for developing or deploying your program can also be compromised

How can formal verification be done

- theorem provers allow us to represent arbitrary abstractions in their languages
- the difference with the typical programming language is that these abstractions are meant to be used in mathematical proofs, to be checked by the theorem prover.
- while in a typical programming language we tend to have abstractions to facilitate numerical calculations, the creation of user interfaces, concurrent tasks and so on
- in particular, we can represent properties of your programs in the language of the theorem prover
- this properties can be automatically extracted from any common programming language like (Rust, Python, etc.)
- the extracted formulas are checked by the theorem prover after the user fills the gaps in the proofs, if they exist
- In the picture we see a proof in Agda, which is a language and theorem prover
- However Agda is written by and for people with advanced knowledge of Computer Science, which most engineers do not have today
- and is not particularly specialized in extracting proof obligations from programming languages like F# or Rust

Wybe, an accessible and powerful tool

- it uses predicate calculus, which is the logic you use every day in `while` and `if` stataments with the addition of ∀ and ∃
- integrated capabilities for extracting proof obligations from Rust, this is work in progress
- first class IDE support, since Wybe built on top of F#
- it uses Microsoft Z3 for checking the proofs

Reactions in social media

- when I open sourced the project a month ago

The team

- just me
- I've been exploring formal verification for more than 10 years, as you can see in an article published by a Cuban online magazine in 2016

Thank you very much for listening.
