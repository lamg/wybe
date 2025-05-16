# Talking points

What is formal verification:

- Formal verification is a way of making sure that a program has no errors
- Am I crazy? 100% security? No and no.
- if you agree that `2 + 2 = 4` always, then you also agree that a program can have 0 errors
- why, because a program can be represented as a mathematical formula
- in order to understand this you have to acknowledge the difference between a calculator and mathematics.
- a calculator can say that `2 + 2 = 5`, but then you say the calculator is broken, not that mathematics is broken
- I'm building a calculator, but instead of numbers, this calculates properties of programs, like `user allowed to mint NFT only if balance > 0`.
- You still could be hacked because this tool can have errors, or the underlying machine can be compromised.

How can it be done:

- you need a theorem prover and a tool for extracting the mathematical properties from the language you use for writing smart contracts (Rust, Python, Solidity, etc.)
- the extracted formulas are checked by the theorem prover with the user providing some missing steps
- In the picture you see a proof in Agda, which is a theorem prover
- However Agda is written by and for people with PhDs
- and is not particularly specialized in extracting proof obligations from smart contracts

Wybe, an accessible and powerful tool

- it uses predicate calculus, which is the logic you use every day in `while` and `if` stataments with the addition of ∀ and ∃
- integrated capabilities for extracting proof obligations from Rust, this is work in progress as you will be able to see in the technical demo
- first class IDE support, since Wybe built on top of F#, a language developed by Microsoft, part of the .Net family with C#
- it uses Microsoft Z3 for checking the proofs

Reactions in social media

- when I open sourced the project a month ago

The team

- just me
- I've been exploring formal verification for more than 10 years, as you can see in an article published by a Cuban online magazine in 2016

Thank you very much for listening.
