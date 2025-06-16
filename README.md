![Wybe](./documents/images/wybe_logo.png)

![NuGet Version](https://img.shields.io/nuget/v/Wybe?style=flat-square)
![NuGet Downloads](https://img.shields.io/nuget/dt/Wybe?style=flat-square)
![Tests](https://img.shields.io/github/actions/workflow/status/lamg/wybe/test.yml?style=flat-square&label=tests)

A theorem prover embedded in F#'s computation expressions, using [Z3][3] under the hood

## Features and progress

- [ ] Check proofs written in a syntax inspired by [Dijkstra's predicate calculus][0]
  - [ ] [A Logical Approach to Discrete Math][1]
    - [x] [Basic predicate calculus proofs](./Prover/GriesSchneider/PredicateCalculus.fs)
    - [x] Integers
    - [x] Sequences
  - [ ] [Relational calculus](./documents/calc_collection.pdf)
  - [x] Functions

- [ ] Extract proof obligations from
  - [ ] Rust
  - [ ] F#
  - [ ] Golang
  - [ ] [Compact](https://docs.midnight.network/develop/reference/compact)

## Installation instructions

- Install the [dotnet 10](https://dotnet.microsoft.com/en-us/download) CLI
- Clone this repository locally

## Example proof

![Double Negation](./documents/images/double_negation.png)

[0]: https://www.cs.utexas.edu/users/EWD/transcriptions/EWD13xx/EWD1300.html
[1]: https://books.google.de/books/about/A_Logical_Approach_to_Discrete_Math.html?id=ZWTDQ6H6gsUC
[3]: https://github.com/Z3Prover/z3
