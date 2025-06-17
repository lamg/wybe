![Wybe](./documents/images/wybe_logo.png)

[![NuGet Version][NuGet Version Shield]][Wybe NuGet]
[![NuGet Downloads][NuGet Downloads Shield]][Wybe NuGet]
[![Tests][Wybe-Tests-Shield]][GitHub Actions]

A formal verification tool with the following features:

- DSL for writting proofs supported by F#'s computation expressions
- [Z3][Z3] as inference engine
- Extraction of proof obligations from several languages
- Cross-language proofs: semantics can be extracted from different languages and combined to prove theorems about the whole project

## Features and progress

- [ ] Check proofs written in a syntax inspired by [Dijkstra's predicate calculus][EWD1300]
  - [ ] [A Logical Approach to Discrete Math][LADM]
    - [x] Prove properties with booleans, integers, sequences and functions [GriesSchneider.fs](./Prover/GriesSchneider.fs)
  - [ ] [Relational calculus](./documents/calc_collection.pdf)

- [ ] Extract proof obligations from
  - [ ] Rust
  - [ ] F#
  - [ ] Golang
  - [ ] [Compact][Compact Docs]
    - [Compact modules](./Prover/LanguageServices/Compact/)
    - [Compact demo](./Test/CompactTest.fs)

## Installation instructions

- Install the [dotnet 10](https://dotnet.microsoft.com/en-us/download) CLI
- Clone this repository locally

## Example proof

![Double Negation](./documents/images/double_negation.png)

[EWD1300]: https://www.cs.utexas.edu/users/EWD/transcriptions/EWD13xx/EWD1300.html
[LADM]: https://books.google.de/books/about/A_Logical_Approach_to_Discrete_Math.html?id=ZWTDQ6H6gsUC
[Z3]: https://github.com/Z3Prover/z3

[Wybe NuGet]: https://www.nuget.org/packages/Wybe
[GitHub Actions]: https://github.com/lamg/wybe/actions
[NuGet Version Shield]: https://img.shields.io/nuget/v/Wybe?style=flat-square
[NuGet Downloads Shield]: https://img.shields.io/nuget/dt/Wybe?style=flat-square
[Wybe Tests Shield]: https://img.shields.io/github/actions/workflow/status/lamg/wybe/test.yml?style=flat-square&label=tests

[Compact Docs]: https://docs.midnight.network/develop/reference/compact
