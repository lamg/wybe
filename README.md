# Wybe

![Wybe](./documents/images/wybe_logo.png)

A proof checker embedded in F#'s computation expressions

## Features and progress:

- Check proofs written in a syntax inspired by [Dijkstra's predicate calculus][0]
  - [ ] [A Logical Approach to Discrete Math][1]
    - [ ] [Basic proofs](./Wybe/GriesSchneider/Theorems.fs)
  - [ ] Lambda calculus interpreter to transform expressions
  - [ ] Sets, ∀, ∃
  - [ ] [Relational calculus][2]

## Examples

![Double Negation](./documents//images/double_negation.png)

[0]: https://www.cs.utexas.edu/users/EWD/transcriptions/EWD13xx/EWD1300.html
[1]: https://books.google.de/books/about/A_Logical_Approach_to_Discrete_Math.html?id=ZWTDQ6H6gsUC
[2]: http://www.mathmeth.com/files/calc_collection.pdf

## Technical debt

- [ ] use names like `∨-over-≡` instead of `∨ over ≡`, since it's getting confusing when formatting proofs, should it be done in the formatter without interfering with the rest of the code, or all names changed for consistency?

- [ ] Leave a trace when parsing calculations in CalculationCE.fs to indicate where the parsing error happened

- [ ] implement evidence of theorem proof when the reduction of transitivity implies demonstrandum

- [ ] when generating rewriters in `compileCalculation` pass a pair of surrounding expressions to the generator, so it can generate alternatives tailored to them

- [ ] use the `withLaws` computation expression to indicate which laws will be used to transform laws appearing in hints,that way `Axioms.sym` is no longer needed. 