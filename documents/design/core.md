Prover/Core.fs is the central component of the Wybe theorem prover. It defines the entire logical framework of
  the system. Its primary responsibilities are:


1. Defining Expressions: It specifies the data structures for all expressions in the Wybe language, including
  propositions (logic), integers, sequences, and functions.
2. Proof Representation: It defines how a formal proof (a "calculation") is structured.
3. Proof Checking: It implements the logic to verify the correctness of a proof by translating Wybe expressions
  into the language of the Z3 SMT solver and using Z3 to check each step.
4. User-Friendly Syntax: It provides F# computation expressions (e.g., proof { ... }) to create a Domain-Specific
  Language (DSL) for writing proofs in a clean, readable way.

Key Data Structures


The core of the file is the WExpr (Wybe Expression) type and the various types that implement it.


* `WExpr`: An abstract interface that represents any expression in the Wybe language. Any type that is a WExpr
 must be able to:
   * `ToZ3Expr`: Translate itself into an expression that the Z3 solver can understand. This is the bridge
     between the Wybe language and the underlying solver.
   * `ToSymbolTree`: Convert itself into a SymbolTree for pretty-printing, which is used to generate
     human-readable string representations of expressions.
   * `TextualSubstitution`: Perform substitution of variables within the expression, a fundamental operation in
     logic.


* Expression Types: These are discriminated unions that represent the different kinds of expressions in Wybe:
   * `Proposition`: Represents logical formulas, including True, False, And, Or, Not, Implies (⇒), Equiv (≡), and
     quantifiers.
   * `Integer`: Represents integer arithmetic, including constants, Plus, Minus, Times, and predicates like
     Exceeds (>) and AtLeast (≥).
   * `Sequence`: Represents sequences (lists) with operations like Cons (::), Concat (++), Length (#), Head, and
     Tail.
   * `Quantifier`: Represents quantified expressions like ∀ (Forall) and ∃ (Exists).
   * `Var`, `FnDecl`, `FnApp`: Represent variables, function declarations, and function applications,
     respectively.


* Proof Structure Types:
   * `Law`: A named proposition, essentially a theorem or axiom that can be used as a premise in a proof.
   * `Step`: A single step in a proof. It connects a fromExp to a toStep using an operator (like ≡ or ⇒) and is
     justified by a list of Laws.
   * `Calculation`: Represents an entire proof, containing the demonstrandum (the statement to be proven) and a
     list of Steps.
   * `CheckedCalculation`: The result of a proof check, which wraps the original Calculation and an optional
     WybeError if the proof failed.


Core Logic and Z3 Integration

The magic happens in how these data structures are used to verify proofs.


1. Translation to Z3: The ToZ3Expr method is called recursively on a WExpr to build an equivalent expression tree
  within the Z3 solver's context. For example, a Wybe And(p, q) becomes a Z3 ctx.MkAnd(p', q').


2. Checking a Single Step: The checkStep function is responsible for verifying one line of a proof. It works as
  follows:
   * It creates a new Z3 solver instance.
   * It takes all the Laws used as justification for the step and asserts them as assumptions in the solver.
   * It formulates the step itself as a proposition to be proven (e.g., fromExpr ≡ toExpr).
   * It then asks Z3 to prove this proposition given the assumptions. It does this by asserting the negation of
     the proposition and checking if the solver finds the system UNSATISFIABLE. If it is, the original
     proposition must be true (a proof by contradiction).


3. Computation Expressions (DSL): To make writing proofs feel natural in F#, the file implements computation
  expression builders:
   * `proof { ... }` (`CalculationCE`): This builder allows a user to write a proof as a sequence of expressions
     and "hints." It parses this sequence, constructs the Calculation object, and then automatically runs the
     verification logic.
   * `≡ { ... }`, `⇒ { ... }`, etc. (`LawsCE`): These builders provide a clean syntax for providing the "hints"
     or justifications for a proof step. They collect a list of laws, axioms, or even previously proven theorems
     (from a CheckedCalculation) to be used as premises.


A particularly advanced feature is the extractPatternFromRecurrence function. When dealing with recursive
functions in quantified expressions (like the definition of Fibonacci), Z3 needs help to know how to expand the
recursion. This function analyzes the expression and automatically generates "patterns" to guide Z3, which is
crucial for proving properties of recursive definitions.

Summary


Prover/Core.fs defines a sophisticated embedded DSL for formal verification in F#. It combines a well-defined set
of F# types to represent mathematical and logical expressions with the power of the Z3 SMT solver. The
architecture is clean and powerful, abstracting the complexities of the Z3 API behind a much more expressive and
readable syntax for writing and automatically checking formal proofs.
