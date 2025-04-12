# Checking a step

Each step is composed of an expression and a hint that connects it to the next step's expression:

```
step
≡ { law }
next_expression
```

checking a step consists in splitting a law by the current hint operator, in this case `≡`, to create a rewriter which is composed of a left hand side `lhs` and right hand side `rhs`. The `lhs` is used to match the expression tree in `step`, once a match is found `rhs` is transformed and replaced in the original expression tree. If one of the many generated expressions is `next_expression` then the step is checked. Let's examine an example:

```wybe
  x ∧ ((a ≡ b) ∨ true)
≡ { ∨ symmetry }
  x ∧ (true ∨ (a ≡ b))
```

`∨ symmetry` is `x ∨ y ≡ y ∨ x`, which is splitted by `≡` since it's the hint's operator. The generated rewriter is `{ lhs = x ∨ y; rhs = y ∨ x }`.

The result of matching `x ∨ y` in the first expression binds the free variables `x` and `y` as follows: `x: a ≡ b`, `y: true`. Now with those bindings `rhs` results in `true ∨ (a ≡ b)`. Then `rhs` is substituted where the match was found and we get  `x ∧ (true ∨ (a ≡ b))` which is the expected expression.

Using F# it's possible to visualize this process by inspecting the steps of a calculation. Let's do it for the following proof:

```fsharp
proof () {
  Theorem("true theorem", True)
  WithLaws [ ``≡ sym`` ]
  p === q === (q === p)
  
  ``≡`` {
      ``≡ sym``
      ``≡ ident``
  }
  
  True
}
|> inspect
|> stepAt 0
|> print
```

this produces the output:

```
step at: 0
alt_0: 
  rewriter: 
  x ≡ y ↦ y ≡ x
  x ≡ x ↦ true
  expansion: 
  (p ≡ q) ≡ (q ≡ p) ✅0
  ├── (q ≡ p) ≡ (p ≡ q) ❌
  ├── (q ≡ p) ≡ (q ≡ p) ✅0
  │   └── true ✅0
  └── (p ≡ q) ≡ (p ≡ q) ✅1
     └── true ✅1
```

there you can see how the law `(x ≡ y) ≡ (y ≡ x)` produces the rewriter `x ≡ y ↦ y ≡ x`. Applying it to the first expression creates a subtree:

```
(p ≡ q) ≡ (q ≡ p) ✅0
  ├── (q ≡ p) ≡ (p ≡ q) ❌
  ├── (q ≡ p) ≡ (q ≡ p) ✅0
  └── (p ≡ q) ≡ (p ≡ q) ✅1
```

The root of the tree is marked with `✅0` because a solution was found in the path `0`, also in the path `1` but `0` was the first.

Now the rewritter `x ≡ x ↦ true` is applied to each children. For the last two we get the expected expression:

```
(q ≡ p) ≡ (q ≡ p) ✅0
└── true ✅0
```

```
(p ≡ q) ≡ (p ≡ q) ✅1
└── true ✅1
```