# Checking a step

Each step is composed of an expression and a hint that connects it to the next step's expression:

```
step
≡ { law }
next_expression
```

To check a step we apply a Leibniz inference rule derived from a law like `x = y ⇒ f.x = f.y`. Thus the above step, seen through the lens of a Leibniz inference rule is:

```
f.x
= { x = y }
f.y
```

The implementation consists in splitting the law, an expression like `x = y`, by the operator `=` and creating a rewritter, which has a left hand side and a right hand side expressions. It's a value that looks like `{lhs = x; rhs = y}`.

Then we find matches of the rewriter's `lhs` in the expression `f.x`. Each match binds a list of free variables in the `lhs` expression, i.e. a list that looks like `[ {freeVar = x; expr = p ∧ q}; {freeVar = y; expr = p ∧ q} ]`. Each free variable with its expression is then substituted in `rhs`.

At this point in every match of `lhs` in `f.x` we can replace our transformed `rhs` to obtain `f.y`. Since the match can happen in many places of the expression `f.x`, there is a list of alternative `f.y` expressions. If the one appearing in the step exists in that list, then the step is checked correctly.

Let's see a detailed example:

```wybe
  p ∧ ((a ≡ b) ∨ true)
≡ { ∨ symmetry }
  q ∧ (true ∨ (a ≡ b))
```

For checking this step we have the Leibniz inference rule derived from `x ≡ y ⇒ f.x ≡ f.y`, which is applicable to this step because of the hint operator `≡`.

`∨ symmetry` is defined as `x ∨ y ≡ y ∨ x`, which is splitted by `≡` as determined in the above Leibniz inference rule, in the subexpression `x ≡ y`. The generated rewriter is `{ lhs = x ∨ y; rhs = y ∨ x }`.

The result of matching `x ∨ y` in the first expression binds the free variables `x` and `y` as follows: `x: a ≡ b`, `y: true`. Now with those bindings, rewritting `rhs` results in `true ∨ (a ≡ b)`. Then `rhs` is substituted where the match was found and we get  `x ∧ (true ∨ (a ≡ b))` which is the expected expression.

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

## Checking transitivity between steps

## Checking ransitivity result as evidence for proving theorem