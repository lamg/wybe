# Checking a step

Each step is composed of an expression and a hint that connects it to the next step's expression:

```
current_expression
≡ { law }
next_expression
```

To check a step we apply a Leibniz inference rule derived from a law like `x = y ⇒ f.x = f.y`. Thus the above step, seen through the lens of a Leibniz inference rule is:

```fsharp
f.x
= { x = y }
f.y
```

In order to apply Leibniz correctly we need to identify `x` in the original expression, which would lead to defining `f.x` as the surrounding expression of `x`. For example in an expression `(a ≡ b) ∧ (a ≡ b)` we can identify `x` as `a ≡ b`, thus we would get the definition `f.x = x ∧ x`. If we have a law like `x ∧ x ≡ x` in the hint, then we rewrite `x ∧ x` as `x`, giving the new definition `f.x = x`. In conjunction with our identification of `x` as `a ≡ b`, the resulting expression would be `a ≡ b`. See the step below for more clarity:

```fsharp
  (a ≡ b) ∧ (a ≡ b) // f.x = x ∧ x
≡ { x ∧ x ≡ x } // x = a ≡ b
  a ≡ b // f.x = x
```

The implementation consists in splitting the law by the hint operator, in this case `≡`. This creates a rewriter, a value that has two internal fields `lhs = x ∧ x` and `rhs = x`, which is used to match `lhs` against the original expression giving a list of bindings for each matched free variable like `x = a ≡ b`. The bindings are then used to rewrite the `rhs` component, resulting in `a ≡ b` in this case. This is then substituted in the subtree where the `lhs` match was found to get the final expression. Since this match can happen in several places in the original expression, then checking a step consist in finding the next step's expression among the list of possible rewrites.

A hint can produce more than one rewriter, when you have more than one law, thus rewriting the original expression creates a tree and checking the step consists in finding a path to the next step's expression. Using F# it's possible to visualize this process by inspecting the steps of a calculation. Let's do it for the following proof:

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

Now the rewriter `x ≡ x ↦ true` is applied to each children. The final expression tree looks like:

```
(p ≡ q) ≡ (q ≡ p) ✅0
  ├── (q ≡ p) ≡ (p ≡ q) ❌
  ├── (q ≡ p) ≡ (q ≡ p) ✅0
  │   └── true ✅0
  └── (p ≡ q) ≡ (p ≡ q) ✅1
     └── true ✅1
```


## Checking transitivity between steps

## Checking ransitivity result as evidence for proving theorem