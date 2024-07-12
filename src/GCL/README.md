# Wybe Guarded Command Language

Wybe Guarded Command Language is a language based on [Edgser W. Dijkstra's Guarded Command Language][GCL]

Features
- No global state. State mutation is restricted to declared variables inside procedures.
- [Procedures](#procedures)
- [States](#states)
- [Alternative statement](#alternative-statement)
- Skip statement
- [Repetition statement](#repetition-statement)
- Assignment statement
- [Statement composition](#statement-composition)

Basic types:
- Arrays
- Numbers (int64, nat64, int32, nat32, float32)
- Booleans
- Strings

## Procedures

```ebnf
proc = PROC input identifier output body END.
input = record_body.
output = record_body.
```

Example:
```
proc factorial {n ∈ nat32} {r ∈ nat32}
    …
end
```

## States

States can be defined, transformed and matched with the following syntax

```ebnf
field_decl = field ELEMENT_OF type.
member_decl = field_decl | bool_expr.
state_body = LBRACE (member_decl (AND|OR))* member_decl RBRACE.
```

Example:
```
{name ∈ string ∧ age ∈ nat32 ∧ age < 120}
```

## Alternative statement

Context is a record meant to declare a destructor for union types

```ebnf
alternative = IF context guard+ FI
```

Example
```
set bool = {true, false}
state Line = { length ∈ float32 }
state Circle = { radius ∈ float32 }
state Figure = Circle | Line
state float32_opt = { def ≡ value ∈ float32 }

proc {f ∈ Figure} area {area ∈ float32_opt }
   open f
   if
   | radius → area := { value = radius² × π }
   | _ → area := { def = false }
   fi
end

proc { n ∈ nat32 } even { r ∈ bool } 
    open n % 2 // when an expression producing a set is opened, the if can match set elements
    if
    | 0 → r := true
    | 1 → r := false
    fi
end

proc { p ∈ bool ∧ q ∈ bool} implies { r ∈ bool } 
    if
    | ¬p ⇒ q → true
    | _ ⇒ false
    fi
    // assigns the result value to the closest variable with the same type inferred from guards
end
```

## Repetition statement

Context is a record meant to declare values local to the scope of the loop, like invariants and counters

```ebnf
repetition = DO context guard+ OD
```

Example
```
proc { n ∈ nat32 ∧ m ∈ nat32 ∧ m ≠ 0 } gcd { m ∈ nat32 }
    do
    | n < m → m := m - n
    | m < n → n := n - m
    od
end

proc { xs ∈ nat32_array } plus1 { xs ∈ nat32_array }
    open xs // members of xs become local (i, x, length)
    do
    | i ≠ length -> x, i := x + 1, i + 1
    od
end
```

## Statement composition

```ebnf
stat0 [context_transformation] [SEMICOLON] stat1
```

```
proc { xs ∈ nat32_array } times2 { ys ∈ nat32_array ∧ (xs.i = ys.i ⇒ ys.x = xs.x * 2) }
    i → {xs.i, ys.i} // the effect on i propagates to xs.i and ys.i
    ys.length, i := xs.length, 0
    
    open xs // members of xs become local (i, x, length)
    do
    | i ≠ length → ys.x, i := x * 2, i + 1
    od
    i := 0
end

proc {xs: nat32_array } plus1_times2 {xs: nat32_array }
    plus1 // captures a variable of the same type and name from context
    // a record expression can be introduced here to modify the context in case automatic capture
    // doesn't work
    times2 // captures a variable of the same type and name from context, after being modified by plus1
end
```

In expressions like `proc0 + proc1`, `+` acts like a special composition statement since it captures the output of
`proc0` and passes it to the input of `proc1`, only if there's no ambiguity and types can be matched.

The general composition statement is `;`, which can be omitted when putting `proc0` and `proc1` in subsequent lines.

## Arrays

```
state nat32_array = { length ∈ nat32 ∧ 0 ≤ i ≤ length  ⇒  x ∈ nat32 }
```

[GCL]: https://en.wikipedia.org/wiki/Guarded_Command_Language