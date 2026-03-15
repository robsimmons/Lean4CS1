```lean
-- FPCourse/Unit1/Week01_ExpressionsTypesValues.lean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Basic
```

# Week 1: Expressions, Types, and Values

## The central idea of this course

Every expression in Lean has a *type*.  Types do two jobs at once.

- **Computational types** classify data: `Nat`, `Bool`, `String`,
  `Nat × Bool`.  A value of a computational type can be evaluated.

- **Logical types** (also called *propositions*) classify *claims*.
  A value of a logical type is a *proof* that the claim holds.

These two jobs are performed by the same language using the same
syntax.  That identity — programs and proofs living in one world — is
the deepest idea in the course.  You will see it demonstrated in every
week that follows.  By Week 14 you will have a name for it.
```lean
namespace Week01
```

## 1.1  Computational types
```lean
-- Every literal has a type.  Use #check to inspect it.
#check (42 : Nat)        -- Nat
#check (true : Bool)     -- Bool
#check ("hello" : String)

-- Functions have arrow types.
#check Nat.succ          -- Nat → Nat
#check Nat.add           -- Nat → Nat → Nat

-- #eval runs computation.
#eval Nat.succ 7         -- 8
#eval Nat.add 3 4        -- 7
#eval true && false      -- false  (Bool operations)
```

## 1.2  The Bool / Prop distinction

`Bool` is a two-element computational type: values `true` and `false`.
It is the type of the result of a test you can *run*.

`Prop` is the type of *logical claims*.  A term of type `P : Prop` is
a *proof* that P holds.  `Prop` is not two-valued; some propositions
have no proof (they are false), some have many proofs.

**This is the most important type-level distinction in Lean.**
```lean
-- Bool: a computed result.
#eval (2 == 3 : Bool)       -- false  (uses BEq instance)
#eval (2 < 5 : Bool)        -- true   (uses DecidableLT)

-- Prop: a logical claim.
#check (2 = 3 : Prop)       -- 2 = 3 : Prop
#check (2 < 5 : Prop)       -- 2 < 5 : Prop
#check (∀ n : Nat, n + 0 = n)   -- Prop
#check (∃ n : Nat, n > 100)     -- Prop

-- A proof of a Prop is a term of that type.
-- `rfl` proves any claim of the form `a = a` when both sides
-- reduce to the same value by computation.
example : 2 + 2 = 4 := rfl
example : Nat.succ 7 = 8 := rfl
```

## 1.3  `decide`: mechanically proving decidable propositions

Some propositions are *decidable*: there is an algorithm that always
produces either a proof or a refutation.  For those propositions, the
term `decide` acts as an automatic proof producer.

`decide` is a *term*, not a command.  It inhabits a type `P : Prop`
whenever `P` has a `Decidable` instance and reduces to `true`.  The
compiler checks this at elaboration time.  If `P` reduces to `false`,
the file fails to compile.

This is mechanical verification in its most direct form: the claim is
part of the type, and the compiler certifies it.
```lean
-- decide proves concrete decidable propositions.
example : 2 + 2 = 4 := by decide
example : ¬ (3 = 5) := by decide
example : 2 < 100 := by decide
example : 10 % 3 = 1 := by decide

-- decide on a list: ∀ over a finite collection is decidable
-- when the predicate is decidable.
example : ∀ x ∈ ([1, 2, 3] : List Nat), x < 10 := by decide
example : ∃ x ∈ ([1, 2, 3] : List Nat), x > 2  := by decide

-- If the claim is FALSE, the file will not compile.
-- Uncomment the next line to see the error:
-- example : 2 + 2 = 5 := decide
```

## 1.4  Product types

A product type `α × β` pairs a value of type `α` with a value of type `β`.
```lean
def myPair : Nat × Bool := (7, true)

#check myPair.1    -- Nat
#check myPair.2    -- Bool
#eval  myPair.1    -- 7
#eval  myPair.2    -- true

-- Nested products
def triple : Nat × Bool × String := (3, false, "hi")
#eval triple.1          -- 3
#eval triple.2.1        -- false
#eval triple.2.2        -- "hi"
```

## 1.5  Proof-carrying types: a first look

Here is a function that divides two natural numbers.  The *type*
of the second argument includes a condition: a proof that the divisor
is nonzero must be supplied by the caller.

```lean
def safeDiv (a : Nat) (b : Nat) (h : b ≠ 0) : Nat := a / b
```

The type `b ≠ 0` is a proposition — a logical type.  Calling
`safeDiv` does not just pass a number; it passes a *proof* that the
number is nonzero.  The compiler enforces this before the program runs.

This pattern — conditions embedded in types, enforced at compile time —
is what we mean by *proof-carrying types*.  You will see it everywhere
from Week 2 onward.
```lean
def safeDiv (a : Nat) (b : Nat) (h : b ≠ 0) : Nat := a / b

-- To call safeDiv we must supply a proof that the divisor ≠ 0.
-- For a concrete nonzero literal, `decide` produces the proof.
#eval safeDiv 10 2 (by decide)   -- 5
#eval safeDiv 17 3 (by decide)   -- 5

-- Attempting safeDiv 10 0 would require a proof of 0 ≠ 0,
-- which is false.  `decide` would refuse, and the file would
-- not compile.
```

## 1.6  Type derivation rules (summary)

| Syntax | Type |
|--------|------|
| `n : Nat` | `Nat` |
| `b : Bool` | `Bool` |
| `(a, b) : α × β` | `α × β` |
| `f : α → β`, `x : α` | `f x : β` |
| `P : Prop`, proof `h : P` | `h : P` |
| `decide` (when `[Decidable P]`) | `P` |

Reading types is the foundational skill of this course.
Every week adds new type constructors to this table.

## Exercises

1. Use `#check` to find the types of `List.length`, `List.append`,
   and `Nat.rec`.

2. Write a product type that pairs a `String` with a `Nat`.
   Construct a value of that type.

3. Write `example : 7 * 6 = 42 := _` and replace `_` with the
   correct proof term.

4. Write `example : ∀ x ∈ [2, 4, 6], x % 2 = 0 := _` and supply
   the proof.

5. Why can't you write `example : (1.0 : Float) = 1.0 := decide`?
   (Hint: think about what equality on `Float` would require.
   We will return to this in Week 7.)
```lean
end Week01
```

