import VersoManual

open Verso Doc
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
namespace Week02

#doc (Manual) "Week 2: Functions and Specifications" =>

# The dual reading of →
%%%
number := false
%%%

The arrow `→` has two readings that are always simultaneously true.

*Computational reading*: `α → β` is the type of functions from `α` to `β`.
A term of this type takes an input of type `α` and returns an output of
type `β`.

*Logical reading*: `P → Q` (where `P Q : Prop`) is the type of proofs
that P _implies_ Q.  A term of this type is a function that converts any
proof of P into a proof of Q.

These are not two different symbols.  They are one symbol with two
readings.  A function _is_ an implication proof; an implication proof _is_
a function.  This identity is the beginning of the Curry-Howard
correspondence, which we will name explicitly in Week 14.

# Defining functions

```lean
-- Named function definition
def double (n : Nat) : Nat := n * 2
def square (n : Nat) : Nat := n * n

-- Anonymous function (lambda)
def double' : Nat → Nat := fun n => n * 2

-- Multi-argument functions are curried by default
def add3 (a b c : Nat) : Nat := a + b + c
-- add3 has type Nat → Nat → Nat → Nat
-- Applying one argument returns a function: Nat → Nat → Nat

-- Evaluation (β-reduction): each application substitutes the argument.
--   add3 1 2 3
--   ↝ (fun a b c => a + b + c) 1 2 3
--   ↝ 1 + 2 + 3                        (three β-reductions)
--   ↝ 6
#eval add3 1 2 3    -- 6
#eval (add3 1) 2 3  -- same: (add3 1) is a Nat → Nat → Nat waiting for two more args
```

# → as implication: logical reading

When `P` and `Q` are propositions, `P → Q` is the claim that P implies Q.
A proof of `P → Q` is a function that takes any proof of P and returns a
proof of Q.  This is indistinguishable from an ordinary function — because
it _is_ an ordinary function.

```lean
-- A proof of P → Q is a term of type P → Q.
-- Here: "if n + 0 = n, then n = n + 0"
theorem add_zero_comm (n : Nat) : n + 0 = n → n = n + 0 :=
  fun h => h.symm

-- Universal claims: ∀ n : Nat, P n
-- This is also a function type: (n : Nat) → P n
-- A proof supplies the function.
theorem add_zero_all : ∀ n : Nat, n + 0 = n :=
  Nat.add_zero

-- The ∀ and → are the same thing: ∀ n, P n is (n : Nat) → P n
-- when P does not mention types not in scope.
```

# The design recipe

Every function in this course is designed using the following steps.
English descriptions are written as Lean _docstrings_ (`/-- ... -/`
placed immediately before a definition) so the tooling surfaces them
in hover text.

:::table
*
 * Step
 * Activity
*
 * 0. Description
 * Write a `/-- docstring -/` saying what the function does in plain English.
*
 * 1. Signature
 * Write the name, argument types, and return type.
*
 * 2. Specification
 * Write a `∀` proposition over the signature expressing what the output must satisfy.
*
 * 3. Examples
 * Write `#eval` checks with `-- expected` comments; once `#eval` is familiar, strengthen to `example : f x = v := rfl`.
*
 * 4. Template
 * Write the function body shape from the input types.
*
 * 5. Code
 * Fill in the body.
*
 * 6. Check
 * Verify the compiler accepts both the definition and the specification.
:::

The description comes first so you understand _what_ before _how_.
The signature must precede the specification — the spec names the
function, so the `def` must exist before the `theorem` can be stated.

```lean
-- Example: doubling a number.

-- Step 0 — Description:
/-- `double'' n` returns twice `n`. -/
-- Step 1 — Signature + Steps 4/5 Template and code:
def double'' (n : Nat) : Nat := n + n

-- Step 3 — Examples (two forms):
-- Form 1: #eval with expected value in comment (explore interactively)
#eval double'' 0    -- 0
#eval double'' 5    -- 10
-- Form 2: rfl-based test (machine-verified; both sides evaluate to the same normal form)
example : double'' 0 = 0  := rfl
example : double'' 5 = 10 := rfl

-- Step 2 — Specification (stated after the def, since it names double''):
--   ∀ n : Nat, double'' n = n + n
-- Step 6 — Check (provided proof):
-- Evaluation: double'' n ↝ n + n (δ-reduction).  Both sides are identical.
theorem double''_spec : ∀ n : Nat, double'' n = n + n :=
  fun n => rfl
```

# Function composition

```lean
-- ∘ is function composition: (f ∘ g) x = f (g x)
def double_then_square : Nat → Nat := square ∘ double

#eval double_then_square 3    -- square (double 3) = square 6 = 36

-- Composition and identity satisfy algebraic laws.
-- These are propositions about functions — logical types.
theorem comp_id (f : α → β) : f ∘ id = f := rfl
theorem id_comp (f : α → β) : id ∘ f = f := rfl
theorem comp_assoc (f : γ → δ) (g : β → γ) (h : α → β) :
    (f ∘ g) ∘ h = f ∘ (g ∘ h) := rfl
```

# Connectives as types

Logical connectives are type constructors.  A proposition built with a
connective has the same structure as a product or sum type in computation.

:::table
*
 * Connective
 * Type constructor
 * Introduction
*
 * `P ∧ Q`
 * like `P × Q`
 * `And.intro : P → Q → P ∧ Q`
*
 * `P ∨ Q`
 * like `P ⊕ Q`
 * `Or.inl : P → P ∨ Q`
*
 * `¬P`
 * `P → False`
 * a function from P to absurdity
*
 * `P ↔ Q`
 * `(P → Q) × (Q → P)`
 * `Iff.intro`
:::

```lean
-- ∧ introduction: supply proofs of both conjuncts
example : 1 < 2 ∧ 2 < 3 :=
  And.intro (by decide) (by decide)

-- ∨ introduction: supply a proof of one disjunct
example : 1 = 1 ∨ 1 = 2 :=
  Or.inl rfl

-- ¬P is P → False
example : ¬ (1 = 2) :=
  by decide

-- ↔ introduction: supply both directions
example : (1 + 1 = 2) ↔ (2 = 1 + 1) :=
  Iff.intro (fun h => h.symm) (fun h => h.symm)
```

# Reading function specifications

When a function's type contains propositions, the type IS the specification.
The examples below show how to read proof-carrying function types.

```lean
-- The type tells you: given a proof that the list is nonempty,
-- return the first element.  No runtime null check needed.
#check List.head   -- (l : List α) → l ≠ [] → α
-- (Actual Lean name may vary; the pattern is the point.)

-- The type tells you: given proofs about the index being in bounds,
-- return the element at that index.
#check List.get    -- (l : List α) → Fin l.length → α
-- Fin n is the type of natural numbers < n.  It IS the bounds proof.
```

# Exercises
%%%
number := false
%%%

1. Write a function `pred' : Nat → Nat` that returns the predecessor,
   treating 0 as 0.  Write its specification as a ∀ proposition.

2. What is the type of `And.intro`?  Use `#check` to find out.
   Explain in English what a term of that type represents both
   computationally and logically.

3. Use `#print Iff` to inspect the definition of `↔`.  What are its
   two fields?  Use `decide` to verify:
   1. `(2 < 3) ↔ ¬(3 ≤ 2)`
   2. `(True ∧ True) ↔ True`
   3. `(True ∧ False) ↔ False`

   For each, state in English what the biconditional asserts.

4. Use `decide` to verify `¬ (True ∧ False)`.
   Then explain: what is the type of `¬ (True ∧ False)` in full,
   unfolding `¬` to `→ False`?

5. State (as a Lean `Prop`) the specification for a function
   `max' : Nat → Nat → Nat` that returns the larger of two numbers.
   Your specification should assert: (a) the result is ≥ both inputs,
   and (b) the result equals one of the two inputs.
