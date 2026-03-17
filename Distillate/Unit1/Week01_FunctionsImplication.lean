-- Distillate/Unit1/Week01_FunctionsImplication.lean
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Basic

/-! @@@
# Week 1: Functions and Implication

## The arrow that does double duty

The symbol `→` appears in two places that turn out to be one place.

**Computational reading.**  `α → β` is the type of functions that take an
input of type `α` and return a result of type `β`.

**Logical reading.**  When `P` and `Q` are propositions, `P → Q` is the
type of proofs that *P implies Q*.  A term of this type converts any proof
of `P` into a proof of `Q`.

These are not two different symbols.  One symbol, two readings.
A function *is* an implication proof.
An implication proof *is* a function.

This identity is the heart of the Curry-Howard correspondence.
We will name it explicitly in Week 8.  For now, we live it.
@@@ -/

namespace Week01

/-! @@@
## 1.1  Defining functions

A function definition names the function, lists its parameters with their
types, states the return type, and gives the body expression.
@@@ -/

-- Basic function definitions
def double (n : Nat) : Nat := n * 2
def square (n : Nat) : Nat := n * n
def increment (n : Nat) : Nat := n + 1

#eval double 5      -- 10
#eval square 7      -- 49
#eval increment 0   -- 1

-- Anonymous functions (lambdas) — the same thing without a name
#eval (fun n => n * 2) 5        -- 10
#eval (fun n => n * n) 7        -- 49

-- The type of double is Nat → Nat
#check double    -- double : Nat → Nat
#check square    -- square : Nat → Nat

/-! @@@
## 1.2  The reduction model for function application

When you apply a function to an argument, Lean substitutes the argument
for the parameter throughout the body.  This is called *β-reduction*.

```
  double 5
  ↝ (fun n => n * 2) 5      -- unfold definition
  ↝ 5 * 2                   -- β-reduction: substitute 5 for n
  ↝ 10                      -- arithmetic
```

Every `#eval` on a function application is exactly this chain of steps.
@@@ -/

-- Multi-argument functions are curried: each argument consumed one at a time
def add (a b : Nat) : Nat := a + b

#check add        -- add : Nat → Nat → Nat
#eval add 3 4     -- 7

-- Partial application: supply only the first argument
#check add 3      -- add 3 : Nat → Nat   (still needs one more Nat)
#eval (add 3) 4   -- 7  (same as add 3 4)

/-! @@@
Currying means: `Nat → Nat → Nat` is really `Nat → (Nat → Nat)`.
`add 3` is a perfectly valid expression of type `Nat → Nat`.
Supplying the second argument finishes the computation.
@@@ -/

/-! @@@
## 1.3  Type signatures as specifications

A function's *type signature* is more than bookkeeping.  It is a
machine-checked claim about what the function can accept and what it
must return.

```
def double (n : Nat) : Nat := ...
```

This says: *given any natural number, produce a natural number.*
Lean verifies that every definition lives up to its signature.
The type IS the specification — enforced, not advisory.

For a stronger specification, we move from the *type* of the function to
a *proposition* about it.  We will explore this fully in Week 7.
For now, notice that `#check` surfaces the type, and `#eval` checks the
output on concrete inputs.
@@@ -/

-- The type says what; the body says how
def max2 (a b : Nat) : Nat := if a ≥ b then a else b

#eval max2 3 7    -- 7
#eval max2 9 2    -- 9
#eval max2 5 5    -- 5

/-! @@@
## 1.4  → as implication: the logical reading

When `P` and `Q` are propositions (terms of type `Prop`), `P → Q` is
the claim "if P then Q."  A proof of `P → Q` is a function that takes
any proof of `P` and returns a proof of `Q`.

The syntax is identical to a function definition — because it IS a
function definition.
@@@ -/

-- Logical implication: if 1 + 1 = 2 then 2 + 2 = 4
-- A proof of this is a function from proofs of (1+1=2) to proofs of (2+2=4)
theorem implication_example : 1 + 1 = 2 → 2 + 2 = 4 :=
  fun _ => by decide   -- ignore the hypothesis; decide proves the conclusion directly

-- A more interesting implication: symmetry of equality
-- If a = b then b = a
theorem eq_symm_example (a b : Nat) : a = b → b = a :=
  fun h => h.symm       -- .symm reverses an equality proof

-- Universal quantification ∀ is also a function type
-- ∀ n : Nat, n + 0 = n   means   (n : Nat) → n + 0 = n
-- A proof is a function that takes any n and returns a proof of (n + 0 = n)
theorem add_zero_all : ∀ n : Nat, n + 0 = n :=
  fun n => Nat.add_zero n

-- decide can prove universally quantified propositions about finite domains
#check (by decide : ∀ b : Bool, b || true = true)

/-! @@@
**Unpacking the universal quantifier.**  The notation `∀ n : Nat, P n`
is definitionally equal to `(n : Nat) → P n`.  A proof is a function.
You have been writing proofs since the first example in this section.
@@@ -/

/-! @@@
## 1.5  The design recipe

Every function in this course follows the same design steps.
The recipe makes specification explicit at each stage.

1. **Description** (English): what does the function do?
2. **Signature**: what are the input and output types?
3. **Specification**: what proposition must the function satisfy?
4. **Examples**: what does it do on concrete inputs?
5. **Implementation**: the body of the definition.

The specification step is where Lean distinguishes this course from
ordinary programming.  We do not merely test; we state a logical claim
and (using `decide` for decidable propositions) verify it.
@@@ -/

-- Example: applying the design recipe to `double`

-- 1. Description: given a natural number, return twice that number.
-- 2. Signature:
def double2 (n : Nat) : Nat :=
-- 5. Implementation:
  n * 2

-- 3. Specification (a proposition that must hold):
--    For all n, double2 n = n + n
-- 4. Examples:
#eval double2 0    -- 0
#eval double2 3    -- 6
#eval double2 10   -- 20

-- Verification: decide proves the specification for any concrete n it can check
#check (by decide : double2 0 = 0 + 0)
#check (by decide : double2 3 = 3 + 3)
#check (by decide : double2 10 = 10 + 10)

-- And universally (decide works over finite domains; Nat is infinite so
-- the universal claim needs a general proof — we'll explore this in Week 7):
theorem double2_spec : ∀ n : Nat, double2 n = n + n := by
  intro n; ring

/-! @@@
## 1.6  Functions to any type

Functions can map between any two types, not just `Nat → Nat`.
They can take propositions as inputs or produce propositions as outputs.
They can take types as inputs (polymorphism — more in Week 3).
@@@ -/

-- Bool → Bool
def boolNot (b : Bool) : Bool := !b
#eval boolNot true   -- false

-- Nat → Bool (a predicate)
def isZero (n : Nat) : Bool := n == 0
#eval isZero 0   -- true
#eval isZero 5   -- false

-- String → Nat
def wordLength (w : String) : Nat := w.length
#eval wordLength "hello"   -- 5

-- Nat → String  (using Lean's built-in conversion)
def showNat (n : Nat) : String := toString n
#eval showNat 42   -- "42"

/-! @@@
## Summary

- `→` is the **function/implication type constructor**.
  - Computationally: `α → β` means "take an α, produce a β."
  - Logically: `P → Q` means "P implies Q"; a proof is a function.
- **`def f (x : α) : β := body`** defines a function named `f`.
- **Currying**: multi-argument functions `α → β → γ` can be partially applied.
- **Reduction**: applying a function substitutes the argument (β-reduction).
- **`∀ x : α, P x`** is the dependent function type `(x : α) → P x`.
  A proof of ∀ is a function.
- **The design recipe**: description → signature → specification → examples
  → implementation.  Specification is a proposition, enforced by Lean.
@@@ -/

end Week01
