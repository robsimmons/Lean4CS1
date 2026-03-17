-- Distillate/Unit1/Week02_ProductTypesConjunction.lean
import Mathlib.Logic.Basic
import Mathlib.Data.Prod.Basic

/-! @@@
# Week 2: Product Types and Conjunction

## Bundling two things at once

The second constructor in our table is the *product type* `α × β`.
A value of type `α × β` contains *both* an `α` *and* a `β` — held
together, retrieved separately.

**Computational reading.**  `α × β` is the type of pairs `(a, b)`
where `a : α` and `b : β`.  It models any situation where you need to
carry two pieces of data together: a name and a score, a point's
x-coordinate and y-coordinate, a key and its value.

**Logical reading.**  When `P` and `Q` are propositions, `P × Q` (or
equivalently `P ∧ Q`) is the type of proofs that *P is true AND Q is
true simultaneously*.  A term of this type packages a proof of P
together with a proof of Q.

Same constructor.  Two readings.  One type system.
@@@ -/

namespace Week02

/-! @@@
## 2.1  Pairs: the anonymous product

The simplest product is an anonymous pair `(a, b)`.
The type is written `α × β`.
@@@ -/

-- Constructing pairs
def myPair : Nat × Bool := (7, true)
def point  : Nat × Nat  := (3, 4)
def label  : String × Nat := ("score", 100)

-- Projecting: extract the first or second component
#eval myPair.1    -- 7
#eval myPair.2    -- true
#eval point.1     -- 3
#eval point.2     -- 4

-- Pairs in function types: a function that returns two things
def minMax (a b : Nat) : Nat × Nat :=
  if a ≤ b then (a, b) else (b, a)

#eval minMax 7 3    -- (3, 7)
#eval minMax 2 9    -- (2, 9)

/-! @@@
## 2.2  Named products: structures

Lean's `structure` keyword gives names to the fields of a product.
This is more readable than anonymous pairs for anything but small,
transient bundles.
@@@ -/

-- A named product: a 2D point
structure Point where
  x : Nat
  y : Nat

-- Constructing a Point
def origin : Point := { x := 0, y := 0 }
def p1     : Point := { x := 3, y := 4 }

-- Accessing fields by name
#eval p1.x    -- 3
#eval p1.y    -- 4

-- Using point in a function
def translate (p : Point) (dx dy : Nat) : Point :=
  { x := p.x + dx, y := p.y + dy }

#eval (translate p1 1 2).x   -- 4
#eval (translate p1 1 2).y   -- 6

/-! @@@
A `structure` is syntactic sugar for an inductive type with a single
constructor.  `Point` is equivalent to `α × β` but with field names
instead of `.1` and `.2`.

The key idea: a structure value holds ALL its fields simultaneously.
To have a `Point`, you must supply BOTH `x` AND `y`.
@@@ -/

/-! @@@
## 2.3  Product types and conjunction: the logical reading

When `P` and `Q` are propositions, `P ∧ Q` (read "P and Q") is the
proposition that BOTH P AND Q are true.

In Lean's type theory, `P ∧ Q` is definitionally `P × Q` in `Prop`.
A proof of `P ∧ Q` is a pair: a proof of P bundled with a proof of Q.

The connective `∧` is the logical reading of the same product constructor
that gives you pairs and structures on the computational side.
@@@ -/

-- A conjunction: both claims are true
#check (by decide : 1 + 1 = 2 ∧ 2 + 2 = 4)
#check (by decide : true = true ∧ false = false)

-- Constructing a conjunction manually with And.intro
-- And.intro takes a proof of P and a proof of Q; returns a proof of P ∧ Q
theorem conj_example : 1 + 1 = 2 ∧ 2 + 2 = 4 :=
  And.intro rfl rfl

-- Destructuring: if you have a proof of P ∧ Q, you can extract each part
theorem extract_left  (h : 1 + 1 = 2 ∧ 2 + 2 = 4) : 1 + 1 = 2 := h.left
theorem extract_right (h : 1 + 1 = 2 ∧ 2 + 2 = 4) : 2 + 2 = 4 := h.right

-- In practice, decide constructs the proof for decidable conjunctions
#check (by decide : 3 < 5 ∧ 5 < 10)

/-! @@@
The table of correspondences so far:

| Data | Logic |
|------|-------|
| `(a, b) : α × β` | proof of `P ∧ Q` |
| `Prod.mk a b` | `And.intro hp hq` |
| `.1` (first projection) | `.left` |
| `.2` (second projection) | `.right` |

The names differ but the structure is identical.  This is not coincidence.
@@@ -/

/-! @@@
## 2.4  Proof-carrying types

One of the most powerful ideas in this course is *proof-carrying types*:
embedding a logical condition directly into a data type.

Instead of a raw `Nat`, you can demand a `Nat` bundled together with a
proof that it satisfies some property.
@@@ -/

-- A type that packages a Nat together with a proof that it is even
def EvenNat : Type := { n : Nat // n % 2 = 0 }

-- To construct an EvenNat, you must supply the number AND the proof
def four_is_even : EvenNat := ⟨4, by decide⟩
def zero_is_even : EvenNat := ⟨0, by decide⟩

-- The value part and proof part are always available
#eval four_is_even.val    -- 4
-- four_is_even.property : 4 % 2 = 0  (a proof term, not a value to print)

/-! @@@
The `{ n : Nat // P n }` notation is Lean's *subtype*: the type of
natural numbers satisfying predicate `P`.  It is a dependent product:
the proof depends on which number you chose.

This is precisely the connection between programs and specifications.
When a function returns `{ n : Nat // n % 2 = 0 }`, its return type
itself guarantees the postcondition.  The type IS the specification.
@@@ -/

-- A function whose return type guarantees the postcondition
def double_with_proof (n : Nat) : { m : Nat // m = n * 2 } :=
  ⟨n * 2, rfl⟩

#eval (double_with_proof 5).val   -- 10
-- (double_with_proof 5).property : 10 = 5 * 2  (guaranteed by the type)

/-! @@@
## 2.5  Products in specifications

Product types appear naturally in function specifications whenever a
function must satisfy multiple independent conditions at once.

If a function `f : α → β × γ` must return both a `β` and a `γ`, then
you can specify each component independently using `∧`.
@@@ -/

-- A function that splits a number into quotient and remainder
def divmod (n d : Nat) : Nat × Nat := (n / d, n % d)

-- Specification: both components must be correct
theorem divmod_spec (n d : Nat) (hd : d ≠ 0) :
    let (q, r) := divmod n d
    n = q * d + r ∧ r < d := by
  simp [divmod]
  omega

#eval divmod 17 5   -- (3, 2):  17 = 3 * 5 + 2  and  2 < 5

/-! @@@
## Summary

- `α × β` is the **product type**: holds a value of type `α` AND a value of type `β`.
- **Pairs**: `(a, b)`, accessed with `.1` and `.2`.
- **Structures**: named fields; syntactic sugar for products.
- **`P ∧ Q`** (conjunction) is the logical reading of the same product:
  a proof holds a proof of P AND a proof of Q.
- **`And.intro`** constructs a conjunction; `.left`/`.right` destruct it.
- **`decide`** produces proofs of decidable conjunctions automatically.
- **Proof-carrying types** embed guarantees directly into the type:
  `{ n : Nat // P n }` requires supplying the value AND its proof.
@@@ -/

end Week02
