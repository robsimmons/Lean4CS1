-- Distillate/Unit1/Week03_SumTypesDisjunction.lean
import Mathlib.Logic.Basic

/-! @@@
# Week 3: Sum Types and Disjunction

## Choosing between alternatives

The third constructor in our table is the *sum type* `α ⊕ β`.
A value of type `α ⊕ β` contains *either* an `α` *or* a `β` — never
both, never neither.  To use it, you must consider both cases.

**Computational reading.**  `α ⊕ β` models any situation where data
comes in two distinct forms: success or failure, North or South, a
number or a name.  The two forms are disjoint; you know which you have.

**Logical reading.**  When `P` and `Q` are propositions, `P ∨ Q`
(equivalently `P ⊕ Q` in `Prop`) is the claim that AT LEAST ONE of P
or Q is true.  A proof must commit to which one it is establishing.

Same constructor.  Two readings.  One type system.

In Lean, sum types are written using the `inductive` keyword.
`Bool` and `Option` are the canonical examples you will meet first.
@@@ -/

namespace Week03

/-! @@@
## 3.1  Bool: the simplest sum type

`Bool` is an inductive type with exactly two constructors, `true` and
`false`.  It is the sum type `Unit ⊕ Unit` with better names.
@@@ -/

-- Bool is defined in the standard library as:
--   inductive Bool : Type
--     | false : Bool
--     | true  : Bool

-- To use a Bool value, you must pattern-match on it
def boolToNat (b : Bool) : Nat :=
  match b with
  | true  => 1
  | false => 0

#eval boolToNat true   -- 1
#eval boolToNat false  -- 0

-- if/then/else is syntactic sugar for match on Bool
def boolToNat' (b : Bool) : Nat := if b then 1 else 0

/-! @@@
## 3.2  Defining your own sum types

The `inductive` keyword introduces a new type by listing its
*constructors* — the ways to build a value of that type.  A sum type
has multiple constructors; a product type has one constructor with
multiple fields.

Each constructor is a disjoint alternative.  Together, they cover
every possible value.
@@@ -/

-- A simple enumeration: four compass directions
inductive Direction
  | North
  | South
  | East
  | West

-- Pattern matching must cover all constructors
def opposite (d : Direction) : Direction :=
  match d with
  | Direction.North => Direction.South
  | Direction.South => Direction.North
  | Direction.East  => Direction.West
  | Direction.West  => Direction.East

-- open brings constructors into scope so you don't need the prefix
open Direction in
def isNorthSouth (d : Direction) : Bool :=
  match d with
  | North => true
  | South => true
  | East  => false
  | West  => false

-- Derived Bool operations: decide can reason about Direction
#check (by decide : opposite Direction.North = Direction.South)
#check (by decide : opposite (opposite Direction.East) = Direction.East)

/-! @@@
## 3.3  Option: the prototypical proof-carrying sum type

`Option α` is one of the most important types in functional programming.
It models computations that may or may not produce a value.

```lean
inductive Option (α : Type) : Type
  | none : Option α
  | some : α → Option α
```

`none` means "no value."  `some v` means "the value `v`."
@@@ -/

-- Safe list head: returns none if the list is empty
def head? (xs : List Nat) : Option Nat :=
  match xs with
  | []     => none
  | x :: _ => some x

#eval head? []          -- none
#eval head? [3, 1, 4]   -- some 3

-- Safe division: returns none if divisor is zero
def safeDiv (n d : Nat) : Option Nat :=
  if d = 0 then none else some (n / d)

#eval safeDiv 10 2    -- some 5
#eval safeDiv 10 0    -- none

-- Using an Option result: must pattern-match to handle both cases
def divOrZero (n d : Nat) : Nat :=
  match safeDiv n d with
  | none   => 0
  | some q => q

#eval divOrZero 10 2   -- 5
#eval divOrZero 10 0   -- 0

/-! @@@
`Option` is a disciplined way of expressing "might fail."
The type tells you that you MUST handle the `none` case.
There is no way to access the value without writing the pattern match.
@@@ -/

/-! @@@
## 3.4  Constructors with data

Constructors can carry payloads.  A sum type constructor is either a tag
(nullary, like `North`) or a tag together with stored data (like `some`).
@@@ -/

-- A result type: either an error message or a computed value
inductive Result (α : Type) : Type
  | error  : String → Result α
  | ok     : α → Result α

def safeSqrt (n : Int) : Result Float :=
  if n < 0
  then Result.error "cannot take square root of a negative number"
  else Result.ok (Float.sqrt n.toFloat)

-- Pattern-match to use the result
def showResult (r : Result Float) : String :=
  match r with
  | Result.error msg => "Error: " ++ msg
  | Result.ok v      => "Result: " ++ toString v

#eval showResult (safeSqrt 4)    -- "Result: 2.0"
#eval showResult (safeSqrt (-1)) -- "Error: cannot take sqrt of a negative number"

/-! @@@
## 3.5  Disjunction: the logical reading of sum types

When `P` and `Q` are propositions, `P ∨ Q` (read "P or Q") is the
claim that AT LEAST ONE of P or Q holds.

In Lean's type theory, `P ∨ Q` is definitionally `P ⊕ Q` in `Prop`.
A proof of `P ∨ Q` is either:
- `Or.inl hp` — a proof that the left disjunct P holds, or
- `Or.inr hq` — a proof that the right disjunct Q holds.

You commit to which side you are proving.  The type enforces this.
@@@ -/

-- Proving a disjunction: commit to the true side
theorem one_lt_two_or_one_gt_two : 1 < 2 ∨ 1 > 2 :=
  Or.inl (by decide)   -- 1 < 2 is true, so take the left

theorem two_eq_two_or_two_eq_three : 2 = 2 ∨ 2 = 3 :=
  Or.inl rfl           -- take the left (2 = 2)

-- decide handles decidable disjunctions automatically
#check (by decide : 1 = 1 ∨ 1 = 2)   -- true because 1 = 1

-- Destructuring a disjunction: case split on which side holds
theorem or_elim_example (h : 1 = 1 ∨ 1 = 2) : True :=
  match h with
  | Or.inl _ => True.intro   -- left case: 1 = 1, conclusion is trivially True
  | Or.inr _ => True.intro   -- right case: 1 = 2, conclusion is trivially True

/-! @@@
The table of correspondences so far:

| Data | Logic |
|------|-------|
| `Sum.inl a : α ⊕ β` | `Or.inl hp : P ∨ Q` |
| `Sum.inr b : α ⊕ β` | `Or.inr hq : P ∨ Q` |
| `match` on constructors | case analysis in a proof |
| `none` / `some` in `Option` | disjoint proof cases |

Exhaustive pattern matching in code IS the completeness condition for
disjunctive proofs.  The compiler ensures you handle every case.
@@@ -/

/-! @@@
## 3.6  Pattern matching: the elimination form for sums

Every time you use a sum-type value, you must pattern-match.
Pattern matching is the *elimination rule* for sum types: it consumes
a sum value by handling each possible constructor.

This is not optional.  You cannot reach inside a sum value without
declaring what you will do with both alternatives.  This exhaustiveness
requirement is enforced at compile time.
@@@ -/

-- Pattern matching on a custom inductive type
inductive Shape
  | Circle    : Float → Shape          -- radius
  | Rectangle : Float → Float → Shape -- width, height

def area (s : Shape) : Float :=
  match s with
  | Shape.Circle r       => Float.pi * r * r
  | Shape.Rectangle w h  => w * h

#eval area (Shape.Circle 1.0)           -- ≈ 3.14159
#eval area (Shape.Rectangle 3.0 4.0)   -- 12.0

-- If you forget a case, Lean errors:
-- def area' (s : Shape) : Float :=
--   match s with
--   | Shape.Circle r => Float.pi * r * r
--   -- ERROR: missing case Shape.Rectangle

/-! @@@
## Summary

- `α ⊕ β` (sum) holds *either* an `α` *or* a `β`; never both; never neither.
- **`inductive`** defines new sum types by listing constructors.
- **`Bool`**: the simplest sum — `true` or `false`.
- **`Option α`**: `none` (absent) or `some v` (present) — canonical "might fail."
- **Pattern matching** (`match`) is the elimination form for sum types;
  it must be exhaustive.
- **`P ∨ Q`** (disjunction) is the logical reading of the sum type:
  a proof commits to `Or.inl` (left) or `Or.inr` (right).
- **`decide`** produces proofs of decidable disjunctions automatically.
- Exhaustive case coverage in programs mirrors completeness in disjunctive
  proofs — one and the same requirement enforced by Lean.
@@@ -/

end Week03
