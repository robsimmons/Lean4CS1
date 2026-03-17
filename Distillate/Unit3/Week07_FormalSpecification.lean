-- Distillate/Unit3/Week07_FormalSpecification.lean
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Perm
import Mathlib.Logic.Basic

/-! @@@
# Week 7: Formal Specification

## What does it mean for a program to be correct?

Every function in this course has come with a type signature — and we
have been saying that the type IS the specification.  This week we make
that claim precise, and introduce the full design recipe.

A *specification* is a formal statement of what a function must do.
In Lean, specifications are *propositions* — types in `Prop`.
A *correct implementation* is a term that inhabits that proposition.

This is the central insight of certified programming: **a correct
program is a proof of its specification**.  The type checker verifies
both at once.

We also study the *verification ladder*: a sequence of increasingly
strong ways to check that a function behaves as intended.
@@@ -/

namespace Week07

/-! @@@
## 7.1  The design recipe

The design recipe structures every function definition in five steps.
We have used it informally throughout the course.  Here it is in full.

1. **Description** (docstring): what does the function do, in English?
2. **Signature**: the type of the function — input and output types.
3. **Specification**: a proposition stating what the function must do.
4. **Examples**: concrete inputs and expected outputs.
5. **Implementation**: the body of the definition.

The signature is a necessary condition; the specification is sufficient.
Lean enforces the signature automatically.  The specification requires
you to state and prove a theorem.
@@@ -/

-- A fully worked example: absolute difference of two natural numbers
-- (Note: Nat subtraction floors at 0, so |a - b| needs care)

-- 1. Description
/-- `absDiff a b` computes the absolute difference |a - b|. -/
-- 2. Signature:
def absDiff (a b : Nat) : Nat :=
-- 5. Implementation:
  if a ≥ b then a - b else b - a

-- 4. Examples:
#eval absDiff 7 3    -- 4
#eval absDiff 3 7    -- 4
#eval absDiff 5 5    -- 0

-- 3. Specification: absDiff is commutative and non-negative
-- (non-negative is guaranteed by Nat; commutativity is the real claim)
theorem absDiff_comm : ∀ a b : Nat, absDiff a b = absDiff b a := by
  intro a b; simp [absDiff]; omega

-- Verification: decide for concrete cases
#check (by decide : absDiff 7 3 = 4)
#check (by decide : absDiff 3 7 = 4)
#check (by decide : absDiff 5 5 = 0)

/-! @@@
## 7.2  The verification ladder

There are four rungs on the ladder, from weakest to strongest.

```
  #eval          dynamic spot-check (one example)
  rfl            exact computation (type-checks only if literally equal)
  decide         decision procedure (decidable propositions, any concrete values)
  theorem        kernel-verified proof (universally quantified claims)
```

Each rung is strictly stronger than the one below it.

- `#eval` is useful but proves nothing.
- `rfl` proves equality by reduction to the same normal form.
- `decide` proves any decidable proposition, but requires finite/concrete values.
- `theorem` is the ultimate: Lean's kernel verifies the proof term itself.
@@@ -/

-- Rung 1: #eval — dynamic spot check
#eval absDiff 7 3     -- 4  (we observe the output; nothing is proved)

-- Rung 2: rfl — exact computation
example : absDiff 7 3 = 4 := rfl     -- Lean reduces both sides to 4

-- Rung 3: decide — decision procedure
#check (by decide : absDiff 7 3 = 4)                     -- works
#check (by decide : absDiff 100 37 = absDiff 37 100)     -- works

-- Rung 4: theorem — universally quantified, kernel-verified
theorem absDiff_nonneg : ∀ a b : Nat, 0 ≤ absDiff a b := by
  intros; exact Nat.zero_le _

-- The ladder in one sentence: go as high as you need.
-- For this course: decide for decidable, theorem for universal.

/-! @@@
## 7.3  Specifications as propositions

A specification states the *relationship* between inputs and outputs.
It can involve:
- **Equality**: `f x = expected_value`
- **Inequality**: `f x > 0`
- **Conjunction**: `P (f x) ∧ Q (f x)` (multiple conditions at once)
- **Universal quantification**: `∀ x, f x = g x`
- **Implication**: `P x → Q (f x)` (conditional)
- **Negation**: `¬ (f x = y)` (something never happens)
@@@ -/

-- Equality specification
def triple (n : Nat) : Nat := n * 3
theorem triple_spec : ∀ n, triple n = n + n + n := by
  intro n; simp [triple]; ring

-- Inequality specification
def increment (n : Nat) : Nat := n + 1
theorem increment_gt : ∀ n, increment n > n := by
  intro n; simp [increment]

-- Conjunction: two independent conditions must hold simultaneously
def sorted2 (a b : Nat) : Nat × Nat :=
  if a ≤ b then (a, b) else (b, a)

theorem sorted2_spec : ∀ a b : Nat,
    let (lo, hi) := sorted2 a b
    lo ≤ hi ∧ (lo = a ∨ lo = b) := by
  intros a b; simp [sorted2]; omega

-- Decide for concrete cases of the conjunction spec
#check (by decide : let (lo, hi) := sorted2 7 3; lo ≤ hi ∧ (lo = 7 ∨ lo = 3))
#check (by decide : let (lo, hi) := sorted2 2 9; lo ≤ hi ∧ (lo = 2 ∨ lo = 9))

/-! @@@
## 7.4  Specifications for sorting: a worked case study

What does it mean to sort a list correctly?  This question has a
precise answer: a correct sort satisfies TWO independent conditions.

1. **Sorted**: the output list is in non-decreasing order.
2. **Permutation**: the output contains exactly the same elements as
   the input, with the same multiplicities.

Neither condition alone is sufficient:
- A function that always returns `[]` satisfies (1) but not (2).
- A function that appends an extra element satisfies (2) ... no,
  actually it fails (2) too, but consider reversing:
  `reverse [3, 1, 2]` gives `[2, 1, 3]` — it satisfies (2) but
  not (1).

Both conditions together define correct sorting.
@@@ -/

-- Lean's standard library provides the right tools
-- List.Sorted r xs: every adjacent pair in xs satisfies relation r
-- List.Perm xs ys: xs and ys are permutations of each other (same elements)

-- A correct sort specification: both conditions in conjunction
def CorrectSort (sort : List Nat → List Nat) : Prop :=
  ∀ xs : List Nat,
    List.Sorted (· ≤ ·) (sort xs) ∧ (sort xs).Perm xs

-- Insertion sort: a simple O(n²) sort
def insert (x : Nat) : List Nat → List Nat
  | []     => [x]
  | h :: t => if x ≤ h then x :: h :: t else h :: insert x t

def insertionSort : List Nat → List Nat
  | []     => []
  | h :: t => insert h (insertionSort t)

-- Examples
#eval insertionSort [3, 1, 4, 1, 5, 9, 2, 6]   -- [1, 1, 2, 3, 4, 5, 6, 9]
#eval insertionSort []                            -- []
#eval insertionSort [5, 4, 3, 2, 1]             -- [1, 2, 3, 4, 5]

-- Verify on concrete inputs with decide
#check (by decide : List.Sorted (· ≤ ·) (insertionSort [3, 1, 4, 1, 5]))
#check (by decide : (insertionSort [3, 1, 4, 1, 5]).Perm [3, 1, 4, 1, 5])

/-! @@@
The formal proof that `insertionSort` satisfies `CorrectSort` involves
proving a series of lemmas by induction.  This proof is the territory
of the follow-on course.  What matters for this course is:

1. You can *state* the specification precisely as a proposition.
2. You can *verify* it on concrete inputs with `decide`.
3. The type-checker enforces that the specification compiles.

The statement is the essential intellectual contribution.
@@@ -/

/-! @@@
## 7.5  Reading specifications

An equally important skill is reading a specification you did not write.
Given a type like

```lean
∀ xs ys : List Nat, myAppend xs ys = xs ++ ys
```

you should be able to answer: *what is this claim saying?*

"For any two lists of natural numbers, `myAppend xs ys` produces the
same result as Lean's built-in list append `++`."

This is a correctness claim: it says our implementation agrees with
the standard.
@@@ -/

-- Reading exercise: what does each specification say?

-- (a) What does this say?
-- ∀ n : Nat, double n > n
-- Answer: every number doubled is strictly greater than itself.
-- (True for n ≥ 1; false for n = 0 since 0 doubled is still 0)
-- Lesson: the specification may be false — you must choose carefully.

-- (b) What does this say?
-- ∀ xs : List Nat, myLength (myReverse xs) = myLength xs
-- Answer: reversing a list does not change its length.

-- (c) What does this say?
-- ∀ f : Nat → Nat, ∀ xs : List Nat, myLength (myMap f xs) = myLength xs
-- Answer: mapping any function over a list does not change its length.

-- Verifying (b) and (c) for concrete inputs
#check (by decide : (List.reverse [1, 2, 3]).length = [1, 2, 3].length)
#check (by decide : (List.map (· * 2) [1, 2, 3]).length = [1, 2, 3].length)

/-! @@@
## 7.6  The specification IS the documentation

In traditional programming, documentation lives in comments that can
go out of date.  In Lean, the specification is a theorem: if the code
changes, the proof fails, and the discrepancy is immediately detected.

Specifications as propositions serve multiple roles simultaneously:
- **Documentation**: tells you what the function does.
- **Testing**: verified on concrete inputs by `decide`.
- **Formal correctness proof**: verified universally by the Lean kernel.
- **Design guide**: writing the specification before the implementation
  clarifies what you are trying to build.

This is why we always write the specification before the implementation.
The design recipe forces this discipline.
@@@ -/

-- Complete design recipe example: minimum of a non-empty list

/-- `listMin xs hne` returns the minimum element of `xs`,
    given a proof `hne` that `xs` is non-empty. -/
def listMin : (xs : List Nat) → xs ≠ [] → Nat
  | [x],    _  => x
  | x :: y :: rest, _ =>
      Nat.min x (listMin (y :: rest) (List.cons_ne_nil y rest))

-- Specification: the result is ≤ every element
theorem listMin_spec (xs : List Nat) (h : xs ≠ []) :
    ∀ x, x ∈ xs → listMin xs h ≤ x := by
  induction xs with
  | nil => exact absurd rfl h
  | cons a t ih =>
    intro x hx
    simp [listMin]
    cases t with
    | nil =>
      simp at hx; rw [hx]
    | cons b rest =>
      simp [Nat.min_def]
      split
      · cases hx with
        | head => rfl
        | tail _ hxt =>
          calc a ≤ Nat.min a (listMin (b :: rest) _) := Nat.min_le_left _ _
            _ ≤ _ := by
                apply ih _ (List.cons_ne_nil b rest)
                exact hxt
      · push_neg at *
        cases hx with
        | head => linarith
        | tail _ hxt =>
          exact ih _ (List.cons_ne_nil b rest) x hxt

-- Verify on concrete inputs
#check (by decide : listMin [3, 1, 4, 1, 5] (by decide) = 1)
#check (by decide : listMin [7] (by decide) = 7)

/-! @@@
## Summary

- **A correct program is a proof of its specification.**
  Types enforce the signature; theorems enforce the behavior.
- **The design recipe**: description → signature → specification →
  examples → implementation.  Specification comes before code.
- **The verification ladder**:
  `#eval` < `rfl` < `decide` < `theorem`
- **Specifications as propositions** use equality, inequality,
  conjunction, implication, quantification, and negation.
- **Sorting correctness**: requires BOTH `List.Sorted` AND `List.Perm`.
  Neither condition alone is sufficient.
- **Reading specifications** is as important as writing them.
- **Specifications are executable documentation**: if the code breaks,
  the proof fails immediately.
@@@ -/

end Week07
