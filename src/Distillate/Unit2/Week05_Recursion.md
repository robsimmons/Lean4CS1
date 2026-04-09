```lean
-- Distillate/Unit2/Week05_Recursion.lean
import Mathlib.Data.List.Basic
import Mathlib.Logic.Basic
```

# Week 5: Recursion and Inductive Types

## When the answer depends on a smaller answer

So far every function we have written terminates trivially: one step,
and you are done.  Most interesting computations are not like this.
Computing the sum of a list requires visiting every element.
Computing a factorial requires multiplying down to 1.

The way to express "repeat this until done" in functional programming
is *recursion*: a function calls itself on a smaller input.
The key guarantee Lean requires is that the input gets *strictly
smaller* at each call — so the process always ends.

This is called *structural recursion*: recursion that follows the
structure of an inductive data type.  The base case handles the
smallest possible value; the recursive case handles the constructor
that builds larger values from smaller ones.

```lean
namespace Week05
```

## 5.1  Natural number recursion

`Nat` is an inductive type:
```
inductive Nat : Type
  | zero : Nat
  | succ : Nat → Nat   -- succ n is the successor of n, i.e., n + 1
```

Every natural number is either `zero` or `succ n` for some smaller `n`.
A function defined by pattern matching on `Nat` has exactly two cases.

**The slogan**: *a base case and a step, applied repeatedly, yields an
answer for any input.*  This is both the definition of recursion and
the content of the principle of mathematical induction.

```lean
-- Factorial: n! = n × (n-1) × ... × 1
def factorial : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * factorial n

-- The recursive structure mirrors the inductive structure of Nat:
--   factorial 0 = 1                  (base case)
--   factorial (n+1) = (n+1) * factorial n  (step)

#eval factorial 0    -- 1
#eval factorial 5    -- 120
#eval factorial 10   -- 3628800

-- Fibonacci numbers
def fib : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fib n + fib (n + 1)

#eval fib 0    -- 0
#eval fib 7    -- 13
#eval fib 10   -- 55

-- Exponentiation
def pow (base : Nat) : Nat → Nat
  | 0     => 1
  | n + 1 => base * pow base n

#eval pow 2 10   -- 1024
```

**Termination.**  Lean checks that every recursive call uses a strictly
smaller argument.  `factorial n` calls `factorial (n-1)` — that is,
`factorial n` in the pattern `n + 1` calls `factorial n`, which IS
smaller.  Lean accepts this automatically.

If your recursion does not obviously decrease, Lean will reject the
definition.  This guarantee means every function you define in Lean
always terminates.  There are no infinite loops.

## 5.1a  The logical reading: recursion IS induction

Every recursive definition has a logical twin.

**Computational reading.**  To define a function on `Nat`, supply a base
case (what to return for `0`) and a step (how to compute the answer for
`n + 1` from the answer for `n`).

**Logical reading.**  To prove a proposition for EVERY `Nat`, supply a
base case (prove it for `0`) and a step (assuming it holds for `n`,
prove it for `n + 1`).

These are the same structure:

| Computation | Logic |
|-------------|-------|
| `def f : Nat → α` | `theorem p : ∀ n : Nat, P n` |
| Base case: `f 0 = ...` | Base case: proof of `P 0` |
| Step: `f (n+1)` uses `f n` | Step: proof of `P n → P (n+1)` |
| Structural recursion | Mathematical induction |

You do not need to write induction proofs.  But recognize the pattern:
every time you write a recursive function with a base case and a step,
you are writing the same structure a mathematician uses to prove
"for all n, ...".  This is Curry-Howard at work.

```lean
-- Computational reading: factorial computes n!
-- Logical reading: this same structure could prove "for all n, P n"
--   base case: P 0 holds              ↔  factorial 0 = 1
--   step: P n implies P (n+1)         ↔  factorial (n+1) = (n+1) * factorial n
```

## 5.2  Lists: the canonical recursive inductive type

A list of natural numbers is either empty or a head element prepended
to a smaller list:

```
inductive List (α : Type) : Type
  | nil  : List α             -- the empty list, written []
  | cons : α → List α → List α  -- h :: t
```

Every list is either `[]` or `h :: t` for some head `h` and tail `t`.
Functions on lists pattern-match on these two cases.

The same duality applies to lists:

| Computation on lists | Logic about lists |
|---------------------|-------------------|
| Base case: `f [] = ...` | Prove `P []` |
| Step: `f (h :: t)` uses `f t` | From `P t`, prove `P (h :: t)` |
| Structural recursion on `List` | Induction on `List` |

The `decide`-verified specifications in §5.5 are the logical reading
made concrete: each `#check (by decide : ...)` is Lean confirming that
a proposition about the function is true.

```lean
-- Length: count the elements
def myLength : List Nat → Nat
  | []      => 0
  | _ :: t  => 1 + myLength t

#eval myLength []           -- 0
#eval myLength [1, 2, 3]    -- 3
#eval myLength [10, 20]     -- 2

-- Sum: add all elements
def mySum : List Nat → Nat
  | []      => 0
  | h :: t  => h + mySum t

#eval mySum []           -- 0
#eval mySum [1, 2, 3]    -- 6
#eval mySum [10, 20, 30] -- 60

-- Append: join two lists
def myAppend : List Nat → List Nat → List Nat
  | [],     ys => ys
  | x :: xs, ys => x :: myAppend xs ys

#eval myAppend [1, 2] [3, 4]    -- [1, 2, 3, 4]
#eval myAppend [] [1, 2]        -- [1, 2]
#eval myAppend [1, 2] []        -- [1, 2]

-- Reverse
def myReverse : List Nat → List Nat
  | []     => []
  | h :: t => myReverse t ++ [h]

#eval myReverse [1, 2, 3, 4]   -- [4, 3, 2, 1]
```

## 5.3  Member test and search

A fundamental operation on lists is testing whether an element appears.
This is a function from a value and a list to a Bool.

```lean
def myMember (x : Nat) : List Nat → Bool
  | []     => false
  | h :: t => if h == x then true else myMember x t

#eval myMember 3 [1, 2, 3, 4]   -- true
#eval myMember 5 [1, 2, 3, 4]   -- false
#eval myMember 1 []              -- false

-- The proposition version: ∈ for lists
-- x ∈ xs : Prop says "x appears in xs"
#check (3 ∈ [1, 2, 3, 4])     -- 3 ∈ [1, 2, 3, 4] : Prop
#check (by decide : 3 ∈ [1, 2, 3, 4])
```

## 5.4  Recursion on multiple arguments

Some functions need to recurse on more than one argument simultaneously,
or choose which argument to decrease.  A common pattern is recursion on
the first list argument.

```lean
-- Zip: pair up elements from two lists
def myZip : List Nat → List Nat → List (Nat × Nat)
  | [],     _      => []
  | _,      []     => []
  | x :: xs, y :: ys => (x, y) :: myZip xs ys

#eval myZip [1, 2, 3] [10, 20, 30]   -- [(1, 10), (2, 20), (3, 30)]
#eval myZip [1, 2] [10, 20, 30]      -- [(1, 10), (2, 20)]  (shorter list wins)

-- Take: return the first n elements
def myTake : Nat → List Nat → List Nat
  | 0,     _      => []
  | _,     []     => []
  | n + 1, h :: t => h :: myTake n t

#eval myTake 3 [1, 2, 3, 4, 5]   -- [1, 2, 3]
#eval myTake 10 [1, 2, 3]         -- [1, 2, 3]  (fewer than 10 elements)
```

## 5.5  Specifications for recursive functions

Recursive functions can be given precise specifications using
propositions.  `decide` can verify these for concrete inputs.

For universally quantified statements about lists, we need either:
- `decide` (works when the proposition is over a decidable, finite domain)
- `simp` with library lemmas (for general proofs about list operations)

```lean
-- Concrete specifications verified by decide
#check (by decide : myLength [1, 2, 3] = 3)
#check (by decide : mySum [1, 2, 3] = 6)
#check (by decide : myAppend [1, 2] [3, 4] = [1, 2, 3, 4])
#check (by decide : myReverse [1, 2, 3] = [3, 2, 1])

-- Properties that hold universally (need simp/omega for general proofs)
-- e.g., length of append = sum of lengths
theorem myLength_append (xs ys : List Nat) :
    myLength (myAppend xs ys) = myLength xs + myLength ys := by
  induction xs with
  | nil       => simp [myLength, myAppend]
  | cons h t ih => simp [myLength, myAppend, ih]; omega

-- Reverse is its own inverse
theorem myReverse_reverse (xs : List Nat) :
    myReverse (myReverse xs) = xs := by
  induction xs with
  | nil       => simp [myReverse]
  | cons h t ih => simp [myReverse]; sorry  -- full proof requires auxiliary lemmas
```

Notice: the above proofs use `induction` in tactic mode.  This is one
case where `decide` cannot help (the universally quantified statement
ranges over all lists, which is infinite).  In this course we use
`decide` for decidable propositions and accept standard Lean automation
(`simp`, `omega`, `ring`) for general theorems.  The goal is always to
focus on the *specification* — what the theorem says — not on proof
construction.

## 5.6  Totality: every function terminates

Lean accepts only *total* functions — functions that return an answer
for every possible input.  The termination checker ensures this by
verifying that each recursive call uses a structurally smaller argument.

This is a guarantee, not a limitation.  It means:
- No infinite loops.
- No crashes from missing cases.
- The type system can trust that `f x` always has a value.
- Specifications about `f` can use equational reasoning freely.

If you need to express a computation that might not terminate (e.g.,
search over an infinite space), you use `Option` to represent possible
failure — or you prove that it always terminates in the relevant cases.

```lean
-- Lean rejects non-terminating definitions
-- def loop : Nat → Nat
--   | n => loop n   -- ERROR: failed to prove termination
-- This is a feature, not a bug.
```

## Summary

- **Structural recursion**: a function calls itself on a strictly
  smaller argument, mirroring the inductive structure of the input type.
- **`Nat` recursion**: base case (`zero`) and step (`succ n → ...`).
  *A base case and a step yield an answer for any input.*
- **`List` recursion**: base case (`[]`) and step (`h :: t → ...`).
- Common list functions: `length`, `sum`, `append`, `reverse`, `zip`.
- **Termination**: Lean checks that every recursive call decreases the
  input.  All defined functions are guaranteed to terminate.
- **Specifications** for recursive functions: `decide` for concrete
  instances; `simp`/`omega`/`ring` for universal statements.
- **The dual reading**: recursive definitions on inductive types
  have the same structure as proofs by induction.  Base case and step
  in computation = base case and step in logic.  This is Curry-Howard
  applied to recursion.

```lean
end Week05
```
