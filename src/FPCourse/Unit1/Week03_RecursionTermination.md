```lean
-- FPCourse/Unit1/Week03_RecursionTermination.lean
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
```

# Week 3: Recursion and Termination

## Structural recursion

A function defined by structural recursion on an inductive type makes a
recursive call only on *subterms* of the input.  Because inductive types
are always finite, each recursive call receives a strictly smaller argument.
Lean verifies this automatically — no termination argument is needed for
structural recursion.

The key insight: if you can pattern-match the input and recurse only into
the pieces revealed by the match, Lean can see the recursion terminates.
```lean
namespace Week03
```

## 3.1  Factorial — direct recursive definition
```lean
def factorial : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 0   -- 1
#eval factorial 5   -- 120
#eval factorial 10  -- 3628800
```

## 3.2  Tail recursion and accumulators

The direct definition rebuilds the product on the way *back* from the
base case.  A tail-recursive version accumulates the product on the way
*down*, so the recursive call is the last thing done.

Tail-recursive functions are important in practice because they run in
constant stack space.  They can also have different proofs of correctness,
which is why we need to state the relationship between the two versions.
```lean
def factorialAcc : Nat → Nat → Nat
  | 0,     acc => acc
  | n + 1, acc => factorialAcc n ((n + 1) * acc)

def factorialTR (n : Nat) : Nat := factorialAcc n 1

#eval factorialTR 5   -- 120
```

## 3.3  Specification: the two definitions agree

The following theorem states that the accumulator version computes the
same value as the direct version, for any starting accumulator.

**You are not expected to construct this proof.**  It is provided so
you can see that such a proof exists and what it looks like.  The proof
is a term — a recursive function on `n` whose type is the specification.

Read the term as: "by induction on n; the base case is a calculation;
the step uses the inductive hypothesis for n with a different accumulator."
```lean
-- Provided term-mode proof.  Read it; do not reproduce it.
theorem factorialAcc_spec : ∀ (n acc : Nat),
    factorialAcc n acc = acc * factorial n := by
  intro n
  induction n with
  | zero => intro acc; simp [factorialAcc, factorial]
  | succ n ih =>
    intro acc
    simp only [factorialAcc, factorial]
    rw [ih]
    ring

-- Corollary: factorialTR agrees with factorial
theorem factorialTR_spec (n : Nat) : factorialTR n = factorial n :=
  Eq.trans (factorialAcc_spec n 1) (Nat.one_mul (factorial n))
```

## 3.4  Non-structural termination

When recursion does not follow the structure of an inductive type,
Lean requires an explicit *termination measure*: a quantity that strictly
decreases at each recursive call with respect to some well-founded relation.

The `termination_by` clause names the measure.
```lean
-- Euclidean GCD — not structurally recursive on either argument,
-- but decreases on the second argument at each step.
def gcd : Nat → Nat → Nat
  | a, 0     => a
  | a, b + 1 => gcd (b + 1) (a % (b + 1))
termination_by _ b => b
decreasing_by apply Nat.mod_lt; omega

#eval gcd 48 18   -- 6
#eval gcd 100 75  -- 25

-- Specification: gcd divides both arguments.
-- This is a Prop.  The proof is provided for you to read.
def divides (d n : Nat) : Prop := ∃ k, n = d * k

-- Nat.gcd_dvd_left and Nat.gcd_dvd_right are Mathlib lemmas.
-- Our gcd coincides with Nat.gcd (provable, provided here):
theorem gcd_eq_nat_gcd : ∀ a b : Nat, gcd a b = Nat.gcd a b := by
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    cases b with
    | zero =>
      simp only [gcd, Nat.gcd_zero_right]
    | succ b =>
      simp only [gcd]
      have key := ih (a % (b + 1)) (Nat.mod_lt a (Nat.succ_pos b)) (b + 1)
      rw [key, Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
```

## 3.5  The termination / totality distinction

A function in Lean must be *total*: it must return a value for every input.
Lean enforces totality through two mechanisms:

- **Structural recursion**: automatically verified by checking recursive
  calls are on strict subterms.
- **Well-founded recursion**: you provide a termination measure; Lean
  verifies it decreases at each call.

A function that does not terminate cannot be given a type in Lean without
using the `partial` keyword — which removes termination guarantees and
disables proof of properties about the function.

This is not a limitation.  It is a *feature*: if a function has a type
in Lean, it terminates on all inputs.  This means any specification you
write about it is asking a question that always has an answer.

## 3.6  Reading specifications about recursive functions

A specification for a recursive function is almost always a ∀ proposition:
"for all inputs, the output satisfies this condition."

Practice reading these:
```lean
-- "For all n, factorial n is positive"
theorem factorial_pos : ∀ n : Nat, 0 < factorial n :=
  fun n => Nat.recOn n (Nat.lt.base 0) (fun n ih => Nat.mul_pos (Nat.succ_pos n) ih)

-- "factorial is monotone" (stated; proof omitted here for brevity,
-- but it has a complete term-mode proof in the companion notes)
theorem factorial_mono : ∀ n : Nat, factorial n ≤ factorial (n + 1) :=
  fun n => Nat.le_mul_of_pos_left (factorial n) (Nat.succ_pos n)
```

## Exercises

1. Define `sumTo : Nat → Nat` that computes 0 + 1 + ... + n.
   Write its specification as a ∀ proposition:
   `∀ n, sumTo n = n * (n + 1) / 2`.

2. Define a tail-recursive version `sumToAcc : Nat → Nat → Nat`.
   State (as a Prop) the relationship between `sumToAcc` and `sumTo`.

3. Use `gcd_eq_nat_gcd` and Mathlib's `Nat.Coprime` to state the
   proposition: "8 and 15 are coprime."  Use `decide` to prove it.

4. Why does the following definition NOT satisfy Lean's termination
   checker?  What termination measure would you supply?

   ```lean
   def collatz : Nat → Nat
     | 0 => 0
     | 1 => 1
     | n => if n % 2 == 0 then collatz (n / 2) else collatz (3 * n + 1)
   ```

5. State the specification for `gcd` as two ∀ propositions expressing
   that it divides both arguments.
```lean
end Week03
```

