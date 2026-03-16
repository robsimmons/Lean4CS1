```lean
-- FPCourse/Unit1/Week03_RecursionTermination.lean
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
```

# Week 3: Recursion and Termination

## Structural recursion

Here is a way to think about recursion that is the *inverse* of the usual
story.

The usual story: "the function calls itself on a smaller input until it
reaches a base case."  That describes *execution*, but it does not explain
*why the definition gives a correct answer for every input*.

The better story starts from what you actually need in order to define a
function on the natural numbers:

1. **A base case.** You supply the answer for input `0` directly.
2. **A step function.** You supply a rule that, *given any input `n` and the
   answer for `n`*, produces the answer for `n + 1`.

Those two ingredients are enough to determine the answer for *every* natural
number: start with the answer for `0`, apply the step once to get the answer
for `1`, again to get the answer for `2`, and so on.  However large the input,
you can always reach it by iterating the step enough times from the base.

This is the content of the *principle of recursion* (or primitive recursion)
on the natural numbers.  The recursive definition in Lean is just a compact
way of writing down these two ingredients:

- The `| 0 => ...` clause supplies the base-case answer.
- The `| n + 1 => ...` clause supplies the step function.  The right-hand side
  may refer to `n` (the previous input) and to the recursive call `f n` (the
  answer for `n`).  That recursive call is not "calling itself" in some
  mysterious way — it is simply *using the assumption that the answer for `n`
  is already in hand*, which the step function is entitled to assume by
  construction.

Lean can verify termination automatically for structural recursion because
it can see that the step clause only ever asks for the answer at `n`, not at
any larger value.

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
-- rfl-based tests: both sides reduce to the same normal form
example : factorial 0 = 1   := rfl
example : factorial 5 = 120 := rfl
```

**Reading the definition.**  Apply the two-ingredient view to `factorial`:

- **Base case** (`| 0 => 1`): the answer for `0` is `1`.
- **Step** (`| n + 1 => (n + 1) * factorial n`): given input `n + 1`, and
  given that the answer for `n` is already `factorial n`, multiply them.

To see why this gives the right answer for `3`, iterate the step up from the base:

```
factorial 0 = 1                              -- base case
factorial 1 = 1 * factorial 0 = 1 * 1 = 1   -- step: n = 0, answer for 0 = 1
factorial 2 = 2 * factorial 1 = 2 * 1 = 2   -- step: n = 1, answer for 1 = 1
factorial 3 = 3 * factorial 2 = 3 * 2 = 6   -- step: n = 2, answer for 2 = 2
```

Each line uses the answer from the line above — exactly the "answer for `n`
already in hand" that the step clause is entitled to assume.

Lean's evaluator runs this in the opposite order — it unfolds `factorial 3`
toward the base case and assembles the result on the way back up.  Either
direction produces `6`.  The inductive framing explains *why* there is
a well-defined answer for every input, not just how to compute it.

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

-- Evaluation: factorialTR 3
--   ↝ factorialAcc 3 1
--   ↝ factorialAcc 2 (3 * 1)   ↝ factorialAcc 2 3
--   ↝ factorialAcc 1 (2 * 3)   ↝ factorialAcc 1 6
--   ↝ factorialAcc 0 (1 * 6)   ↝ factorialAcc 0 6
--   ↝ 6                          (first clause: acc is returned)
-- Notice: the accumulator grows on the way DOWN; no work on the way back up.
#eval factorialTR 5   -- 120
example : factorialTR 5 = 120 := rfl
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
-- Note: rfl-based tests do NOT work for gcd.
-- gcd uses well-founded (non-structural) recursion; the kernel cannot reduce it.
-- Neither rfl nor decide can close goals about gcd on concrete values.
-- #eval works because it uses the compiled code path, not the kernel.
-- This distinction matters: rfl-based tests are available only for
-- structurally recursive functions (like factorial above).

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
-- You should be able to read and understand the proposition.
-- The proof term is here for your curiosity; you are not expected to produce it.
theorem factorial_pos : ∀ n : Nat, 0 < factorial n :=
  fun n => Nat.recOn n (Nat.lt.base 0) (fun n ih => Nat.mul_pos (Nat.succ_pos n) ih)

-- "factorial is monotone: each value is no greater than the next"
-- You should be able to read and understand the proposition.
-- The proof term is here for your curiosity; you are not expected to produce it.
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
