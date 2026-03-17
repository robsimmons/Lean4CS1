-- Distillate/Unit3/Week08_CurryHoward.lean
import Mathlib.Logic.Basic
import Mathlib.Data.List.Basic

/-! @@@
# Week 8: The Curry-Howard Correspondence

## You have been doing logic all along

This is the week we name what you have been doing since Week 0.

Every type you have written in this course has two readings:
computational and logical.  Every function you have written is both
a program and a proof.  These are not analogies.  They are identities.

The *Curry-Howard correspondence* (also called *propositions as types*
or *proofs as programs*) states that:

> **Types are propositions.  Terms are proofs.**

This is not a philosophy.  It is a mathematical theorem about the
structure of type theory.  Lean's type system is designed to make this
identity literal: the same `def` keyword that defines a program also
proves a theorem.  There is no separate "proof mode" at the level of
the type theory.

This week we:
1. Exhibit the full correspondence table.
2. Revisit every type constructor you have learned, now seeing both
   sides at once.
3. Explore what it means for a program to *be* a proof of its spec.
4. Describe the automation boundary — where `decide` works and why.
5. Preview what the sequel course does with the other side.
@@@ -/

namespace Week08

/-! @@@
## 8.1  The correspondence table

| Type constructor | Computational reading | Logical reading |
|---|---|---|
| Basic type `α` | An atomic data type | An atomic proposition |
| `α → β` | Function from α to β | α implies β |
| `α × β` | Pair: α AND β | Conjunction: P ∧ Q |
| `α ⊕ β` | Choice: α OR β | Disjunction: P ∨ Q |
| `Empty` | Uninhabitable type | Falsity: False |
| `α → Empty` (≡ `¬α`) | α is uninhabitable | Negation: ¬P |
| `Unit` | Type with one element | Truth: True |
| `(a : α) × P a` | Dependent pair | Existential: ∃ x, P x |
| `(a : α) → P a` | Dependent function | Universal: ∀ x, P x |

This table is not a list of analogies.  Each row is an identity:
the computational reading and the logical reading describe the *same*
type, read two ways.
@@@ -/

/-! @@@
## 8.2  Inhabited types are true propositions

A type is *inhabited* when at least one term of that type exists.
A proposition is *true* when at least one proof of it exists.

These are the same definition.

Under the correspondence:
- `Nat` is inhabited (by `0`, `1`, `2`, …): it is "trivially true"
  as a proposition (or rather, it is too general to be interesting as a
  proposition — the interesting propositions are the constrained ones).
- `1 + 1 = 2` is inhabited (by `rfl`): this proposition is true.
- `1 + 1 = 3` is uninhabited: this proposition is false.
- `Empty`/`False` is uninhabited: there is no proof of False.
- `¬P` is inhabited when P is uninhabited: ¬P is true when P is false.
@@@ -/

-- Demonstrating inhabitation = truth
#check (rfl : 1 + 1 = 2)              -- rfl inhabits this type = proves this prop
#check (True.intro : True)             -- True.intro inhabits True
-- there is no term of type (1 + 1 = 3) — it is false

-- ¬P = P → False: proving something false
-- If 1 = 2 were provable, we could produce a False:
theorem one_ne_two : ¬ (1 = 2) := by decide
-- This is a function: given a proof of (1=2), produce False.
-- Since no proof of (1=2) exists, this function is vacuously valid.

/-! @@@
## 8.3  Every function is a proof

In Lean, there is no distinction between a function definition and a
theorem proof.  Both are terms.  Both inhabit a type.  The only
difference is whether we choose to read the type computationally or
logically.
@@@ -/

-- double as a FUNCTION
def double (n : Nat) : Nat := n * 2

-- double's specification as a THEOREM
-- This is also a function: given n, produce a proof that double n = n + n
theorem double_spec : ∀ n : Nat, double n = n + n := by
  intro n; simp [double]; ring

-- A function that DIRECTLY returns a proof (proof-carrying computation)
def doubleWithProof (n : Nat) : { m : Nat // m = n + n } :=
  ⟨n * 2, by ring⟩

-- The proof component is always available alongside the value
example : (doubleWithProof 5).val = 10 := rfl
-- (doubleWithProof 5).property : 10 = 5 + 5   ← this is the proof

/-! @@@
## 8.4  The six constructors, both sides at once

Let us revisit each of the six type constructors introduced in Week 0,
now reading each one from both sides simultaneously.
@@@ -/

-- (1) BASIC TYPE: Nat (data) vs. propositional atoms (logic)
-- As data: values like 0, 1, 42
-- As propositions: claims like (1 + 1 = 2), (x < y)
example : Nat := 42                    -- computational
example : 1 + 1 = 2 := rfl            -- logical

-- (2) FUNCTION TYPE: α → β
-- As data: a function that computes
-- As proof: an implication — given proof of α, produce proof of β
def succ_positive : ∀ n : Nat, n + 1 > 0 := fun n => Nat.succ_pos n
-- This is simultaneously: a function Nat → (n + 1 > 0)
--                    and: a proof of ∀ n, n + 1 > 0

-- (3) PRODUCT TYPE: α × β
-- As data: holds an α AND a β simultaneously
-- As proof: conjunction — holds proof of P AND proof of Q
example : Nat × Bool := (42, true)                     -- data
example : 2 > 1 ∧ 3 > 2 := ⟨by decide, by decide⟩    -- proof

-- (4) SUM TYPE: α ⊕ β
-- As data: holds EITHER an α OR a β
-- As proof: disjunction — holds proof of P OR proof of Q
example : Bool ⊕ Nat := Sum.inl true                     -- data
example : 1 = 1 ∨ 1 = 2 := Or.inl rfl                   -- proof

-- (5) EMPTY TYPE: Empty / False
-- As data: no inhabitants — an impossible value
-- As proof: no proofs — a false proposition
-- (We cannot construct these, only prove things from them vacuously)
theorem vacuous (h : False) : 0 = 1 := False.elim h

-- (6) FUNCTION TO EMPTY: α → Empty / ¬P
-- As data: a function that produces an impossible value (only if α is also empty)
-- As proof: negation — establishes that P has no proof
example : ¬ (1 = 2) := by decide                -- logical
-- same as: (1 = 2) → False

/-! @@@
## 8.5  Decidability: the automation boundary

`decide` works when a proposition is *decidable*: there exists an
algorithm that always terminates and answers "provable" or "not provable."

For decidable propositions, `decide` runs the algorithm and packages
the result as a proof term.  The Lean kernel then checks the proof term
(not the algorithm — just the witness) for correctness.

**When does `decide` work?**
- Equality of basic types with computable equality: `Nat`, `Bool`, `String`
- Bounded arithmetic: `2 + 3 = 5`, `7 < 10`
- Boolean predicates applied to finite values
- Finite universal quantification: `∀ b : Bool, ...`
- Propositional logic connectives (∧, ∨, ¬) of decidable propositions

**When does `decide` NOT work?**
- Universally quantified claims over infinite types: `∀ n : Nat, P n`
  (unless P is bounded or the quantifier is over a finite enumeration)
- Properties of functions in general: `∀ f : Nat → Nat, ...`
- Floating-point equality: `Float` does not have `DecidableEq`
  because `NaN ≠ NaN` violates the reflexivity requirement
@@@ -/

-- decide works here:
#check (by decide : 2 + 3 = 5)
#check (by decide : ∀ b : Bool, b || true = true)        -- Bool is finite
#check (by decide : ∀ n : Fin 10, n.val < 10)            -- Fin 10 is finite

-- decide does NOT work here (uncomment to see the error):
-- #check (by decide : ∀ n : Nat, n + 0 = n)  -- Nat is infinite

-- For infinite types, use theorem + standard tactics:
theorem add_zero_all : ∀ n : Nat, n + 0 = n := Nat.add_zero

/-! @@@
## 8.6  Programs are proofs of their specifications

We close the loop on the central claim.

A function definition in Lean:
```lean
def f (x : α) : β := body
```
is the same thing as a proof:
```lean
theorem f : ∀ x : α, β := fun x => body
```

When `β` is a proposition (a type in `Prop`), the definition IS a proof.
When `β` is a data type (a type in `Type`), the definition IS a program.

When `β` bundles data with a proof — a dependent type — the function
is BOTH a program AND a proof simultaneously.

This is the unification of specification and implementation.  When you
write a function that returns `{ m : Nat // m = n * 2 }`, you are not
writing a program *and separately* a proof.  You are writing one thing
that is both.
@@@ -/

-- A function that IS its own correctness proof
-- Return type bundles the value with a proof of the specification
def safeDivide (n d : Nat) (hd : d ≠ 0) :
    { q : Nat // n = q * d + n % d ∧ n % d < d } :=
  ⟨n / d, by constructor <;> omega⟩

-- The definition:
--   - Computes the quotient (n / d)
--   - Simultaneously proves it satisfies the division algorithm
-- No separate proof needed.  The type IS the specification.

#eval (safeDivide 17 5 (by decide)).val     -- 3
-- (safeDivide 17 5 _).property : 17 = 3 * 5 + 2 ∧ 2 < 5  (always available)

/-! @@@
## 8.7  Existential types: dependent pairs

One entry in the correspondence table we have not yet examined closely
is the existential quantifier.

`∃ x : α, P x` (read "there exists an `x` of type `α` such that `P x`")
is the *dependent pair* type: a pair `⟨witness, proof⟩` where the
second component is a proof that the first component satisfies `P`.

This is precisely the *subtype* `{ x : α // P x }` introduced in Week 2.

Under Curry-Howard:
- `{ x : α // P x }` is the existential `∃ x : α, P x`
- The *witness* is the data value
- The *proof* is the certificate of correctness
@@@ -/

-- Existential: "there exists an even number greater than 4"
theorem exists_even_gt_4 : ∃ n : Nat, n % 2 = 0 ∧ n > 4 :=
  ⟨6, by decide⟩   -- 6 is the witness; decide proves 6 % 2 = 0 ∧ 6 > 4

-- Subtype form (computation-oriented)
def evenGt4 : { n : Nat // n % 2 = 0 ∧ n > 4 } :=
  ⟨6, by decide⟩

-- These are the same thing, one read computationally, one logically.

/-! @@@
## 8.8  The two-course arc

This course has been the computational half of a pair.

| This course (CS1) | Sequel (CS2: Certified Proofs) |
|---|---|
| Types as data | Types as propositions |
| Functions as programs | Functions as proofs |
| `decide` produces proof objects | Tactic proofs build proof objects |
| Specifications stated, auto-verified | Specifications proved by hand |
| `Type` | `Prop` |

In CS2, every concept from this course appears again — but the emphasis
shifts from *computing values* to *constructing proofs* of the
universally-quantified theorems that `decide` cannot touch.

The architecture of CS2 is already laid down in your understanding of
this course.  You know all six type constructors.  You know what a
proof term looks like.  You know what a specification says.  CS2 takes
the same tools and drives them one level deeper: from automation to
construction.

**The central fact of this course, stated plainly:**
Every correct program in Lean is a proof that it satisfies its
specification.  Specification and implementation are one artifact,
certified by the type checker.
@@@ -/

/-! @@@
## Summary: the full correspondence

| Lean construct | Computational reading | Logical reading |
|---|---|---|
| `T : Type` | A data type | A proposition |
| `t : T` | A value of type T | A proof of proposition T |
| `α → β` | Function type | Implication |
| `fun x => body` | Lambda (anonymous function) | Proof of implication |
| `α × β` | Pair type | Conjunction (∧) |
| `⟨a, b⟩ : α × β` | A pair | Proof of conjunction |
| `.1`, `.2` | Projections | Elimination of conjunction |
| `α ⊕ β` | Sum type | Disjunction (∨) |
| `Sum.inl a` | Left injection | Left disjunct |
| `Sum.inr b` | Right injection | Right disjunct |
| `Empty` | Uninhabitable type | False (⊥) |
| `Empty.rec` | Vacuous function | Ex falso (False.elim) |
| `α → Empty` (= `¬α`) | α is empty | Negation (¬P) |
| `Unit` | Singleton type | True (⊤) |
| `(x : α) → P x` | Dependent function | Universal (∀) |
| `{ x : α // P x }` | Subtype | Existential (∃) |
| `⟨witness, proof⟩` | A value + certificate | Existential proof |
| `decide` | Runs decision procedure | Produces proof automatically |

You have worked with every row in this table.
The Curry-Howard correspondence is not a theorem about this course.
It is what this course has been all along.
@@@ -/

end Week08
