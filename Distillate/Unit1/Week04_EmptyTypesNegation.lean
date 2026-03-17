-- Distillate/Unit1/Week04_EmptyTypesNegation.lean
import Mathlib.Logic.Basic

/-! @@@
# Week 4: Empty Types and Negation

## The type with no inhabitants

The fifth constructor in our table is `Empty`.

**Computational reading.**  `Empty` is a type with no constructors —
no values, no terms, no inhabitants whatsoever.  You can declare
`Empty` as a type, but you can never produce a value of type `Empty`.
It is the void: not a single thing lives there.

**Logical reading.**  `False` is the proposition with no proofs.
A claim that is false has no witnesses.  `False` in Lean is structurally
identical to `Empty` — an inductive type with zero constructors.

Why does this matter?  Because *if you somehow had a proof of `False`,
you could prove anything* — by pattern-matching on it with zero cases.
Impossibility is explosive.

The sixth constructor follows directly: `α → Empty` is the type of
functions that, given an inhabitant of `α`, produce an inhabitant of
`Empty`.  Since `Empty` has no inhabitants, such a function could only
exist if `α` also had no inhabitants.  This is negation.
@@@ -/

namespace Week04

/-! @@@
## 4.1  The Empty type

`Empty` is defined with no constructors:

```lean
inductive Empty : Type
-- (no constructors)
```

There is no way to produce a value of type `Empty`.
But there IS a function `Empty.rec` with a remarkable type:
@@@ -/

-- Empty.rec : ∀ {α : Sort u}, Empty → α
-- Given an Empty, produce ANYTHING.
-- This is not magic — it is vacuously valid: you can never call it.
#check @Empty.rec

-- If you have an Empty, you can produce any type — vacuously
-- (This function exists but can never be called with a real argument)
def impossibleToNat : Empty → Nat := Empty.rec

-- The same pattern holds for False in Prop
-- False.elim : ∀ {α : Sort u}, False → α
-- If you have a proof of False, you can prove anything.
#check @False.elim

theorem from_false (h : False) : 1 = 2 :=
  False.elim h   -- vacuously true: h cannot exist

/-! @@@
**Why is this useful?**  You will never call `Empty.rec` or `False.elim`
with a genuine argument — because no genuine argument can exist.
Their value is precisely in *case analysis*: when you match on a value
of an inductive type and one constructor is `Empty` (impossible), Lean
knows that branch is unreachable, and closes it automatically.
@@@ -/

/-! @@@
## 4.2  Negation: functions to Empty

The sixth constructor is `α → Empty`.

In logic, the *negation* of a proposition `P` is written `¬P` (read
"not P").  In Lean, `¬P` is *definitionally equal to* `P → False`.

```
¬P   :=   P → False
```

A proof of `¬P` is a function: given any hypothetical proof of `P`,
produce a proof of `False`.  Since `False` has no proof, such a
function can only exist when `P` is itself unprovable — i.e., when
`P` is false.

This is the correct, constructive account of negation.
@@@ -/

-- ¬P is definitionally P → False
#check @Not   -- Not : Prop → Prop

-- Proving ¬(1 = 2): provide a function from (1 = 2) to False
-- decide handles this for us
#check (by decide : ¬ (1 = 2))

-- Manually: if 1 = 2 were true, we could derive a contradiction
-- (Lean's discriminate/decide handle this behind the scenes)
theorem one_ne_two : ¬ (1 = 2) := by decide

-- Negation of Bool propositions
#check (by decide : ¬ (true = false))
#check (by decide : ¬ (1 + 1 = 3))

/-! @@@
## 4.3  The explosion principle (ex falso quodlibet)

"From false, anything follows."

If you have a proof `h : False`, you can close any goal.
`False.elim h` takes the proof of False and produces a proof of
whatever type you need.

In a program, this corresponds to matching on `Empty` with zero cases:
the match exhausts all constructors (there are none), so it trivially
covers every case.  The resulting function is total — it just never runs.
@@@ -/

-- Pattern matching on Empty: zero cases needed, so it type-checks
-- (This function is total even though it seems to have no body)
def absurdFun (e : Empty) : Nat :=
  match e with   -- no cases needed: Empty has no constructors

-- The same for False in Prop
theorem exFalso (h : False) : 2 + 2 = 5 :=
  match h with   -- no cases needed

/-! @@@
This is not a trick.  It is a theorem-prover's version of the
classical principle: a false hypothesis makes any implication vacuously
valid.  In formal logic, `False → P` holds for ALL `P`.
@@@ -/

/-! @@@
## 4.4  Negation in practice: contradictions and `absurd`

A common proof pattern is to derive a contradiction: you have `h₁ : P`
and `h₂ : ¬P`, which together let you conclude anything.

Lean provides `absurd : ∀ {a : Prop} {b : Prop}, a → ¬a → b` for exactly
this pattern.
@@@ -/

-- absurd: given a proof of P and a proof of ¬P, conclude anything
theorem contradiction_example (h : 1 = 2) : 0 = 1 :=
  absurd h (by decide)   -- h claims 1=2, decide proves ¬(1=2); absurd closes goal

-- decide finds the negation automatically
#check (by decide : ¬ (2 + 3 = 7))
#check (by decide : ¬ (true && false = true))

/-! @@@
## 4.5  Impossible branches in pattern matching

One of the most elegant uses of Empty/False in Lean is *ruling out
impossible cases*.  When you define a function by pattern matching,
Lean sometimes allows you to assert that a constructor cannot appear.

If a constructor can only be inhabited by providing a proof of
a false proposition, then that branch is unreachable, and Lean accepts
a match expression with that branch omitted (or filled with `nomatch`).
@@@ -/

-- An indexed type where some constructors are provably impossible
-- (A taste of dependent types — more in future courses)

-- Example: the Fin type enforces bounds
-- Fin n is the type of natural numbers strictly less than n
-- Fin 0 has no inhabitants — there is no Nat that is < 0
#check (Fin 3)    -- type of {0, 1, 2}
#check (⟨0, by decide⟩ : Fin 3)    -- 0 < 3, so 0 : Fin 3
#check (⟨2, by decide⟩ : Fin 3)    -- 2 < 3, so 2 : Fin 3

-- Fin 0 is empty: no proof of (n < 0) exists for any n
-- def absurdFin0 : Fin 0 → Nat := fun ⟨_, h⟩ => absurd h (Nat.not_lt_zero _)

/-! @@@
## 4.6  Empty types in specifications

Functions to empty types matter most in specifications, even if they
rarely appear in production code.  When you want to say "this situation
cannot occur," you state it as a function from the supposed witness to
`False`.

Specifications that include negations (`¬P`) often look like:
- "this list is never empty after this operation" → `¬ (result = [])`
- "these two outputs never coincide" → `¬ (f x = g x)`
- "this function is injective" → `∀ x y, f x = f y → x = y`

All of these can be proved by `decide` when the types are finite and
decidable.
@@@ -/

-- Specifications involving negation
def negate (b : Bool) : Bool := !b

-- Specification: negate never returns its input
#check (by decide : ∀ b : Bool, negate b ≠ b)

-- Specification: negate is its own inverse
#check (by decide : ∀ b : Bool, negate (negate b) = b)

-- Disequality: sometimes the specification IS a negation
#check (by decide : (0 : Nat) ≠ 1)
#check (by decide : true ≠ false)

/-! @@@
## Summary

- **`Empty`**: an inductive type with no constructors; no inhabitants.
  Computationally: uninhabitable.  Logically: `False` (no proofs).
- **`Empty.rec` / `False.elim`**: given an `Empty`/`False`, produce
  any type — vacuously valid because the argument can never exist.
- **Negation**: `¬P` is *defined as* `P → False`.
  A proof of `¬P` is a function converting any proof of P into `False`.
- **`absurd`**: given `h : P` and `h' : ¬P`, conclude anything.
- **Impossible branches**: pattern matching on `Empty` requires zero
  cases — the exhaustiveness check is trivially satisfied.
- **`decide`** proves negations when the proposition is decidable.
- **Specifications use negation** to express constraints: "this cannot
  happen," "these are always distinct," "this function is injective."
@@@ -/

end Week04
