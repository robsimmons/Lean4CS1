-- Distillate/Unit1/Week00_TypesExpressions.lean
import Mathlib.Logic.Basic
import Mathlib.Data.Bool.Basic

/-! @@@
# Week 0: Types and Expressions

## One language. Two readings.

A *type* classifies values.  `Nat` classifies `0, 1, 2, 3, …`.
`Bool` classifies `true` and `false`.  When you encounter a type, ask:
*what values inhabit this type?*

This question works equally well for data and for logic.

| In data | In logic |
|---------|---------|
| `Nat` | any claim that Lean can count witnesses to |
| `Bool` | a two-valued *computation*, not a claim |
| `1 + 1 = 2` | a *proposition* — a claim whose witnesses are proofs |

This course is organized around six kinds of types.  Every data structure
in computing is built from some combination of them.  Every proposition in
logic is expressed by the same six constructors.  This is not an analogy.
It is one language with two readings.

| Constructor | Computational reading | Logical reading |
|---|---|---|
| Basic type | Atomic data (`Nat`, `Bool`, `String`) | Atomic proposition |
| `α → β` | Function from α to β | α implies β |
| `α × β` | Pair: α bundled with β | Conjunction: α AND β |
| `α ⊕ β` | Choice: α OR β | Disjunction: α OR β |
| `Empty` | Uninhabitable — nothing lives here | Falsity — no proof exists |
| `α → Empty` | α is itself uninhabitable | Negation: α is contradictory |

By the end of the course you will have seen all six in both readings,
and you will use one vocabulary — *types and their inhabitants* — for both.
@@@ -/

namespace Week00

/-! @@@
## 0.1  Basic types: atoms of computation and logic

Basic types are not constructed from anything else.  They are given to you
by the language.  You encounter them by name.
@@@ -/

-- Nat: natural numbers 0, 1, 2, 3, ...
#check (0 : Nat)
#check (42 : Nat)
#eval 2 + 3        -- 5
#eval 10 - 3       -- 7  (natural-number subtraction floors at 0)
#eval 10 - 15      -- 0  (not negative — Nat has no negative values)

-- Bool: exactly two values.
#check (true : Bool)
#check (false : Bool)
#eval true && false  -- false
#eval true || false  -- true
#eval !true          -- false

-- String: sequences of characters.
#check ("hello" : String)
#eval "hello" ++ ", world"   -- "hello, world"
#eval "hello".length          -- 5

/-! @@@
## 0.2  The Lean notional machine

Think of Lean as a machine with one job: given an expression, apply
reduction rules one step at a time until nothing more can be reduced.
The irreducible result is called the *normal form*.

```
  expression  ──→  Lean kernel  ──→  normal form
   (source)        (evaluates)       (irreducible value)
```

Every `#eval` invokes this machine.  Every proof you will see later runs
the same machine on a decision procedure.

We write `e ↝ v` to mean "expression `e` reduces to value `v` in one step."

| Expression | What happens | Normal form |
|---|---|---|
| `2 + 3` | arithmetic step | `5` |
| `10 - 3` | arithmetic step | `7` |
| `true && false` | `true && b ↝ b` by definition | `false` |
| `"hello".length` | string library | `5` |

`#check e` inspects the *type* of `e` without evaluating it.
Types are checked statically; values are produced dynamically.
Both happen before you see any output.
@@@ -/

/-! @@@
## 0.3  Propositions are types; proofs are terms

Lean does something that at first looks surprising: it uses the *same*
type machinery for logic that it uses for data.

A *proposition* is a claim that may or may not be true.  In Lean,
propositions are types.  A *proof* of a proposition is a *term* of that
type — the same relationship that holds between any type and its values.

| Type (data) | A sample value | Type (logic) | A sample proof |
|---|---|---|---|
| `Nat` | `42` | `1 + 1 = 2` | `rfl` |
| `Bool` | `true` | `True` | `True.intro` |
| `String` | `"hi"` | `2 ≠ 3` | `by decide` |

A proposition with at least one proof is *true*.
A proposition with no proof is *false*.

You do not need to construct proofs yourself in this course.  Lean's
`decide` term does that for you, for the class of propositions this course
uses most.
@@@ -/

-- Checking that a true proposition has a proof
#check (rfl : 1 + 1 = 2)       -- rfl : 1 + 1 = 2
#check (True.intro : True)      -- True.intro : True

-- decide: Lean evaluates a decision procedure and returns a proof (or fails)
#check (by decide : 2 + 3 = 5)
#check (by decide : true && false = false)
#check (by decide : ¬ (1 = 2))   -- negation: 1 ≠ 2

/-! @@@
Notice: `by decide` is not magic.  It runs the Lean reduction machine on
a *decision procedure* — a function that outputs `true` or `false` — and,
if the result is `true`, packages up the computation trace as a proof.
You will understand exactly how this works by Week 5.

For now, the key point: **when you can `#eval` an expression and get
`true`, you can almost always close the corresponding proposition with
`by decide`.**
@@@ -/

-- If #eval confirms it, decide can prove it
#eval (2 + 3 == 5)           -- true
#check (by decide : 2 + 3 = 5)  -- works: same fact, proven

-- The distinction: = is a proposition (logical claim); == is a Bool (computation)
-- = lives in Prop; the proof is a term
-- == lives in Bool; the result is a value
#check @Eq        -- Eq : α → α → Prop
#check @BEq.beq   -- BEq.beq : α → α → Bool

/-! @@@
## 0.4  The Bool / Prop distinction

`Bool` and `Prop` both express "true or false" ideas, but they are
different.

| | `Bool` | `Prop` |
|---|---|---|
| What it is | A two-valued data type | A type of logical claims |
| How you "check" | `#eval` — run the program | `#check (by decide : ...)` |
| What `true`/`false` mean | Two concrete values | "proved" / "not proved" |
| Can you compute with it? | Yes: `if b then ... else ...` | No — it's a claim, not a branch |

You will use both throughout this course:
- `Bool` when you need to *compute* a yes/no answer.
- `Prop` when you need to *state and verify* a logical claim.

The two worlds connect through `Decidable`: for many propositions, Lean
can *decide* them — running a Bool computation to produce a proof.
That connection is exactly what `by decide` exploits.
@@@ -/

-- Bool computation: use if/then/else
def isEven (n : Nat) : Bool := n % 2 == 0

#eval isEven 4   -- true
#eval isEven 7   -- false

-- Prop claim: state and verify
#check (by decide : isEven 4 = true)
#check (by decide : isEven 7 = false)

/-! @@@
## 0.5  The six constructors: a first pass

The table at the top of this week is your map for the entire course.
Here is a brief first encounter with each constructor, in both readings.
Subsequent weeks explore each in depth.
@@@ -/

-- (1) Basic type: Nat — atoms that need no further construction
example : Nat := 7

-- (2) Function type: Nat → Nat — both a function and an implication
example : Nat → Nat := fun n => n + 1

-- (3) Product type: Nat × Bool — a pair, in logic also a conjunction
example : Nat × Bool := (3, true)

-- (4) Sum type: Bool ⊕ Nat — a choice, in logic also a disjunction
--   (⊕ is Sum in the Lean standard library)
example : Bool ⊕ Nat := Sum.inl true
example : Bool ⊕ Nat := Sum.inr 42

-- (5) Empty type: nothing inhabits it; in logic this is False
-- (we cannot write "example : Empty := ..." — no such term exists)
-- We can however state that:
#check (Empty)   -- Empty : Type

-- (6) α → Empty: a function TO the empty type; in logic this is negation ¬α
-- If α had an inhabitant, we could produce one of Empty — but Empty has none,
-- so this type is only inhabited when α itself is empty (false).
example : 1 = 2 → False := by decide  -- 1 ≠ 2, so this implication holds

/-! @@@
## Summary

- Every Lean expression has a **type**.  Types classify values.
- **Basic types**: `Nat`, `Bool`, `String` — given, not constructed.
- **`#eval`** runs the reduction machine and shows the normal form.
- **`#check`** shows the type without evaluating.
- **Propositions are types**.  Proofs are terms of propositional type.
- **`decide`** produces proofs of decidable propositions automatically.
- **`Bool` vs `Prop`**: computation vs. logical claim.
- Six type constructors cover all data structures *and* all of
  propositional logic.  Same language, two readings.
@@@ -/

end Week00
