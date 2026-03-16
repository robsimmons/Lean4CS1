-- FPCourse/Unit1/Week00_AlgebraicTypes.lean
import Mathlib.Logic.Basic
import Mathlib.Data.Bool.Basic

/-! @@@
# Week 0: Algebraic Types — The Language of Computation and Logic

## One language. Two readings.

A *type* classifies values.  `Nat` classifies the natural numbers.
`Bool` classifies `true` and `false`.  A type answers the question:
*what values of this shape can exist?*

This course is organized around six ways of building types — six *type
constructors*.  Every data structure in computing is built from some
combination of these six.  And every proposition in propositional logic
is expressed by the same six constructors.

This is not an analogy.  It is the same language, read two ways.

| Constructor | Computational reading | Logical reading |
|---|---|---|
| Basic type | Atomic data | Atomic proposition |
| `α → β` | Function from α to β | α implies β |
| `α × β` | Pair: α bundled with β | Conjunction: α AND β |
| `α ⊕ β` | Choice: α OR β (as data) | Disjunction: α OR β (as claim) |
| `Empty` | Uninhabitable — nothing exists here | Falsity — no proof exists |
| `α → Empty` | α itself is uninhabitable | Negation: α is contradictory |

By the end of this week you will have seen all six in both readings.
You will have one vocabulary — *types and their inhabitants* — that
covers both.
@@@ -/

namespace Week00

/-! @@@
## 0.1  Basic Types: the atoms of computation and logic

The simplest types are defined by listing their values.  These are the
*atoms* — not built from other types; they just exist.
@@@ -/

-- Nat: the type of natural numbers.  Values: 0, 1, 2, 3, ...
#check (0 : Nat)
#check (42 : Nat)
#eval 2 + 3        -- 5
#eval 10 - 3       -- 7 (natural number subtraction, floors at 0)

-- Bool: two values.
#check (true : Bool)
#check (false : Bool)
#eval true && false  -- false
#eval true || false  -- true

-- String: sequences of characters.
#check ("hello" : String)
#eval "hello" ++ ", world"   -- "hello, world"
#eval "hello".length          -- 5

/-! @@@
The command `#eval e` *runs* expression `e` and prints its value.
The command `#check e` inspects the *type* of `e` without running it.

An *expression* is any piece of Lean text that has a type and reduces
to a value.  `2 + 3` has type `Nat` and reduces to `5`.

### The same question, two registers

We can ask of any type: *what are its inhabitants?*

| Type | Sample inhabitants |
|------|--------------------|
| `Nat` | `0`, `1`, `2`, `42` |
| `Bool` | `true`, `false` |
| `String` | `""`, `"hi"`, `"hello, world"` |

We can ask the identical question of *propositions*:

| Proposition (type) | Inhabitants |
|--------------------|-------------|
| `1 + 1 = 2` | exactly one: the proof `rfl` |
| `1 + 1 = 5` | none — it is false |
| `True` | exactly one: `True.intro` |
| `False` | none — it is false |

A proposition with at least one inhabitant is *true*.  A proposition
with no inhabitant is *false*.  In Lean, propositions ARE types.
@@@ -/

-- Proofs are terms.  `rfl` inhabits `1 + 1 = 2` the way `42` inhabits `Nat`.
example : 1 + 1 = 2 := rfl
example : True      := True.intro

-- `decide` runs Lean's built-in decision procedure to produce proofs
-- of *decidable* propositions — ones for which an algorithm exists.
example : 7 * 6 = 42       := by decide
example : 2 + 2 ≠ 5        := by decide
example : 100 < 200         := by decide

-- `#check` works on proofs too.
#check (rfl : 1 + 1 = 2)    -- the type IS the proposition
#check (True.intro : True)

/-! @@@
`rfl` is a term.  Its *type* is `1 + 1 = 2`.  The proposition is a type;
the proof is a value of that type.  This is the central fact of the course.

`decide` can only handle propositions for which computation terminates —
*decidable* propositions.  Concrete arithmetic facts are decidable.
Universal claims over all natural numbers (`∀ n : Nat, ...`) generally
are not, and require a proof.  We return to this in Week 7.
@@@ -/

/-! @@@
## 0.2  Function Types: `α → β`

The arrow type `α → β` is the type of **functions** from `α` to `β`.
A value of type `α → β` takes any input of type `α` and produces an
output of type `β`.

Functions are the most fundamental type constructor.  Every other
construct — recursion, type classes, proofs — ultimately reduces to
functions.
@@@ -/

-- Defining functions with `def`:
def double  : Nat → Nat    := fun n => n * 2
def isZero  : Nat → Bool   := fun n => n == 0
def negate  : Bool → Bool  := fun b => !b
def greet   : String → String := fun name => "Hello, " ++ name

#eval double 7         -- 14
#eval isZero 0         -- true
#eval isZero 5         -- false
#eval greet "Alice"    -- "Hello, Alice"

-- Multi-argument functions are *curried*:
-- `Nat → Nat → Nat` means `Nat → (Nat → Nat)`.
-- Applying one argument returns a function waiting for the second.
def add : Nat → Nat → Nat := fun a b => a + b

#eval add 3 4          -- 7   (apply both arguments)
#eval (add 3) 4        -- 7   (same: add 3 is itself a Nat → Nat)

-- Named argument style (equivalent, more readable for multi-arg):
def max' (a b : Nat) : Nat := if a ≥ b then a else b

#eval max' 5 3         -- 5
#eval max' 2 8         -- 8

/-! @@@
### The logical reading: implication

When `P` and `Q` are propositions, `P → Q` is the type of proofs that
**P implies Q**.  A proof of `P → Q` is a *function*: given any proof
of `P`, it returns a proof of `Q`.

This is not a metaphor.  The same keyword (`fun`), the same syntax
(`fun h => ...`), the same application rule — a proof of `P → Q`
literally IS a function.

**The identity function is simultaneously**:
- *Computational*: given any value, return it.
- *Logical*: if P holds then P holds (reflexivity of implication).
@@@ -/

-- Computational: identity function for data.
def myId (a : α) : α := a
#eval myId 42       -- 42
#eval myId "hello"  -- "hello"

-- Logical: if P holds, then P holds.
theorem p_implies_p (P : Prop) (h : P) : P := h
-- This IS the identity function, applied to a proof.

-- Implication is transitive: if P → Q and Q → R, then P → R.
-- Computation: function composition.
-- Logic: hypothetical syllogism.
theorem implies_trans (P Q R : Prop)
    (hpq : P → Q) (hqr : Q → R) : P → R :=
  fun hp => hqr (hpq hp)

-- The proof IS function composition: hqr ∘ hpq.
-- Compare with the computational version:
def compose (f : β → γ) (g : α → β) : α → γ := fun a => f (g a)

-- Their structures are identical.  The only difference is that
-- P, Q, R range over Prop instead of Type.

/-! @@@
## 0.3  Product Types: `α × β`

A **product type** `α × β` bundles a value of type `α` with a value of
type `β`.  To *build* a product you must supply BOTH components.  To
*use* a product you project out whichever component you need.

Products are how data is *aggregated*: a 2D point is an x AND a y;
a person record is a name AND an age AND a city.
@@@ -/

-- Building and projecting products:
def myPair : Nat × Bool := (7, true)
#eval myPair.1    -- 7       (first component)
#eval myPair.2    -- true    (second component)

-- Anonymous constructor ⟨_, _⟩ is equivalent to (_, _) for products:
def myPoint : Float × Float := ⟨3.0, 4.0⟩

-- Nested products (right-associative by default):
def myTriple : Nat × String × Bool := (42, "hello", false)
#eval myTriple.1        -- 42
#eval myTriple.2.1      -- "hello"
#eval myTriple.2.2      -- false

-- A function that takes a product and swaps its components:
def swap (p : α × β) : β × α := (p.2, p.1)
#eval swap (1, "one")    -- ("one", 1)
#eval swap (true, 42)    -- (42, true)

-- Products in function signatures (named arguments are sugar for products):
def hypotenuse (legs : Float × Float) : Float :=
  Float.sqrt (legs.1 ^ 2 + legs.2 ^ 2)
#eval hypotenuse (3.0, 4.0)   -- 5.0

/-! @@@
### The logical reading: conjunction (AND)

In logic, `P ∧ Q` holds when **both** P holds **and** Q holds.  A proof
of `P ∧ Q` is a pair: a proof of P together with a proof of Q.

`And` in Lean is literally a structure with two fields.  It IS a product
type, specialized to the case where the components are proofs.

| Product | And (conjunction) |
|---------|--------------------|
| `α × β` | `P ∧ Q` |
| `(a, b) : α × β` | `⟨h₁, h₂⟩ : P ∧ Q` |
| `p.1 : α` | `h.left : P` |
| `p.2 : β` | `h.right : Q` |
@@@ -/

-- Proving a conjunction: supply both halves.
example : 2 < 3 ∧ 3 < 4 := ⟨by decide, by decide⟩

-- Or: explicit constructor.
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := And.intro rfl rfl

-- Extracting from a conjunction:
theorem use_left  (h : P ∧ Q) : P := h.left
theorem use_right (h : P ∧ Q) : Q := h.right

-- Commutativity: if P ∧ Q then Q ∧ P.
-- Computation: swap the pair.
-- Logic: swap the conjunction.
theorem and_comm' (h : P ∧ Q) : Q ∧ P :=
  ⟨h.right, h.left⟩   -- this IS the swap function applied to proofs

-- Three-way conjunction:
example : 1 < 2 ∧ 2 < 3 ∧ 3 < 4 := by decide

/-! @@@
## 0.4  Sum Types: `Sum α β` (written `α ⊕ β`)

A **sum type** `α ⊕ β` carries either a value of type `α` **or** a
value of type `β`.  It represents a *choice* or *variant*: you get one
kind of thing or the other, and the tag `inl`/`inr` tells you which.

Sums are how programs handle **alternatives**: a result is either a
successful value or an error; a shape is a circle or a rectangle or a
triangle.
@@@ -/

-- Sum has two constructors: inl (left) and inr (right).
def aNum  : Nat ⊕ String := Sum.inl 42
def aStr  : Nat ⊕ String := Sum.inr "error"

-- To USE a sum, you must handle BOTH cases:
def describeNatOrStr (s : Nat ⊕ String) : String :=
  match s with
  | Sum.inl n => "a number: " ++ toString n
  | Sum.inr e => "a string: " ++ e

#eval describeNatOrStr aNum    -- "a number: 42"
#eval describeNatOrStr aStr    -- "a string: error"

-- The canonical programming sum: Option.
-- Option α represents either a value (some a) or absence (none).
-- It is a sum: Unit ⊕ α, roughly.
def safeDivide (a b : Nat) : Option Nat :=
  if b = 0 then none else some (a / b)

#eval safeDivide 10 2   -- some 5
#eval safeDivide 10 0   -- none

-- Using an Option:
def showResult (r : Option Nat) : String :=
  match r with
  | none   => "no result"
  | some n => "result: " ++ toString n

#eval showResult (safeDivide 10 2)    -- "result: 5"
#eval showResult (safeDivide 10 0)    -- "no result"

/-! @@@
### The logical reading: disjunction (OR)

In logic, `P ∨ Q` holds when **at least one** of P or Q holds.  A proof
of `P ∨ Q` is either a proof of P (tagged `Or.inl`) or a proof of Q
(tagged `Or.inr`).

`Or` IS a sum type, specialized to propositions.

| Sum | Or (disjunction) |
|-----|------------------|
| `α ⊕ β` | `P ∨ Q` |
| `Sum.inl (a : α)` | `Or.inl (h : P)` |
| `Sum.inr (b : β)` | `Or.inr (h : Q)` |
| `match s with \| inl a => ... \| inr b => ...` | `match h with \| inl h => ... \| inr h => ...` |

To *prove* a disjunction, pick one side and prove it.
To *use* a disjunction, case-split on which side holds (just like `match`).
@@@ -/

-- Proving a disjunction: choose a side.
example : 1 = 1 ∨ 1 = 2 := Or.inl rfl      -- left side
example : 1 = 2 ∨ 1 = 1 := Or.inr rfl      -- right side
example : 3 < 4 ∨ 4 < 3 := by decide       -- decide picks the right side

-- Using a disjunction: case analysis.
theorem or_comm' (h : P ∨ Q) : Q ∨ P :=
  match h with
  | Or.inl hp => Or.inr hp   -- had P; now tag it as inr
  | Or.inr hq => Or.inl hq   -- had Q; now tag it as inl
-- This IS `swap` applied to proofs of disjuncts.

-- Disjunction from an implication:
theorem or_weaken (h : P) : P ∨ Q := Or.inl h

/-! @@@
## 0.5  The Empty Type: `Empty` and `False`

The **empty type** has no constructors and no values.  It is impossible
to produce a term of this type.

In computation: `Empty` represents a branch that can never be reached.
A function returning `Empty` can never actually return.  Pattern-matching
on a value of type `Empty` needs **zero** branches — vacuously complete.

In logic: `False` is the proposition with no proof.  A proposition that
cannot be proved is *false*.

`Empty : Type` and `False : Prop` are the same idea in two universes.
@@@ -/

-- `Empty` has no constructors — you cannot produce a value of it.
-- But you CAN write a function FROM Empty (with no cases to handle):
def fromEmpty (e : Empty) : α := nomatch e

-- In logic: `False → P` (ex falso quodlibet — from absurdity, anything).
theorem ex_falso (h : False) : P := False.elim h

-- Why is this useful?  Because it discharges impossible cases.
-- If a case leads to `False`, the rest of the goal becomes irrelevant.
example (h : 2 + 2 = 5) : "pigs fly" = "pigs fly" :=
  absurd h (by decide)   -- decide proves ¬(2+2=5); absurd closes the goal

-- `absurd : P → ¬P → Q`
-- Given a proof of P and a proof of ¬P, produce anything.
-- This is the logical short-circuit: contradiction → done.

/-! @@@
The power of the empty type: every impossible case reduces to one.

When your program reaches a state that "cannot happen," the right tool
is to prove it is `False` and use `False.elim` (or `absurd`) to discharge
the goal.  The program does not crash; it never reaches that branch at all,
because the type system certified the branch is unreachable.

`nomatch e` is Lean's syntax for pattern-matching on a value of a type
with no constructors: the match is exhaustive with zero branches.
@@@ -/

/-! @@@
## 0.6  Functions to Empty: `α → Empty` and `¬P`

The most surprising type constructor: **a function whose codomain is
the empty type**.

A value of type `α → Empty` is a function that, if given an `α`, would
produce an `Empty`.  But `Empty` has no values — so such a function can
never complete its job.  This means: if such a function *exists*, then
`α` itself must have had no values to pass in.  The function *proves*
that `α` is uninhabited.

In computation: `α → Empty` certifies that `α` has no values.

In logic: `¬P` is **defined** as `P → False`.  A proof of `¬P` is a
function: given any proof of `P`, produce a proof of `False`.  Since
`False` has no proofs, the function can never fire — which means P has
no proofs, i.e., P is false.

Negation is not a primitive.  It IS the function arrow, aimed at `False`.
@@@ -/

-- ¬P unfolds to P → False:
#print Not   -- def Not (a : Prop) : Prop := a → False

-- Every proof of ¬P is a function P → False.
-- `decide` constructs this function automatically for decidable cases.
example : ¬ (1 = 2)  := by decide
example : ¬ (3 > 5)  := by decide
example : ¬ (0 = 1)  := by decide

-- Negation from definitions:
-- ¬(1 = 2) means (1 = 2) → False.
-- 1 and 2 have different normal forms, so the Eq constructor cannot apply;
-- Lean sees there are zero cases to match, so `nomatch` closes the goal.
theorem one_ne_two : ¬ (1 = 2) := fun h => nomatch h

-- Contradiction: if P and ¬P both hold, everything follows.
theorem contradiction (h : P) (hne : ¬P) : Q :=
  False.elim (hne h)   -- hne h : False, then ex falso

-- Double negation introduction (the direction that holds constructively):
-- "If P holds, then P is not contradictory."
theorem not_not_intro (h : P) : ¬¬P :=
  fun hnp => hnp h    -- hnp : ¬P = P → False; apply it to h : P

-- Example: ¬(P ∧ ¬P) — no proposition and its negation can both hold.
theorem not_and_not (h : P ∧ ¬P) : False :=
  h.right h.left      -- apply ¬P (= h.right) to P (= h.left)

/-! @@@
## 0.7  The Six Constructors Together

Here is the complete picture.  Every type you will write in this course
is built from some combination of these six.  Every proposition you will
reason about is expressed by some combination of these six.

| Constructor | Computational | Logical |
|-------------|---------------|---------|
| Basic type | `Nat`, `Bool`, `String`, ... | Atomic proposition `P : Prop` |
| `α → β` | Function: transform α into β | Implication: α proves β |
| `α × β` | Product: carry BOTH α and β | Conjunction: BOTH α and β |
| `α ⊕ β` | Sum: carry ONE OF α or β | Disjunction: ONE OF α or β |
| `Empty` / `False` | No value exists | No proof exists |
| `α → Empty` / `¬α` | α is uninhabited | α is contradictory |

The question "what inhabits this type?" has two flavors:
- Computational types (`Type`): inhabitants are *data*.
- Logical types (`Prop`): inhabitants are *proofs*.

But the **constructors are shared**.  Products bundle data AND proofs
the same way.  Sums tag data AND proofs the same way.  Functions
transform data AND convert proofs the same way.  The empty type
represents impossible data AND impossible proofs.

You do not need two languages.  You are learning one.
@@@ -/

-- All six constructors demonstrated side by side:

-- Product / And
def dataPair  : Nat × Bool := ⟨5, true⟩
def proofPair : 2 < 3 ∧ 3 < 4 := ⟨by decide, by decide⟩

-- Sum / Or
def dataSum    : Nat ⊕ Bool  := Sum.inl 7
def proofDisj  : 2 < 3 ∨ 3 < 2 := Or.inl (by decide)

-- Function / Implication
def dataFun   : Nat → Nat   := fun n => n + 1
def proofImpl : 2 < 3 → 2 ≤ 3 := fun h => Nat.le_of_lt h

-- Negation / Uninhabited
def proofNeg  : ¬ (1 = 2) := by decide

-- Empty type: a function from Empty returns anything
def fromImpossible (e : Empty) : Nat × Bool × String := nomatch e

/-! @@@
## 0.8  Challenges in programming with algebraic types

Understanding the six constructors is not yet fluency.  The challenge is
knowing **which constructor fits each situation**.

Here are the fundamental design questions:

**Use a product when** you need to carry multiple pieces of data at once.
A point is x AND y.  A function's return type is a product when it returns
two things.  A precondition bundled with a return value is a product of
data and proof.

**Use a sum when** data has multiple, mutually exclusive forms.  An API
result is success OR error.  A command is add OR remove OR update.
Pattern-matching IS elimination of a sum — you must handle every case.

**Use a function when** you want to defer or parameterize computation.
A callback, a comparator, a predicate — these are function-type arguments.

**Use negation (function to False) when** you need to *rule out* a case.
A precondition `h : x ≠ 0` is `(x = 0) → False`.  It certifies the
impossible before the program runs.

**Use Empty/False when** a branch cannot exist.  The type system then
verifies you never reach it; `nomatch` or `False.elim` closes the goal.

The payoff: once you have the right type, the program often writes itself.
The type tells you what constructors to use; the exhaustiveness checker
tells you which cases remain.  Types are not just documentation —
they are your co-programmer.

## Exercises

1. Write a function `classify : Nat → String ⊕ String` that returns
   `Sum.inl "even"` if the input is even and `Sum.inr "odd"` if it is odd.
   Use `if/then/else` and the `%` (mod) operator.

2. A `Result` type represents either success or failure:
   ```lean
   inductive Result (α ε : Type) where
     | ok  : α → Result α ε
     | err : ε → Result α ε
   ```
   Define it.  Then write a function `safeDiv : Nat → Nat → Result Nat String`
   that returns `ok (a / b)` when `b ≠ 0` and `err "division by zero"` otherwise.

3. Write the type of a function `lookup` that takes a `Nat` key and a
   `List (Nat × String)` (association list) and returns `Option String`.
   Then implement it by recursion on the list.

4. Explain in your own words why a function of type `α → Empty` certifies
   that `α` has no values.  Then write a term of type `False → Nat × Bool × String`
   and explain what it means in both the computational and logical readings.

5. Use `decide` to verify each claim.  For each, identify which type
   constructor(s) the proposition uses:
   (a) `2 < 3 ∧ 3 < 4`
   (b) `2 < 3 ∨ 3 < 2`
   (c) `¬ (2 = 3)`
   (d) `¬ (2 < 3 ∧ 3 < 2)`
   (e) `(2 < 3 ∧ ¬(3 < 2)) ∨ (3 < 2 ∧ ¬(2 < 3))`
@@@ -/

end Week00
