import VersoManual

open Verso Doc
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

namespace Week00
variable (α β : Type)
variable (P Q : Prop)
variable (a : α)
variable (b : β)
variable (h₁ : P)
variable (h₂ : Q)
variable (p : α × β)
variable (h : P ∧ Q)


#doc (Manual) "Week 0: Algebraic Types — The Language of Computation and Logic" =>

# One language. Two readings.
%%%
number := false
%%%

A _type_ classifies values.  {name}`Nat` classifies the natural numbers.
{name}`Bool` classifies {lean}`true` and {lean}`false`.  When you encounter a type, ask:
_what values of this type can exist?_

This course is organized around six kinds of types.  Every data structure
in computing is built from some combination of these six.  And every
proposition in propositional logic is expressed by the same six constructors.

This is not an analogy.  It is the same language, read two ways.

:::table
*
 * Constructor
 * Computational reading
 * Logical reading
*
 * Basic type
 * Atomic data
 * Atomic proposition
*
 * {lean}`α → β`
 * Function from `α` to `β`
 * Implication: $`α → β`
*
 * {lean}`α × β`
 * Pair: α bundled with β
 * Conjunction: $`α \wedge β`
*
 * {lean}`α ⊕ β`
 * Choice: α OR β (as data)
 * Disjunction: $`α \vee β`
*
 * {lean}`Empty`
 * Uninhabitable — nothing exists here
 * Falsity $`\bot` — no proof exists
*
 * {lean}`α → Empty`
 * α itself is uninhabitable
 * Negation $`\neg α`: $`α` is contradictory
:::

By the end of this week you will have seen all six in both readings.
You will have one vocabulary — _types and their inhabitants_ — that
covers both.  You do not need two languages.  You are learning one.

# Basic Types: the atoms of computation and logic

*Why basic types?* Before you can build anything, you need raw
material — types that are not constructed from anything else.  Basic
types are your atoms: given to you, not derived.

You encounter them by name: {name}`Nat`, {name}`Bool`, {name}`String`.  Their values
are listed explicitly and cannot be broken down further.

```lean
-- Nat: the type of natural numbers.  Values: 0, 1, 2...
#check (0 : Nat)
#check (42 : Nat)
#eval 2 + 3   -- 5
#eval 10 - 3  -- 7 (natural number subtraction, floors at 0)

-- Bool: two values.
#check (true : Bool)
#check (false : Bool)
#eval true && false  -- false
#eval true || false  -- true

-- String: sequences of characters.
#check ("hello" : String)
#eval "hello" ++ ", world" -- "hello, world"
#eval "hello".length       -- 5
```

*The Lean notional machine.*  Think of Lean as a machine with one job:
given an expression, apply reduction rules one step at a time until no
further reduction is possible.  The irreducible result is the *normal form*.

```
  expression  ──→  Lean kernel  ──→  normal form
   (source)        (evaluates)       (irreducible value)
```

Every `#eval` you write invokes this machine.  Every `by decide` runs
it on a decision procedure.  Every {name}`rfl` succeeds because both sides
of the equation reach the *same* normal form.

Each `#eval` above is a chain of named reductions:

:::table
*
 * Expression
 * Reduction steps
 * Normal form
*
 * {lean}`2 + 3`
 * one arithmetic step
 * {lean}`5`
*
 * {lean}`10 - 3`
 * one arithmetic step
 * {lean}`7`
*
 * {lean}`true && false`
 * `true && b ↝ b` (definition of `&&`)
 * {lean}`false`
*
 * {lean}`"hello" ++ ", world"`
 * string concat definition
 * {lean}`"hello, world"`
*
 * {lean}`"hello".length`
 * list length definition
 * {lean}`5`
:::

The symbol `↝` means _reduces to in one step_.  You will see it used
throughout this course whenever a specific reduction rule is being named.

`#check e` inspects the _type_ of `e` without evaluating it.  Types are
checked statically at elaboration time; values are produced dynamically
at evaluation time.  Both happen before you see any output.

An _expression_ is any piece of Lean text that has a type and can be
evaluated to a normal form.

## The same question, two registers

We can ask of any type: *what are its inhabitants?*

:::table
*
 * Type
 * Sample inhabitants
*
 * {lean}`Nat`
 * {lean}`0`, {lean}`1`, {lean}`2`, {lean}`42`
*
 * {lean}`Bool`
 * {lean}`true`, {lean}`false`
*
 * {lean}`String`
 * {lean}`""`, {lean}`"hi"`, {lean}`"hello, world"`
:::

We can ask the identical question of _propositions_:

:::table
*
 * Proposition (type)
 * Inhabitants
*
 * {lean}`1 + 1 = 2`
 * exactly one: the proof {lean}`rfl`
*
 * {lean}`1 + 1 = 5`
 * none — it is false
*
 * {lean}`True`
 * exactly one: {name}`True.intro`
*
 * {lean}`False`
 * none — it is false
:::

A proposition with at least one inhabitant is _true_.  A proposition
with no inhabitant is _false_.  In Lean, propositions ARE types.

```lean
-- Proofs are terms.  `rfl` inhabits `1 + 1 = 2` the way `42` inhabits `Nat`.
example : 1 + 1 = 2 := rfl   -- Evaluation: 1+1 ↝ 2, same as the right side
example : True      := True.intro

-- `decide` evaluates a decision procedure to produce a proof automatically.
example : 7 * 6 = 42       := by decide  -- Evaluation: 7*6 ↝ 42 ✓
example : 2 + 2 ≠ 5        := by decide  -- Evaluation: 2+2 ↝ 4 ≠ 5 ✓
example : 100 < 200        := by decide  -- Evaluation: comparison ↝ true ✓

-- `#check` works on proofs too.
#check (rfl : 1 + 1 = 2)    -- the type IS the proposition
#check (True.intro : True)
```

*Evaluation.*  {lean}`rfl` proves `a = b` when `a` and `b` _evaluate to the
same normal form_.  {lean}`1 + 1 = 2` holds by {lean}`rfl` because both sides reduce
to `2` — the equality is *definitional*, certified by computation.

*Evaluation.*  {tactic}`decide` works by evaluating the _decision procedure_
for the proposition.  For {lean}`7 * 6 = 42`, Lean evaluates {lean}`7 * 6` to {lean}`42`,
confirms both sides are the same, and constructs the proof automatically.
If evaluation had produced {lean}`false`, the file would not compile — the
proof term would be absent, and the type would be uninhabited.

{tactic}`decide` can only handle propositions for which evaluation terminates —
_decidable_ propositions.  Concrete arithmetic is decidable; universal
claims over all natural numbers are not.  We return to this in Week 7.

# Function Types: {lean}`α → β`

*Why function types?*  Every transformation in programming — mapping,
filtering, converting, composing — is a function.  Functions are also
how you prove implications: a proof of `P → Q` is literally a function
from proofs of `P` to proofs of `Q`.  Mastering `→` unlocks both.

```
  α → β

  ┌───┐           ┌───┐
  │ α │  ──f──→   │ β │
  └───┘  (apply)  └───┘

  Build:  fun a => ...   (introduce a function)
  Use:    f a            (apply it to an argument; β-reduction fires)
```

The arrow type {lean}`α → β` is the type of _functions_ from {lean}`α` to {lean}`β`.
A value of type {lean}`α → β` takes any input of type {lean}`α` and produces an
output of type {lean}`β`.

Functions are the most fundamental type constructor.  Every other
construct — recursion, type classes, proofs — ultimately reduces to
functions.

```lean
-- Defining functions with `def`:
def double  : Nat → Nat    := fun n => n * 2
def isZero  : Nat → Bool   := fun n => n == 0
def negate  : Bool → Bool  := fun b => !b
def greet   : String → String := fun name => "Hello, " ++ name

-- Evaluation: applying a function substitutes the argument for the parameter.
-- This substitution step is called β-reduction.
-- double 7 ↝ 7 * 2 ↝ 14        (β-reduction, then arithmetic)
-- isZero 0 ↝ 0 == 0 ↝ true      (β-reduction, then BEq)
-- greet "Alice" ↝ "Hello, " ++ "Alice" ↝ "Hello, Alice"
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
```

## The logical reading: implication

When $`P` and $`Q` are propositions, $`P → Q` is the type of proofs that
*P implies Q*.  A proof of $`P → Q` is a _function_: given any proof
of $`P`, it returns a proof of $`Q`.

This is not a metaphor.  The same keyword (`fun`), the same syntax
(`fun h => ...`), the same application rule — a proof of {lean}`P → Q`
literally IS a function.

*The identity function is simultaneously*:
- _Computational_: given any value, return it.
- _Logical_: if P holds then P holds (reflexivity of implication).

```lean
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
```

# Product Types: {lean}`α × β`

*Why product types?*  Real programs combine data: a point has an x
coordinate AND a y coordinate; a database record has a name AND an age
AND an address.  Whenever you need to carry multiple pieces of data
simultaneously, you reach for a product.

```
  α × β

  ┌──────────────┐
  │  .1  :  α    │   ← first component
  │  .2  :  β    │   ← second component
  └──────────────┘

  Build:  (a, b)   or   ⟨a, b⟩
  Use:    p.1, p.2       (projections; ι-reduction fires)
```

A *product type* `α × β` bundles a value of type `α` with a value of
type `β`.  To _build_ a product you must supply BOTH components.  To
_use_ a product you project out whichever component you need.

Products are how data is _aggregated_: a 2D point is an x AND a y;
a person record is a name AND an age AND a city.

```lean
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
```

## The logical reading: conjunction (AND)

In logic, $`P ∧ Q` holds when *both* P holds *and* Q holds.  A proof
of $`P ∧ Q` is a pair: a proof of $`P` together with a proof of $`Q`.

`And` in Lean is literally a structure with two fields.  It IS a product
type, specialized to the case where the components are proofs.


:::table
*
 * Product
 * And (conjunction)
*
 * {lean}`α × β`
 * {lean}`P ∧ Q`
*
 * {lean}`((a, b) : α × β)`
 * {lean}`(⟨h₁, h₂⟩ : P ∧ Q)`
*
 * {lean}`(p.1 : α)`
 * {lean}`(h.left : P)`
*
 * {lean}`(p.2 : β)`
 * {lean}`(h.right : Q)`
:::

```lean
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
-- Evaluation: ⟨h.right, h.left⟩ ↝ ⟨proof-of-Q, proof-of-P⟩  (projections reduce)
theorem and_comm' (h : P ∧ Q) : Q ∧ P :=
  ⟨h.right, h.left⟩   -- this IS the swap function applied to proofs

-- Three-way conjunction:
example : 1 < 2 ∧ 2 < 3 ∧ 3 < 4 := by decide
```

# Sum Types: {lean}`Sum α β` (written {lean}`α ⊕ β`)

*Why sum types?*  Real programs handle alternatives: a network request
either succeeds OR fails; a command is either add OR remove OR update;
a shape is a circle OR a rectangle OR a triangle.  Sums capture this
structure in the type — and pattern-matching forces you to handle every
case.

```
  α ⊕ β

  ┌──────────────────────────┐
  │  Sum.inl (a : α)         │   ← "I have an α"
  │    OR                    │
  │  Sum.inr (b : β)         │   ← "I have a β"
  └──────────────────────────┘

  Build:  Sum.inl a   or   Sum.inr b
  Use:    match s with | Sum.inl a => ... | Sum.inr b => ...
```

A *sum type* `α ⊕ β` carries either a value of type `α` *or* a
value of type `β`.  It represents a _choice_ or _variant_: you get one
kind of thing or the other, and the tag `inl`/`inr` tells you which.

Sums are how programs handle *alternatives*: a result is either a
successful value or an error; a shape is a circle or a rectangle or a
triangle.

```lean
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
```

## The logical reading: disjunction (OR)

In logic, `P ∨ Q` holds when *at least one* of P or Q holds.  A proof
of `P ∨ Q` is either a proof of P (tagged `Or.inl`) or a proof of Q
(tagged `Or.inr`).

`Or` IS a sum type, specialized to propositions.

:::table
*
 * Sum
 * Or (disjunction)
*
 * {lean}`α ⊕ β`
 * {lean}`P ∨ Q`
*
 * {lean}`Sum.inl (a : α)`
 * {lean}`Or.inl (h₁ : P)`
*
 * {lean}`Sum.inr (b : β)`
 * {lean}`Or.inr (h₂ : Q)`
*
 * ```
   match s with
    | inl a => ...
    | inr b => ...
   ```
 * ```
   match h with
    | inl h => ...
    | inr h => ...
   ```
:::


To _prove_ a disjunction, pick one side and prove it.
To _use_ a disjunction, case-split on which side holds (just like `match`).

```lean
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
```

# The Empty Type: {lean}`Empty` and {lean}`False`

*Why an empty type?*  Sometimes a situation is genuinely impossible:
a division by zero that your types have already ruled out; a branch of
a proof that leads to contradiction.  When you can prove a situation is
impossible, the empty type lets you discharge it cleanly — the type
system certifies the branch is unreachable.

The *empty type* has no constructors and no values.  It is impossible
to produce a term of this type.

In computation: {lean}`Empty` represents a branch that can never be reached.
A function returning {lean}`Empty` can never actually return.  Pattern-matching
on a value of type {lean}`Empty` needs *zero* branches — vacuously complete.

In logic: {lean}`False` is the proposition with no proof.  A proposition that
cannot be proved is _false_.

{lean}`(Empty : Type)` and {lean}`(False : Prop)` are the same idea in two universes.

```lean
-- `Empty` has no constructors — you cannot produce a value of it.
-- But you CAN write a function FROM Empty (with no cases to handle):
def fromEmpty (e : Empty) : α := nomatch e

-- In logic: `False → P` (ex falso quodlibet — from absurdity, anything).
theorem ex_falso {P : Prop} (h : False) : P := False.elim h

-- Why is this useful?  Because it discharges impossible cases.
-- If a case leads to `False`, the rest of the goal becomes irrelevant.
example (h : 2 + 2 = 5) : "pigs fly" = "pigs fly" :=
  absurd h (by decide)   -- decide proves ¬(2+2=5); absurd closes the goal

-- `absurd : P → ¬P → Q`
-- Given a proof of P and a proof of ¬P, produce anything.
-- This is the logical short-circuit: contradiction → done.
```

The power of the empty type: every impossible case reduces to one.

When your program reaches a state that "cannot happen," the right tool
is to prove it is {lean}`False` and use {lean}`False.elim` (or {lean}`absurd`) to discharge
the goal.  The program does not crash; it never reaches that branch at all,
because the type system certified the branch is unreachable.

`nomatch e` is Lean's syntax for pattern-matching on a value of a type
with no constructors: the match is exhaustive with zero branches.

# Functions to Empty: {lean}`α → Empty` and {lean}`¬P`

*Why functions to empty?*  Ruling out a case is as important as
handling one.  When you write a precondition `h : n ≠ 0`, you are
carrying a function `(n = 0) → False` — proof that passing in a
zero is impossible.  Negation is not a primitive added to the language;
it falls out of the function arrow and the empty type that you already
have.

The most surprising type constructor: *a function whose codomain is
the empty type*.

A value of type {lean}`α → Empty` is a function that, if given an {lean}`α`, would
produce an {lean}`Empty`.  But {lean}`Empty` has no values — so such a function can
never complete its job.  This means: if such a function _exists_, then
{lean}`α` itself must have had no values to pass in.  The function _proves_
that {lean}`α` is uninhabited.

In computation: {lean}`α → Empty` certifies that {lean}`α` has no values.

In logic: {lean}`¬P` is *defined* as {lean}`P → False`.  A proof of {lean}`¬P` is a
function: given any proof of {lean}`P`, produce a proof of {lean}`False`.  Since
{lean}`False` has no proofs, the function can never fire — which means {lean}`P` has
no proofs, i.e., {lean}`P` is false.

Negation is not a primitive.  It IS the function arrow, aimed at {lean}`False`.

```lean
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
theorem contradiction {P Q : Prop} (h : P) (hne : ¬P) : Q :=
  False.elim (hne h)   -- hne h : False, then ex falso

-- Double negation introduction (the direction that holds constructively):
-- "If P holds, then P is not contradictory."
theorem not_not_intro (h : P) : ¬¬P :=
  fun hnp => hnp h    -- hnp : ¬P = P → False; apply it to h : P

-- Example: ¬(P ∧ ¬P) — no proposition and its negation can both hold.
theorem not_and_not (h : P ∧ ¬P) : False :=
  h.right h.left      -- apply ¬P (= h.right) to P (= h.left)
```

# The Six Constructors Together
%%%
tag := "six-constructors"
%%%

Here is the complete picture.  Every type you will write in this course
is built from some combination of these six.  Every proposition you will
reason about is expressed by some combination of these six.

:::table
*
 * Constructor
 * Computational
 * Logical
*
 * Basic type
 * {lean}`Nat`, {lean}`Bool`, {lean}`String`, …
 * Atomic proposition {lean}`(P : Prop)`
*
 * {lean}`α → β`
 * Function transform `α` into `β`
 * Implication: Implication: α proves β
*
 * {lean}`α × β`
 * Product: carry BOTH α and β
 * Conjunction: BOTH α and β
*
 * {lean}`α ⊕ β`
 * Sum: carry ONE OF α OR β
 * Disjunction: ONE OF α or β
*
 * {lean}`Empty` / {lean}`False`
 * No value exists
 * No proof exists
*
 * {lean}`α → Empty` / {lean}`¬P`
 * α is uninhabited
 * α is contradictory
:::


The question "what inhabits this type?" has two flavors:
- Computational types (`Type`): inhabitants are _data_.
- Logical types (`Prop`): inhabitants are _proofs_.

But the *constructors are shared*.  Products bundle data AND proofs
the same way.  Sums tag data AND proofs the same way.  Functions
transform data AND convert proofs the same way.  The empty type
represents impossible data AND impossible proofs.

```lean
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
```

# Challenges in programming with algebraic types

Understanding the six constructors is not yet fluency.  The challenge is
knowing *which constructor fits each situation*.

Here are the fundamental design questions:

*Use a product when* you need to carry multiple pieces of data at once.
A point is x AND y.  A function's return type is a product when it returns
two things.  A precondition bundled with a return value is a product of
data and proof.

*Use a sum when* data has multiple, mutually exclusive forms.  An API
result is success OR error.  A command is add OR remove OR update.
Pattern-matching IS elimination of a sum — you must handle every case.

*Use a function when* you want to defer or parameterize computation.
A callback, a comparator, a predicate — these are function-type arguments.

*Use negation (function to False) when* you need to *rule out* a case.
A precondition `h : x ≠ 0` is `(x = 0) → False`.  It certifies the
impossible before the program runs.

*Use Empty/False when* a branch cannot exist.  The type system then
verifies you never reach it; `nomatch` or {lean}`False.elim` closes the goal.

The payoff: once you have the right type, the program often writes itself.
The type tells you what constructors to use; the exhaustiveness checker
tells you which cases remain.  Types are not just documentation —
they are your co-programmer.

# Exercises
%%%
number := false
%%%

1. Use {tactic}`decide` to verify each claim.  For each, identify which type
   constructor(s) from the six-constructor table the proposition uses:
   1. {lean}`2 < 3 ∧ 3 < 4`
   2. {lean}`2 < 3 ∨ 3 < 2`
   3. {lean}`¬ (2 = 3)`
   4. {lean}`¬ (2 < 3 ∧ 3 < 2)`
   5. {lean}`(2 < 3 ∧ ¬(3 < 2)) ∨ (3 < 2 ∧ ¬(2 < 3))`

2. Explain in your own words why a function of type {lean}`α → Empty` certifies
   that {lean}`α` has no values.  Then write a term of type {lean}`False → Nat × Bool × String`
   and explain what it means in both the computational and logical readings.

3. Write `twice : (α → α) → α → α` that applies a function twice —
   `twice f x = f (f x)`.  Test it with `#eval`:
   ```
   #eval twice double 3        -- 12
   #eval twice negate false    -- false
   ```
   When `α` is a Prop, what does `twice` say logically?
   Write the type {lean}`(P → P) → P → P` in Lean and read it aloud.

4. Write `mapOption : (α → β) → Option α → Option β` using `match`.
   It should apply `f` to the wrapped value if `some`, return `none` otherwise.
   Test it:
   ```
   #eval mapOption double (some 5)     -- some 10
   #eval mapOption double none         -- none
   #eval mapOption negate (some true)  -- some false
   ```
   Which two type constructors from the six-constructor table does the
   type of `mapOption` use?

5. For each description, write the Lean type using only {ref "six-constructors"}[the six constructors].
   Write just the type — not a term inhabiting it.
   1. A person's name (String) paired with their score (Nat)
   2. A result that is either a computed Nat or an error String
   3. A function that takes any proof of `P ∧ Q` and returns a proof of `Q`
   4. Evidence that `¬ (2 + 2 = 5)`
   5. A value certifying that the type `Empty` is uninhabited
   Then use `decide` to verify (4).  What does Lean do to check it?
