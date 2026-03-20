import VersoManual

open Verso Doc
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
namespace Week04

#doc (Manual) "Week 4: Algebraic Datatypes" =>

# Sum types and product types
%%%
number := false
%%%

Lean's `inductive` keyword lets us define new types by listing their
_constructors_.  The resulting type is either a _sum_ (one of several
alternatives) or a _product_ (bundling several fields) — or both.

These are called _algebraic_ datatypes because they obey the same
algebraic laws as sums and products of numbers: a type with `n` values
of type A and `m` values of type B as alternatives has `n + m` values.

# Enumeration types (pure sums)

```lean
inductive Direction where
  | North | South | East | West
deriving Repr, DecidableEq

#eval Direction.North      -- Direction.North
example : Direction.North ≠ Direction.South := by decide
```

# Record types (pure products)

```lean
structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }
```

# Option: the prototypical proof-carrying type

`Option α` is either `none` (no value) or `some a` (a value `a : α`).
It is Lean's answer to null.

But notice: `Option.get` does not simply hope the value is present.
Its type _requires_ a proof:

```lean (name := optionget)
#check Option.get
```
```leanOutput optionget
Option.get.{u} {α : Type u} (o : Option α) : o.isSome = true → α
```

The caller must supply evidence before the function will run.
This is the proof-carrying pattern from {ref "week1"}[Week 1], now applied to a
realistic data type.

```lean
-- Option.get requires a proof.
def safeHead (xs : List α) (h : xs ≠ []) : α :=
  xs.head h

-- For concrete lists, `decide` produces the proof.
#eval safeHead [1, 2, 3] (by decide)    -- 1

-- Option.map: lift a function into an optional context
-- Specification: ∀ f o, (Option.map f o).isSome = o.isSome
theorem option_map_isSome (f : α → β) :
    ∀ o : Option α, (Option.map f o).isSome = o.isSome :=
  fun o => Option.recOn o rfl (fun _ => rfl)
```

# ∀ and ∃ in datatype specifications

When we define a new type, its specifications typically quantify over
all values of that type.  Here is the vocabulary:

:::table
*
 * Symbol
 * Reading
 * Introduction form
*
 * `∀ x : T, P x`
 * "for all x of type T, P holds of x"
 * supply a function `fun x => proof_of_P_x`
*
 * `∃ x : T, P x`
 * "there exists x of type T such that P holds"
 * `⟨witness, proof⟩`
:::

```lean
-- ∀ example: a property of all options
theorem none_map_always_none (f : α → β) :
    Option.map f none = none :=
  rfl

-- ∃ example: witness a specific value satisfying a property
example : ∃ n : Nat, n > 100 := ⟨101, by decide⟩

private def factorial' : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial' n

example : ∃ n : Nat, factorial' n > 1000 :=
  ⟨7, by decide⟩
```

# Recursive types: expressions

A _recursive_ inductive type refers to itself in its constructor
arguments.  This is how we build trees, lists, and other inductively
structured data.

```lean
inductive Expr where
  | num  : Int → Expr
  | add  : Expr → Expr → Expr
  | mul  : Expr → Expr → Expr
  | neg  : Expr → Expr
deriving Repr

-- Evaluation by structural recursion on Expr.
-- The function is named `eval` deliberately: it IS evaluation —
-- the process of reducing an expression tree to its integer value.
def Expr.eval : Expr → Int
  | .num n    => n
  | .add e₁ e₂ => e₁.eval + e₂.eval
  | .mul e₁ e₂ => e₁.eval * e₂.eval
  | .neg e    => -e.eval

-- Evaluation trace: Expr.eval (.add (.num 3) (.mul (.num 4) (.num 5)))
--   ↝ (.num 3).eval + (.mul (.num 4) (.num 5)).eval    -- add clause
--   ↝ 3 + (.mul (.num 4) (.num 5)).eval                -- num clause
--   ↝ 3 + ((.num 4).eval * (.num 5).eval)              -- mul clause
--   ↝ 3 + (4 * 5)                                      -- num clause ×2
--   ↝ 3 + 20 ↝ 23                                      -- arithmetic
#eval Expr.eval (.add (.num 3) (.mul (.num 4) (.num 5)))  -- 23

-- Specification: eval distributes over add.
-- Evaluation: (.add e₁ e₂).eval ↝ e₁.eval + e₂.eval by the add clause.
-- Both sides are definitionally equal, so rfl applies.
theorem eval_add (e₁ e₂ : Expr) :
    (Expr.add e₁ e₂).eval = e₁.eval + e₂.eval :=
  rfl
```

# The template principle

Every inductive type `T` has a corresponding _elimination principle_:
to define a function from `T`, provide one clause per constructor.
The types of the clauses are determined by the constructor signatures.

For `Expr`:
- A clause for `num n` — has access to `n : Int`
- A clause for `add e₁ e₂` — has access to both subexpressions and
  their recursively computed results
- A clause for `mul e₁ e₂` — same
- A clause for `neg e` — access to `e` and its result

This is the _template principle_: the type tells you the shape of the
function.

# Exercises
%%%
number := false
%%%

1. Define an inductive type `Shape` with constructors for
   `Circle` (radius : Float), `Rectangle` (width height : Float),
   and `Triangle` (base height : Float).

2. Define a function `area : Shape → Float`.

3. State (as a Prop) the specification: "the area of any circle with
   radius r equals `π * r * r`."  You may use `Float.pi` from Lean.
   (We will not prove this — Float lacks decidable equality.  But we
   can state it.)

4. Add a `sub : Expr → Expr → Expr` constructor and extend `eval`.
   State its specification as a ∀ proposition.

5. Use `∃` to state: "there exists an Expr that evaluates to 42."
   Prove it by providing a witness.
