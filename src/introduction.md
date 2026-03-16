# CS1

**Author:** Kevin Sullivan

**Date:** April 15, 2026

Draft For Comment

---

A Certified Introduction to Programming

A 14-week literate Lean 4 curriculum for a first course in typed functional programming.
Every file in this course compiles cleanly against Lean 4 / Mathlib v4.28.0.

## Design Commitments

Students emerge fluent in computational and logical types.
Knowledge of proof construction is **not** an objective of this course.
The focus is instead on certified *computation*: writing functions,
stating their specifications as propositions, and verifying them.
Accordingly, except in particular cases, proof constructions are automated.

- Propositions are types from Week 1.
- `decide` produces proofs for decidable propositions.
- The logic progression (Bool/Prop → propositional → predicate → set/relation)
  is distributed across all 14 weeks.
- The `Float`/`DecidableEq` lesson appears in Week 7 as a central topic.

## Course Structure

| Unit | Weeks | Theme                                            |
| ---- | ----- | ------------------------------------------------ |
| 1    | 1–3   | Expressions, Functions, Recursion                |
| 2    | 4–7   | Algebraic Datatypes, Lists, Trees, Decidability  |
| 3    | 8–9   | Higher-Order Functions, Specifications           |
| 4    | 10    | Sets and Relations                               |
| 5    | 11–12 | Abstract Types, Type Classes                     |
| 6    | 13–14 | Streams, Curry-Howard                            |

## Assessment Forms

Students are assessed on five competencies:

1. **Specification writing**: given a function and English description,
   write the correct Lean type expressing its specification.
2. **Specification reading**: given a Lean proposition, state in English
   what it asserts; give a satisfying and falsifying example.
3. **Type inhabitation**: write a term the compiler accepts at a given type.
4. **Counterexample finding**: given a function and an incorrect
   specification, find a concrete input that witnesses the mismatch.
5. **Decidability identification**: given a proposition, state whether
   `decide` closes it, which other term if not, and why.

## Building

```bash
lake build        # compile the Lean sources
make convert      # convert .lean → .md
mdbook serve      # serve locally at http://localhost:3000
```
