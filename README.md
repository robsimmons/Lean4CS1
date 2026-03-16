# CS1: Programming, Certified

A 14-week literate Lean 4 curriculum introducing typed functional programming
through the lens of the Curry-Howard correspondence.  Every file compiles
cleanly against Lean 4 / Mathlib v4.28.0: no `sorry`, no `by`.

## Design commitments

**Students emerge fluent in computational and logical types, but proof
construction is not an assessment target.**

- Propositions are types from Week 1.
- `decide` is the primary proof producer for decidable propositions.
- All provided proofs are in term mode — `by` never appears.
- `sorry` never appears.
- Full Mathlib notations are used throughout.
- The logic progression (Bool/Prop → propositional → predicate → set/relation)
  is distributed across all 14 weeks.
- `Float`/`DecidableEq` and the IEEE 754 boundary appear in Week 7 as
  central course content.

## Course structure

| Unit | Weeks | Theme |
|------|-------|-------|
| 1 | 1–3 | Expressions, Functions, Recursion |
| 2 | 4–7 | Algebraic Datatypes, Lists, Trees, Decidability |
| 3 | 8–9 | Higher-Order Functions, Specifications |
| 4 | 10 | Sets and Relations |
| 5 | 11–12 | Abstract Types, Type Classes |
| 6 | 13–14 | Streams, Curry-Howard |

## Repository layout

```text
FPCourse/          Lean 4 source files (literate, /-! @@@ ... @@@ -/ blocks)
  Unit1/           Weeks 1–3
  Unit2/           Weeks 4–7
  Unit3/           Weeks 8–9
  Unit4/           Week 10
  Unit5/           Weeks 11–12
  Unit6/           Weeks 13–14
scripts/
  convert.hs       Literate Lean → Markdown (Haskell, primary)
  convert.py       Literate Lean → Markdown (Python, fallback)
src/
  SUMMARY.md       mdBook table of contents
  introduction.md  Course overview page
  FPCourse/        Generated Markdown (one .md per .lean file)
book.toml          mdBook configuration
Makefile           Build automation: make → convert + mdbook build
.github/workflows/
  mdbook.yml       CI/CD: convert, build, deploy to GitHub Pages
```

## Building the Lean sources

Requires Lean 4 and Lake.  The first build downloads Mathlib (~several GB)
and may take 30–60 minutes.

```bash
lake build
```

`Build completed successfully` means every proof in the curriculum compiles.

## Building the web book

Requires [mdBook](https://rust-lang.github.io/mdBook/) and its preprocessors
(`mdbook-toc`, `mdbook-mermaid`, `mdbook-image-size`).

**Convert Lean sources to Markdown** (uses `runhaskell` if available,
otherwise Python 3):

```bash
make convert        # FPCourse/**/*.lean → src/FPCourse/**/*.md
```

**Build and serve locally:**

```bash
make serve          # builds and serves at http://localhost:3000
```

**Full pipeline** (convert + build):

```bash
make                # or: make all
```

## Continuous deployment

Pushing to `main` triggers `.github/workflows/mdbook.yml`, which:

1. Installs GHC, mdBook, and preprocessors.
2. Runs `scripts/convert.hs` on every `.lean` file.
3. Builds the book with `mdbook build`.
4. Deploys the result to GitHub Pages.

## Literate format

Prose lives inside `/-! @@@ ... @@@ -/` comment blocks; everything else
is treated as Lean code.  The converter emits prose as-is and wraps code
in ` ```lean ``` ` fences.

```lean
/-! @@@
## Section heading

Explanation in **Markdown**.
@@@ -/

-- This becomes a ```lean code block.
def example : Nat := 42
```

## Assessment forms

Students are assessed on five competencies (no proof production required):

1. **Specification writing** — given a function and English description,
   write the correct Lean type expressing its specification.
2. **Specification reading** — given a Lean proposition, state in English
   what it asserts; give a satisfying and a falsifying example.
3. **Type inhabitation** — write a term the compiler accepts at a given type.
   The compiler is the primary grader.
4. **Counterexample finding** — given a function and an incorrect
   specification, find a concrete input that witnesses the mismatch.
5. **Decidability identification** — given a proposition, state whether
   `decide` closes it, which other term if not, and why.
