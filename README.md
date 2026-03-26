# CS1: Programming, Certified

A literate Lean 4 curriculum introducing typed functional programming through the lens of the Curry-Howard correspondence. Every file compiles cleanly against Lean 4 / Mathlib — no `sorry`, no `by`.

This fork of Kevin Sullivan's repository demonstrates the conversion of a 
part of the CS1 course to [Verso](https://verso.lean-lang.org). Only the
full-semester course, and not the Distillate, have been translated.

The translation isn't intended to be a fully-consistent work suitable for
classroom use. Week 0's translation uses a number of Verso's inline-code
display and math features, subsequent weeks are a more shallow/mechanical
translation and generally only use Verso features for top-level code.

## Building the document

These build commands will create the HTML site and allow it to be previewed
at http://localhost:8000/

```
lake exe build-doc
python -m http.server --directory _out/html-multi
```

The `.github/workflows/deploy_verso.yml` action puts the built verso document
at https://robsimmons.github.io/Lean4CS1/
