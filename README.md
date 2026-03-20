# CS1: Programming, Certified

A literate Lean 4 curriculum introducing typed functional programming through the lens of the Curry-Howard correspondence. Every file compiles cleanly against Lean 4 / Mathlib — no `sorry`, no `by`.

This fork of Kevin Sullivan's repository demonstrates the conversion of a 
part of the CS1 course to [Verso](https://verso.lean-lang.org). Only the 
first unit of the CS1 full course (weeks 0-3) are incorporated. 

Week 0 attempts a translation that uses a number of Verso's inline-code
display and math features, subsequent weeks are a more shallow/mechanical
translation and only use Verso features for top-level code.

## Building the document

These build commands will 

```
lake exe build-doc
python -m http.server --directory _out/html-multi
```