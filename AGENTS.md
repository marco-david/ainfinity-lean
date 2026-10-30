# AGENTS.md

Instructions for AI coding agents working in this repository. The reasoning behind these rules
is explained in [`CONTRIBUTING.md`](CONTRIBUTING.md), which is written for (human) contributors.

## Project overview

This is a Lean 4 / Mathlib formalization of A∞-category theory and KLRW categories and
computations at the intersection of these theories, developed at UC Berkeley.
The long-term goal is to upstream some of the code (notably the A∞-category theory) to Mathlib.
Nonetheless, we aim for all code to meet Mathlib's standards where possible.
The project is currently organized into four Lake libraries:

| Library | Contents |
| --- | --- |
| `Util/` | The `Texify` class and the `#texify` command for rendering terms and chain complexes as LaTeX. |
| `ComputableCochainComplex/` | Computable biproducts and zero objects, the additive completion `CMat_`, bounded cochain complexes. |
| `AInfinity/` | Grading types, graded linear maps, graded linear quivers, the Stasheff identities, A∞-categories, A∞-functors. |
| `KLRW/` | KLRW algebras and categories, the braiding functor, examples. |

Supporting files:

* `blueprint/src/` is the LaTeX blueprint. Its `\lean{...}` and `\leanok` tags refer to Lean
  declarations.
* `formalization.yaml` holds project metadata (scope, status, `sorry` counts). CI validates it.
* `README.md` describes the repository layout.

## Build and check

```bash
lake exe cache get        # download prebuilt Mathlib; run once after cloning or bumping Mathlib
lake build                # build all four libraries
lake exe mk_all           # regenerate the root files after adding, moving or deleting a file
lake exe mk_all --check   # what CI runs
lake env lean Path/To/File.lean   # check a single file
```

Work is finished only when `lake build` succeeds with no errors and no warnings. The one
allowed warning is "declaration uses `sorry`", and only where a `sorry` is permitted (see below).

## File layout

Each Lean file (other than the generated root files `Util.lean`,
`ComputableCochainComplex.lean`, `AInfinity.lean` and `KLRW.lean`) follows this layout:

```lean
/-
Copyright (c) 2026 Author Name. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Author Name
-/
module

public import Mathlib.Some.Specific.File
public import AInfinity.Grading

/-! # Title

Module docstring: what the file defines, the main results, and any notation or design choices.
-/

@[expose] public section

namespace ...

...

end ...
```

Each file should open an appropriate namespace, introducing meaningful layers of abstraction.

* **Module system.** Every file begins with `module`. Use `public import` for anything that
  appears in a public statement. Declarations are private by default, so wrap the file's
  content in `public section`, or `@[expose] public section` if other files need to unfold its
  definitions.
* **Imports.** Prefer specific Mathlib imports over `import Mathlib` in new files.
* **Root files.** After adding, renaming or deleting a file, run `lake exe mk_all`.
* **Namespaces.** Code in `AInfinity/` lives in `namespace AInfinityTheory`. Do not put generic
  names such as `sum` or `size` in the root namespace.
* Do not indent the contents of `namespace` or `section` blocks.

## Hard rules

### Correctness

* The code must be accepted by the kernel. Do not continue to later steps while the current
  tactic state has an error.
* Use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`. Never use
  `native_decide` or `bv_decide`, and never declare an `axiom`.
* Do not introduce `sorry` or `admit` unless asked for a proof skeleton. Two exceptions:
  existing `sorry`s in work-in-progress files (`KLRW/`, parts of `ComputableCochainComplex/`)
  are tolerated, and when a refactor breaks a downstream proof you cannot fix, replace that
  proof with `sorry` rather than leaving the build broken. Mention every new `sorry` in your
  summary.
* These exceptions apply only to work-in-progress branches. A PR into `master` must not
  contain any `sorry`.

### Naming

Follow Mathlib's
[naming conventions](https://leanprover-community.github.io/contribute/naming.html):

| Kind of declaration | Case | Examples |
| --- | --- | --- |
| Files and folders | `UpperCamelCase` | `AInfinity/GradedLinearQuiver.lean` |
| Types, structures, classes, type families, `Prop`-valued definitions | `UpperCamelCase` | `GradedLinearQuiver`, `IsCompact`, `Nat.Prime` |
| Other definitions (functions, terms, instances given by name) | `lowerCamelCase` | `LinearMap.adjoint`, `cbiprod` |
| Theorems and lemmas | `snake_case`, with type names written in `lowerCamelCase` | `isClopen_compl_iff`, `mul_div_cancel` |

Names must be meaningful. Names such as `part_1`, `aux_lemma` or `existence_theorem` are not
allowed. Choose names carefully, because they are expensive to change later.

### Style

* Lines are at most 100 characters.
* Put spaces around infix operators and around `:` and `:=`: write `3 + 4`, `(h : x < y)`,
  `f x := ...`.
* When a tactic (`refine`, `constructor`, `by_cases`, `rcases`, ...) creates several goals,
  focus each one with `·`.
* Make an argument implicit when later arguments determine it, e.g.
  `theorem mul_div_cancel (m : ℕ) {n : ℕ} (H : 0 < n) : m * n / n = m`.
* Use `Type*` rather than `Type` unless a fixed universe is required.
* **`simp`:** squeeze every *non-terminal* `simp` into `simp only [...]` (use `simp?`).
  A terminal `simp`, one that closes the goal, may stay unsqueezed.

### Documentation

* Every file has a `/-! ... -/` module docstring.
* Every definition, structure, class and instance given by name has a `/-- ... -/` docstring
  that explains the mathematical meaning, not just the Lean encoding.
* Major theorems have docstrings. Small `simp` or API lemmas may omit them.

## Design heuristics

These are strong defaults. Depart from them only for a concrete reason.

* **Reuse before you define.** Before writing a helper, search the workspace and Mathlib with
  `rg`, `exact?` and `apply?`. Build on the existing foundations, e.g. `GradingType`
  (`AInfinity/Grading.lean`), `GradedLinearMap` and `GradedMultilinearMap`
  (`AInfinity/GradedLinearAlgebra.lean`), `GradedLinearQuiver`, and the Stasheff sums in
  `AInfinity/Stasheff.lean`. Do not introduce an alternative foundational model unless asked.
* **Check signatures.** Read a declaration's actual type (`#check`, or open the source) before
  using it. Never guess.
* **Be economical with definitions.** Do not add a definition only to save typing (e.g.
  `abbrev Vec n := Fin n → ℝ`), and do not add a definition that is a special case of an
  existing one. As a rough guide, a new type should come with about 20 lemmas and a new
  non-type definition with about 5.
* **Keep definitions small and general.** Split long definitions into small steps. Take free
  generalizations, e.g. `Ring` instead of `CommRing` and `Semiring` instead of `Ring` when
  nothing else changes. Theorems may be less general than the definitions they concern.
* **In `ComputableCochainComplex/`, keep things computable.** Do not mark new declarations
  `noncomputable` without a reason.
* **Keep proofs short and flat.**
  * At least half of all proofs should be 5 lines or fewer, and almost none over 30.
  * Proofs should be mostly backward reasoning (`apply`, `refine`, `induction`, `cases`,
    `congr`), rewriting (`rw`, `grw`), and finishing automation (`simp`, `grind`, `aesop`,
    `omega`).
  * Keep `have` statements to 3 lines or fewer. Turn a `have` with a `∀`, or any reusable
    step, into its own lemma.
  * Avoid nesting deeper than about 3 levels.
  * If two proofs share an argument, extract it into a lemma.

## Keeping the project consistent

When you make changes, also:

* Fix all downstream uses after renaming or moving a declaration (see the `sorry` rule above).
* Update the `\lean{...}` tags in `blueprint/src/chapters/*.tex` when declarations they
  reference are renamed, and add `\leanok` when a blueprint item is fully formalized.
* Update `formalization.yaml` (scope, status, `sorry_count`, `sorry_in_definitions`) after
  significant changes.
* Update the library table in `README.md` when you add or remove a major component.

## Git

* Keep each commit focused, with a descriptive message.
* Do not commit build output (`.lake/`) or generated documentation.
