# Contributing

Thank you for contributing to the A∞-categories formalization. This project aims to upstream a
notable portion of its code to Mathlib, so we follow Mathlib's conventions from the start.
Some of the guidelines below may seem strict, but they will save us a lot of time later.
(Based on the advice of Niels Voss at the start of the project.)

The same rules, in a condensed form for AI coding agents, are in [`AGENTS.md`](AGENTS.md). If
you change a convention here, update that file as well.

Useful references:

* [Mathlib style guide](https://leanprover-community.github.io/contribute/style.html)
* [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html)
* [Mathlib documentation guidelines](https://leanprover-community.github.io/contribute/doc.html)

## Getting started

```bash
lake exe cache get   # download prebuilt Mathlib
lake build           # build all four libraries
```

The repository layout is described in [`README.md`](README.md). The blueprint, in
`blueprint/src/`, gives the mathematical roadmap. Before starting on a topic, look at the
relevant chapter to see what is planned and what already exists.

## Setup conventions

### The module system

Every file uses Lean's module system: it begins with the `module` keyword. The module system
speeds up compilation and gives us basic encapsulation. Mathlib uses it too. Keep in mind:

* Lean distinguishes public imports from private ones. Anything that appears in a theorem
  statement must be imported with `public import`, e.g. `public import Mathlib.Order.Basic`
  rather than `import Mathlib.Order.Basic`.
* Definitions and theorems are private by default. Either mark each one `public`, or put
  `public section` near the top of the file, as most files here do. Every definition that
  appears in the statement of a public theorem must itself come from a public import.
* A definition cannot be unfolded in another file unless it is marked `@[expose]`. Most files
  therefore use `@[expose] public section`.

### Root files

Mathlib has a file, `Mathlib.lean`, that imports every file in the library. Similarly, each of
our libraries has a root file (`Util.lean`, `ComputableCochainComplex.lean`, `AInfinity.lean`,
`KLRW.lean`) that imports every file in its folder. `lake build` builds these root files, so
they must import everything, or parts of the repository will silently go unchecked. Run
`lake exe mk_all` after adding, renaming or deleting a file. CI checks this with
`lake exe mk_all --check`.

### File headers

Start every file with the copyright header, then `module`, the imports and a `/-! ... -/` module
docstring. The files in `AInfinity/` are good examples.

## Coding standards

These are hard rules. Follow them as strictly as you can. Like the other rules in this section,
it is fine to break them temporarily while working, but finished code should follow them.

* **No warnings.** Code should produce no warnings or errors. The one exception is "declaration
  uses `sorry`" in work that is still in progress. If a linter warning really gets in the way,
  you may disable that linter locally, but do not just ignore warnings.
* **Naming conventions.** Names are hard to change later, so it is worth getting them right the
  first time. Mathlib mixes `lowerCamelCase`, `UpperCamelCase` and `snake_case`:
  * File and folder names use `UpperCamelCase`, e.g. `Mathlib/Computability/DFA.lean`. This is
    why our folder is called `AInfinity`, not `Ainfinity`.
  * Types, type families, propositions and typeclasses use `UpperCamelCase`, e.g. `Nat`,
    `LinearMap`, `Subsingleton`, `Nat.Prime`, `Continuous`, `IsCompact`. This applies when you
    *define* a proposition, not when you prove one.
  * All other definitions use `lowerCamelCase`, e.g. `Nat.add`, `LinearMap.adjoint`,
    `RingHom.ker`, `sInf`.
  * Theorems use `snake_case`, with the names of types and propositions written in
    `lowerCamelCase`. For example, `isClopen_compl_iff` states `IsClopen sᶜ ↔ IsClopen s`:
    `IsClopen` becomes `isClopen`, and the pieces are joined with underscores.
* **Line length.** Lines are at most 100 characters.
* **Multiple goals.** When a tactic such as `refine` or `by_cases` produces several goals,
  indent each subgoal with `·` (typed `\.`).
* **Spacing.** Put spaces around infix operators: write `3 + 4`, not `3+4`, and
  `(h : x < y)`, not `(h:x < y)`. Put a space before and after `:=`.
* **Indentation.** Do not indent the contents of `section` or `namespace` blocks. This matches
  Mathlib.
* **Implicit arguments.** Make an argument implicit if Lean can work it out from later
  arguments. For example, in
  ```lean
  theorem mul_div_cancel (m : ℕ) {n : ℕ} (H : 0 < n) : m * n / n = m := by ...
  ```
  Lean can work out `n` from the type of `H`, so `n` is implicit. Nothing later mentions `m`, so
  `m` is explicit. This rule has more exceptions than the others in this section.
* **Squeeze only non-terminal `simp`s.** Squeezing a `simp` means replacing it with the
  `simp only [...]` call that `simp?` suggests. Do this for every `simp` that does not close the
  goal: an unsqueezed non-terminal `simp` breaks whenever the simp set changes. Do not squeeze a
  `simp` that closes the goal. Those are robust as they are, and squeezing them only makes them
  brittle.
* **No new axioms.** Use only the three standard axioms, `Classical.choice`, `propext` and
  `Quot.sound`. Do not use `native_decide` or `bv_decide`, which depend on additional trust.
* **Docstrings.** Every definition needs a `/-- ... -/` docstring that explains the
  mathematical idea, and every file needs a `/-! ... -/` module docstring. Major theorems should
  have docstrings too.

## Heuristics

These are guidelines to follow as often as possible, but in the end you will have to use your
judgement.

### Names should be meaningful

Lemma names matter as much as definition names. Avoid arbitrary names like `part_1` or
`existence_theorem`. Do not put very generic names, like `sum` or `size`, in the root namespace.

### Definitions should be as general as possible

Mathlib makes definitions as general as it can. It works with semilinear maps between
semimodules rather than linear maps between vector spaces, with preorders rather than partial
orders whenever possible, and defines operations on metric spaces for extended metric spaces
whenever possible. Unlike Mathlib, we do not have time to jump through hoops for generality, but
we should take "free" generalizations whenever they come up. For example, use `Type*` instead of
`Type` whenever we can, and if a definition works for rings, define it for rings rather than
commutative rings.

Theorems may be much less general than definitions. We can define something for all rings and
then prove a major theorem that only holds for commutative rings.

### Definitions should be as incremental as possible

Break complex definitions into small, gradual steps, and split an algorithm into small
functions. If a definition takes more than a few lines of Lean, it should probably be split up.

### Be economical with definitions

Automation like `simp` cannot see through definitions (but it can see through abbreviations as an exception),
so every new definition makes our code harder for automation to work with. Do not add a definition
that will only appear in a few theorems. Use an abbreviation instead if you want one. Also avoid
definitions that are just special cases of other definitions. For example, Mathlib has no
separate definition of the Riemann integral, because it is a special case of the Bochner
integral. (Mathlib might define what it means for a function to be Riemann integrable, but it
will not add a second integral.)

The main reason new definitions cause trouble for automation is simp normal forms. Suppose
Mathlib defined `Real.tau := 2 * Real.pi`. Every lemma about `Real.pi` would then need a copy
for `Real.tau`, or working with `Real.tau` would be painful. We also want `simp` to move
expressions toward a canonical form, and having two ways to write the same thing gets in the way.

As a rough guide, each new type should come with about 20 lemmas and each new non-type
definition with about 5. These numbers are not precise, but they convey the idea.

In particular, do not add definitions just to save typing.

### Don't repeat yourself in theorems

In software engineering, the "don't repeat yourself" (DRY) principle says that when two
functions share similar code, the shared part should be factored into its own function. For the
reasons above, this applies to Lean definitions sometimes: factor out a common part of two
definitions only if we can prove lemmas about it.

For theorems, DRY always applies. If two proofs contain similar arguments, factor the shared part
into a separate lemma.

### Avoid forward reasoning in proofs; factor it into lemmas

Mathlib proofs mostly use:

* backward reasoning (`apply`, `induction`, `cases`, `congr`),
* symmetric reasoning (`rw`, `grw`, `symm`),
* automation that closes goals (`simp`, `aesop`, `grind`).

They rarely use long chains of forward reasoning with `have`. Forward reasoning is not wrong,
but if you find yourself writing many `have`s, consider splitting those steps into lemmas so
that the main proof is mostly backward reasoning.

As a rule of thumb, avoid `have` statements longer than 3 lines, and especially `have`
statements with `∀` quantifiers, which should almost always be their own lemmas. Also avoid
proofs nested more than about 3 levels deep: flat proofs are better than tree-shaped ones. A
single line of a natural-language proof should usually become one or more lemmas, not one
`have` in a Lean proof.

### Proofs should be short and easy to replace

This may sound strange, but proofs should be the least valuable part of a Lean file. The most
valuable parts are the definitions and the theorem statements. Avoid files that consist of a
single long proof. A single proof can take many (human) hours to write, but some of that time
should go into finding lemmas to factor out.

Keep proofs short enough that they could easily be rewritten from scratch. As a rule of thumb,
at least half of all proofs should be at most 5 lines, and very few should go past 30. (This is
for algebra. Analysis proofs tend to be a bit longer but are still almost always under 100
lines.) About a fifth of all proofs in Mathlib are a single line. There are three reasons:

* **Fragility.** When definitions move around in Mathlib or in our code, proofs break. The
  shorter a proof is, the easier it is to find the problem. In the worst case, the proof has to
  be rewritten from scratch.
* **A library of lemmas.** Most definitions should come with many lemmas. If a proof needs a
  fact about a definition, other proofs will probably need it soon too, so it might as well be a
  separate lemma.
* **Collaboration.** Several people cannot easily work on one long proof. Working on many small
  lemmas together is much easier.

### Fix downstream files when refactoring

When you rename or move declarations, fix everything downstream. At the very least, replace
broken proofs with `sorry` so the build does not fail. (Of course, final PRs into the master
branch should no longer contain `sorry`.)

## Keeping metadata in sync

* **Blueprint.** When you rename a declaration that a `\lean{...}` tag in
  `blueprint/src/chapters/` refers to, update the tag. When an item is fully formalized, mark it
  `\leanok`.
* **`formalization.yaml`.** After significant changes, update the scope, status and `sorry`
  counts. CI validates the file against the
  [formalization.yaml schema](https://github.com/mathlib-initiative/formalization.yaml).
* **`README.md`.** Keep the library table up to date.
