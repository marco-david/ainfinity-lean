# Cohomology implementation progress

## Design and baseline

- Read the updated roadmap, repository instructions, contribution guide, existing finite-free
  and based complexes, bounded complexes, and the one-black-strand model.
- The starting branch is `computable-cochain-complex`. The baseline `lake build` succeeds
  with the eight existing `sorry` warnings. No existing source changes were present.
- The pinned Mathlib provides `ShortComplex.moduleCatHomologyIso` for the kernel quotient.
  Its `Submodule.smithNormalForm` is noncomputable and cannot be the executable backend.
- Keep new Lean files directly in `ComputableCochainComplex/`, as requested.
- General quotient-defined KLRW integration must require certified finite graded coordinates
  over the actual solver coefficient ring. No polynomial specialization, normal-form theorem,
  independence theorem, or local-finiteness theorem is assumed.

## Shared certificate bridge (checked; no full milestone complete)

- `CohomologyKernel.lean` supplies `KernelCertificate`, executable `cyclesEquiv`, the equation
  `Z * (L * A) = A`, completeness of coordinate boundary equations with the same preimage,
  and `quotientEquiv` identifying the kernel quotient with the presentation `L * A`.
- `Cohomology.lean` connects the local certificate at any integer degree to Mathlib homology
  of `FiniteFreeCochainComplex.toCochainComplex`, and transports it through
  `BasedCochainComplex.coordinateIso`.
- Only comparisons with abstract Mathlib homology are noncomputable.
- Matrix reduction, field cohomology coordinates, induced maps, the integer backend, a
  proof-producing entry point, and graded adapters remain to be implemented.
- The two bridge modules build successfully. `lake env lean` also accepts
  `CohomologyExamples.lean`, including rectangular integer coordinates, a boundary preimage,
  a non-boundary, and zero-complex presentation isomorphisms over ℚ and `ZMod 2`.
  The explicit axiom audit of the equivalences, boundary-preimage theorem, and both homology
  transports reports only `propext`, `Classical.choice`, and `Quot.sound`.
- With the new files imported by the root, `lake build` succeeds (8335 jobs), with only the
  eight existing `sorry` warnings. `lake exe mk_all --module --check` also passes.

## Resolved: root-generation instructions disagreed with the module convention

- Following `AGENTS.md` and `CONTRIBUTING.md`, ran `lake exe mk_all` after adding the files.
  It removed `module` and changed `public import` to `import` in all four library roots.
- The pinned `.lake/packages/mathlib/scripts/mk_all.lean` requires `--module` to generate
  module-system roots. `.github/workflows/lean_action_ci.yml` also runs the check without
  that flag; `README.md` and the contribution instructions document the unflagged commands.
- Stopped and restored the roots; the user then approved correcting the commands and resuming.
- Commit `6938dd5` updates the documented commands and both CI workflows. The blueprint
  workflow uses the pinned action's supported `mk_all-args: "--module"` input.
- Regenerated the roots with `--module`; only the intended new imports changed.
