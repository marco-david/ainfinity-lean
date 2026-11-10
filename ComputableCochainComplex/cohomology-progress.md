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

## Shared certificate bridge (checked)

- `CohomologyKernel.lean` supplies `KernelCertificate`, executable `cyclesEquiv`, the equation
  `Z * (L * A) = A`, completeness of coordinate boundary equations with the same preimage,
  and `quotientEquiv` identifying the kernel quotient with the presentation `L * A`.
- `Cohomology.lean` connects the local certificate at any integer degree to Mathlib homology
  of `FiniteFreeCochainComplex.toCochainComplex`, and transports it through
  `BasedCochainComplex.coordinateIso`.
- Only comparisons with abstract Mathlib homology are noncomputable.
- The field layer below builds on this bridge. Induced maps, the integer backend, and graded
  adapters remain to be implemented.
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

## Field implementation

- `CohomologyReduction.lean` provides finite, decidable checks for kernel completeness over
  domains (`KernelData.Valid`) and free quotient coordinates (`SplitPresentationData.Valid`).
  A successful check constructs the existing `KernelCertificate` or a quotient equivalence.
- `CohomologyField.lean` supplies dimension-bounded exact Gaussian reduction, checked
  `computeField`, complete normalization, original-coordinate representatives, and
  `boundaryPreimage` returning an actual preimage together with its equation.
- `FreeCohomologyCertificate.size_eq` proves `h = b - rank(A) - rank(B)`. The local
  `homologyIso` and `FiniteFreeCochainComplex.fieldCohomologyIso` identify the result with
  Mathlib homology. `computeFieldCohomology` uses only the requested degree's two matrices.
- `certify_cohomology A, B` and `certify_cohomology C at n` are two forms of one small tactic.
  They prove explicit cohomology isomorphisms using `decide +kernel`, with a checked dimension
  cast. Ordinary `decide` gets stuck on the pinned rational implementation; kernel reduction
  succeeds and adds no native-evaluation axiom.
- Passing examples cover ℚ and `ZMod 2`, zero and identity maps, zero-dimensional terms,
  negative degrees, endpoints, support gaps, exact three-term data, rectangular non-exact
  three-term data, and invalid square-zero inputs. `rationalMiddle` normalizes `[3, 5, -8]`
  to `[5]`, represents it by `[-5, 5, 0]`, and computes boundary preimages.
- The generator's output is treated as untrusted until the finite checks pass. Failed checks
  return explicit errors; no claim follows from a bare evaluation of the generator.
- The field examples and full `lake build` pass (8337 jobs; only the eight pre-existing
  `sorry` warnings), and the root check passes. Axiom audits of the checker, calculator,
  boundary witnesses, rank formula, equivalences, and computed rational certificate report
  only `propext`, `Classical.choice`, and `Quot.sound`.

## Induced maps

- `CohomologyMap.lean` constructs the concrete kernel-quotient map of an existing short
  complex map and proves its agreement with Mathlib using `LeftHomologyMapData`.
  `KernelCertificate.presentationMap` transports it to the shared presentation coordinates.
- `FreeCohomologyCertificate.mapMatrix` is the executable product of normalization,
  cochain-map, and representative matrices. Its naturality, identity, and composition
  theorems follow from the comparison with Mathlib homology.
- `FiniteFreeCochainComplex.Hom.fieldCohomologyMatrix` accepts the original cochain map and
  a requested integer degree. Its naturality theorem compares with the original complexes.
- Examples now kernel-check a map acting by 2 on boundaries, 3 on cohomology, and 5 on
  outgoing coordinates; a change of middle basis inducing -1; and maps and composition at
  a negative degree of a gapped complex. All field examples compile.
- The basis-change fixture uses explicit identity matrices: categorical identities on two
  definitionally equal module objects caused excessive elaborator unfolding. This changes
  no mathematical data and avoids weakening or dropping the change-of-basis test.
- Full `lake build` passes (8338 jobs, only the eight pre-existing `sorry` warnings),
  `mk_all --module --check` passes, and `git diff --check` is clean. The map-comparison and
  composition axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.

## Integer backend (checked results; universal success unproved)

- Rechecked pinned Mathlib: its Smith normal form is noncomputable, and its record does not
  include the divisibility chain needed for normalized invariant factors.
- `CohomologySmith.lean` checks inverse coordinate matrices, both inclusions of relation
  modules, and a nonnegative divisibility-normalized diagonal. Its quotient equivalence,
  canonical representatives, and boundary preimages are proved for every checked certificate.
  `splitEquiv` separates unrestricted integer coordinates and nontrivial `ZMod` factors,
  omitting unit factors.
- `CohomologyIntegerReduction.lean` retains the shared matrix-operation data. It uses
  Euclidean row/column sweeps, corrects pivots that do not divide the remaining block, and
  normalizes signs. Recursion checks strictly decreasing pivot absolute value; there is no
  fuel parameter. Descent and final verification failures are explicit. Universal generator
  success has not been proved, and is not claimed by the API.
- `CohomologyInteger.lean` checks generated integral kernels and Smith presentations, then
  reuses the shared Mathlib comparison. Induced maps are transported through the quotient
  equivalence, hence respect torsion relations; naturality and composition compile.
- Initial kernel-checked examples pass: multiplication by 2, gcd/lcm normalization of
  `diag(4,6,0)` to factors `[2,12]` with one free coordinate, a nonzero outgoing differential,
  canonical representatives, positive and negative boundary preimages, and negative degree.
  Further explicit cyclic equivalences and torsion-map regressions are being checked.
- Further checks pass: explicit `ZMod 2` homology isomorphisms, multiplication by 3 on
  `ℤ/4` and its square, a saturated kernel of `[6,10,15]`, unit/negative pivots, empty
  degrees, gaps, and endpoints. `BasedCochainComplex.integerCohomologyIso` supplies the
  existing realization transport.
- Full `lake build` passes (8342 jobs, only the eight existing warnings), the module-root
  check passes, and the integer quotient, calculator, boundary, map, and homology-transport
  axiom audits contain only the three permitted axioms. No new proof placeholders exist.

## Graded adapter and KLRW boundary

- `CohomologyGraded.lean` restricts an existing Mathlib short complex using explicit
  homogeneous-preservation proofs, with the convention `M⟨s⟩_q = M_(q+s)`.
  `LocalCoordinates` evaluates its differentials on basis vectors, proves the matrix
  comparison, and transports computed cohomology and representatives to the original modules.
- `GradedHomCoordinates` requires actual homogeneous submodules, finite ordered linear
  equivalences, executable coordinate composition, and proof that decoding agrees with
  original composition. `CohomologyKLRWInput.lean` names this contract for the existing
  quotient-defined KLRW category and supplies no fabricated inhabitant. Normal forms,
  spanning/independence and finite graded pieces over the solver's ring remain upstream.
- `CohomologyOneBlackStrand.lean` proves degree additivity for the actual `compShift`,
  with minimal strand degree `|X-Y|` and dot degree two. It constructs executable bases
  for every homogeneous piece (zero or one coordinate), proves original composition
  compatibility, and verifies that the scalar differential is postcomposition by `r • id`.
- The one-black-strand source exposes its Hom groups as `DFinsupp`, but does not register
  their scalar module instance. The adapter registers the existing pointwise action; it
  does not alter the original category or use its unrelated `not_isZero` placeholder.
- `CohomologyGradedExamples.lean` kernel-checks a composition creating a dot, inadmissible
  degrees, the shift convention, and `T₀ --2·id--> T₀` in cohomological degree one and
  internal degree two. Its actual homogeneous-module homology is isomorphic to `ZMod 2`,
  and the nonzero class decodes to the one-dot diagram. A boundary witness is also checked.
- `LocalCoordinates.shortComplexIsoOfMatrices` and the two `...HomologyIsoOfMatrices`
  methods also accept executable matrices and compatibility proofs separately, so an
  abstract quotient category's noncomputable operations need not run inside the calculator.
- The full graded build passes; root checking and the axiom audit pass. In particular the
  one-dot representative theorem and the computed strand certificate use only the three
  permitted axioms, with no dependency on existing KLRW placeholders.
