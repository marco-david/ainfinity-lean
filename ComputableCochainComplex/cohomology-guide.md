# Certified cohomology: using the implementation

## Inputs and coefficient rings

Use the existing `FiniteFreeCochainComplex R`. Supply its degreewise sizes, finite support,
differential matrices (target rows, source columns), and square-zero proof. For a categorical
complex with an additive module realization, use `BasedCochainComplex.ofSupport` and
`toFiniteFree`; the existing `coordinateIso` retains the meaning of those coordinates.

A request at integer degree `n` uses only `C.incoming n` and `C.d n`, including at endpoints,
gaps, and negative degrees. Alternatively pass local matrices directly:

```lean
ComputableCohomology.computeField A B
ComputableCohomology.computeInteger A B
```

Here `A : Matrix (Fin b) (Fin a) R`, `B : Matrix (Fin c) (Fin b) R`, and the solver checks
`B * A = 0`. The field API requires `[Field R] [DecidableEq R]`, including exact rationals
and finite fields such as `ZMod 2`. The integral API uses `ℤ`. Polynomial rings are not
supported coefficient backends.

## Results, representatives, and proofs

For an existing complex call `C.computeFieldCohomology n` or `C.computeIntegerCohomology n`.
Both return `Except String` containing a certificate. A successful certificate proves the
entire cohomology presentation, not just independence of selected representatives.

For a certificate `result`:

- `result.normalize x` gives canonical coordinates for a cocycle `x`.
- `result.representative y` gives an original-coordinate cocycle representing `y`.
- `result.boundaryPreimage x hx` returns `some ⟨v, proof⟩` exactly when the cocycle is a
  boundary; `proof` states `A *ᵥ v = x`. Here `hx` proves `B *ᵥ x = 0`.
- `result.preimage x` by itself is the preimage of the *boundary part* removed by
  normalization. Use `boundaryPreimage` when a preimage of all of `x` is required.
- `result.homologyIso` identifies local Mathlib homology with the computed model.
  `C.fieldCohomologyIso n result` and `C.integerCohomologyIso n result` compare with the
  original finite-free complex.

Field models are `Fin result.size → R`, with the theorem
`FreeCohomologyCertificate.size_eq` proving `b - rank A - rank B`. Integer models separate
free coordinates from cyclic coordinates `ZMod d` with `d > 1`. They use the retained
finite diagonal indices; unit factors are omitted. `result.quotient.freeRank` and
`result.quotient.torsionFactors` give the free rank and positive divisibility-normalized
invariant factors. The quotient equivalence supplies the actual group/module description.

For a concrete field calculation, one tactic proves an explicit isomorphism:

```lean
example : Nonempty (C.toCochainComplex.homology n ≅ ModuleCat.of R (Fin h → R)) := by
  certify_cohomology C at n
```

`C`, `n`, and `h` must be concrete enough for kernel reduction. The local-matrix form is
`certify_cohomology A, B`. This tactic is field-only. For a concrete integer calculation,
extract the certificate with `(computeInteger A B).toOption.get (by decide +kernel)` and
use its isomorphism. `CohomologyIntegerExamples.lean` shows explicit isomorphisms to `ZMod 2`,
not only lists of factors. Computation uses `decide +kernel`; native evaluation is never a proof.

For based complexes, `data.integerCohomologyIso n result` transports the integer result.
For free models, compose `data.cohomologyPresentationIso n result.kernel` with
`(result.quotient.quotientEquiv _ result.valid).toModuleIso`.

## Induced maps

Given the original cochain map `f : C ⟶ D`, compute certificates `source` and `target` at
`n`. Then use:

```lean
f.fieldCohomologyMatrix n source target
f.integerCohomologyMap n source target
```

The first returns a matrix. The second returns an integer-linear map on the free/torsion
models; it respects the torsion relations. Both act by representing a class, applying
`f.f n`, and normalizing in the target. Their `..._naturality` theorems identify these maps
with `HomologicalComplex.homologyMap`; identity and composition follow from this comparison.
The examples include a nontrivial rational map, a change of basis, composition at a negative
degree, and multiplication by 3 on `ℤ/4`.

## A new graded adapter

Use the convention `M⟨s⟩_q = M_(q+s)`. Supply the actual homogeneous submodules and proofs
that the two local differentials carry the selected source pieces into the target pieces.
`restrictAtDegree` then forms an existing Mathlib `ShortComplex` on those submodules.
These proofs enforce internal degree zero after shifts; an inhomogeneous differential cannot
be admitted merely by truncating away its other components.

Supply `LocalCoordinates` on the three resulting modules: three finite ranks and executable
linear equivalences with the corresponding coordinate vectors. Its `incoming` and `outgoing`
matrices evaluate the original differentials on basis vectors. Pass these matrices to the
same field/integer solver. Use `freeHomologyIso` or `integerHomologyIso` to transport the
answer, and `freeRepresentative` or `integerRepresentative` to decode original cocycles.
Only the requested local pieces are required, without a global realization functor.

When ambient quotient operations are noncomputable, supply executable matrices separately
with proofs that their actions match those operations. `shortComplexIsoOfMatrices`,
`freeHomologyIsoOfMatrices`, and `integerHomologyIsoOfMatrices` provide the same comparison
without requiring the calculator to evaluate the ambient maps.

`GradedHomCoordinates` is an optional provider contract for a whole category: homogeneous
submodules, finite ordered linear coordinates, executable composition in coordinates, and
its decoding compatibility proof. `QuotientKLRWCoordinates` names this input for the existing
quotient-defined KLRW category. No inhabitant is assumed or fabricated. Its actual grading,
normal forms, spanning/independence, and local-finiteness proofs belong upstream.

A finite matrix over `ℤ[u,ℏ]` is **not** a finite integer matrix. The actual homogeneous
pieces must be proved finite free over the ring supplied to the solver. The implementation
performs no numerical specialization of polynomial coefficients.

`CohomologyOneBlackStrand.lean` is a complete small test adapter: minimal-strand degree
`|X-Y|`, dot degree 2, and zero/one-coordinate pieces. The acceptance examples prove that
`T₀ --2·id--> T₀` has `ZMod 2` cohomology at cohomological degree 1 and internal degree 2;
the nonzero class decodes to the one-dot diagram. They also check composition creating a
dot and the shift convention.

## Failure and coverage boundaries

Reduction candidates are untrusted until their finite equations pass. Invalid square-zero
inputs, a failed pivot-descent guard, or failed certificate verification return explicit
errors. Missing coordinate or homogeneity proofs prevent construction of the typed input.
An unsupported ring or exhausted elaborator/kernel resources makes the tactic fail.

The integer generator is total and uses checked decreasing absolute pivots, without a fuel
parameter. Every returned certificate has complete mathematical correctness. A theorem that
the generator succeeds for **every** finite integer matrix has not been established; no
blanket coverage claim is made. Kernel-checked examples cover nonunit pivots, mixed torsion
and free parts, saturated kernels, signs, empty dimensions, gaps, and induced torsion maps.
They also prove exhaustive checked reduction for all 81 two-by-two matrices with entries
in `{-1,0,1}`; this finite theorem is not a universal integer-success theorem.
