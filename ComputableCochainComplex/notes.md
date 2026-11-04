# Notes

- `HasExplicitZeroObject` stores a chosen object and its `IsZero` proof. Maps to and from it
  use the existing zero morphisms; explicit binary biproduct data remains separate.
- `BoundedCochainComplex.ofComplex` equips a cochain complex with a finite support bound;
  degrees inside the bound may be zero. Use `homMk` to lift maps of underlying complexes.
- CMat_ needs to be extended with the operations for manipulating decompositions. i.e. reindexing a list of summands by a supplied permuatation, expressing a summand and its complement as a biproduct, constructing corresponding isomorphisms, and assembling/extracting block morphisms.
- `ComplexCoordinates R K` uses a commutative ring and supplied finite-free coordinates
  for the realized chain terms. `ofSupport` supplies zero coordinate counts outside the bound,
  including over the zero ring, and `coordinateIso` verifies the matrix interpretation.
- Kernels, images, and cohomology need not be free. The complex `ℤ → ℤ` with differential
  multiplication by `2` is representable even though its cokernel is `ℤ/2ℤ`.
  Computing cohomology requires additional ring-specific algorithms.
- For a fixed object `X`, the intended realization uses modules `Hom(X, C^n)` with supplied
  finite-free coordinates. Over a field these are vector spaces, not generally fields.
- Infinite graded modules can be treated degree by degree when the differential preserves
  grading and each graded piece has supplied finite-free coordinates. This does not give a
  finite algorithm for the entire infinite graded result.
