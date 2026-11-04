# Notes

- `HasExplicitZeroObject` stores a chosen object and its `IsZero` proof. Maps to and from it
  use the existing zero morphisms; explicit binary biproduct data remains separate.
- `BoundedCochainComplex.ofComplex` equips a cochain complex with a finite support bound;
  degrees inside the bound may be zero. Use `homMk` to lift maps of underlying complexes.
- CMat_ needs to be extended with the operations for manipulating decompositions. i.e. reindexing a list of summands by a supplied permuatation, expressing a summand and its complement as a biproduct, constructing corresponding isomorphisms, and assembling/extracting block morphisms.
- A couple different levels of implementation:
    - Finite vector spaces over a computable field: you can split the chain into B^n, Z^n, and H^n. However, the simple chain 0 -> Z ->(2) Z -> 0 does not have a Z-basis for the homology, so it cannot be represented under this implementation.
    - Infinite graded vector spaces with decomposition into finite dimensional pieces, assuming differential respects grading: we can use the previous step to compute cohomology at each degree. Does not guarantee an algorithm that can produce the entire answer by computing over infinite degrees
- We will be computing over cochain complex with objects Hom(X, C^n). However, this may not be a vector space in general, rather it is over R-modules. Chat says that if we restrict R = F_2 then the Hom space is a field and we can proceed with calculations as described above.
- "X" in this case is an arbitrary fixed object.
