# Notes

- BoundedCochainComplex requires exact support, i.e. for a finite set S every degree within S must be nonzero. Changed it to require bounded but not necessarily exact support.
- CMat_ needs to be extended with the operations for manipulating decompositions. i.e. reindexing a list of summands by a supplied permuatation, expressing a summand and its complement as a biproduct, constructing corresponding isomorphisms, and assembling/extracting block morphisms.
- A couple different levels of implementation:
    - Finite vector spaces over a computable field: you can split the chain into B^n, Z^n, and H^n. However, the simple chain 0 -> Z ->(2) Z -> 0 does not have a Z-basis for the homology, so it cannot be represented under this implementation.
    - Infinite graded vector spaces with decomposition into finite dimensional pieces, assuming differential respects grading: we can use the previous step to compute cohomology at each degree. Does not guarantee an algorithm that can produce the entire answer by computing over infinite degrees
- We will be computing over cochain complex with objects Hom(X, C^n). However, this may not be a vector space in general, rather it is over R-modules. Chat says that if we restrict R = F_2 then the Hom space is a field and we can proceed with calculations as described above.
- "X" in this case is an arbitrary fixed object.
