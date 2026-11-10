/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import ComputableCochainComplex.CohomologyGraded
public import KLRW.KLRWCategory

/-!
# Input contract for the quotient-defined KLRW category

This module names an input type and does not supply an inhabitant. The upstream KLRW work
must identify the actual homogeneous submodules and construct executable finite ordered
coordinates, proving spanning, independence, and composition compatibility. The local adapter
also accepts coordinates only for the three relevant terms, via `LocalCoordinates`.

The coefficient ring `R` here is the ring used by the solver. In particular, the ambient
KLRW algebra over `R[u,ℏ]` is not replaced by a numerical specialization. Even a finite
matrix over `ℤ[u,ℏ]` does not supply finite free integer coordinates: those must be proved
for the actual homogeneous pieces before using `computeInteger`.
-/

@[expose] public section

namespace ComputableCohomology

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Certified graded coordinates over the actual coefficient ring for the existing quotient
category. Normal forms, their correctness, and local finiteness are required upstream input. -/
abbrev QuotientKLRWCoordinates (R : Type*) [CommRing R] (parameters : KLRW.KLRWStructure V) :=
  GradedHomCoordinates R (KLRW.KLRWObject.WithRing R parameters)

end ComputableCohomology
