/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Certified algorithms for finite matrix modules

`Matrix.KernelGenerators` certifies a finite generating family for a matrix kernel.
`EffectiveModuleAlgorithms` supplies syzygies and witnessed lifting of known image members.
These are algorithmic hypotheses, not consequences of `CommRing`. Kernels need not be free
or split. This algebraic contract has no dependency on complexes or homology.
-/

@[expose] public section

open scoped Matrix

namespace Matrix

variable {R : Type*} [CommRing R] {b c : ℕ}

/-- A finite generating family for a matrix kernel. The range equality supplies both
soundness and completeness, without requiring independence or a splitting. -/
structure KernelGenerators (B : Matrix (Fin c) (Fin b) R) where
  /-- Number of generators, retained as finite coordinate data rather than an asserted rank. -/
  size : ℕ
  /-- Columns are kernel generators in the original ambient coordinates. -/
  generators : Matrix (Fin b) (Fin size) R
  /-- The image is exactly the kernel; checking only `B * generators = 0` would not suffice. -/
  range_eq_ker : LinearMap.range generators.mulVecLin = LinearMap.ker B.mulVecLin

end Matrix

/-- The two operations needed to construct cohomology presentations and induced maps.
Lifting is required only when existence is proved, so no decision of nonmembership or
normal-form algorithm is imposed on a backend. Both operations must be executable. -/
class EffectiveModuleAlgorithms (R : Type*) [CommRing R] where
  /-- Compute a complete finite generating family for a kernel. Applying this operation
  a second time to the generator matrix supplies all relations. -/
  syzygies {b c : ℕ} (B : Matrix (Fin c) (Fin b) R) : Matrix.KernelGenerators B
  /-- Lift a known member of a matrix image, returning its original source coordinates.
  The membership proof is erased at runtime; it is not itself an executable preimage. -/
  lift {a b : ℕ} (A : Matrix (Fin b) (Fin a) R) (x : Fin b → R)
    (hx : x ∈ LinearMap.range A.mulVecLin) : {y : Fin a → R // A *ᵥ y = x}

namespace Matrix.KernelGenerators

variable {R : Type*} [CommRing R] {b c : ℕ}

variable {B : Matrix (Fin c) (Fin b) R} (k : KernelGenerators B)

/-- Interpret generator coefficients as elements of the certified kernel.
The codomain restriction exposes exactness without involving complexes or homology. -/
def toKernel : (Fin k.size → R) →ₗ[R] LinearMap.ker B.mulVecLin :=
  k.generators.mulVecLin.codRestrict _ (fun x =>
    k.range_eq_ker ▸ (show k.generators *ᵥ x ∈ LinearMap.range k.generators.mulVecLin from
      ⟨x, rfl⟩))

/-- Lift a kernel element through the supplied known-member algorithm.
This choice of coefficients need not extend to a linear map on the ambient free module. -/
def lift [EffectiveModuleAlgorithms R] (x : LinearMap.ker B.mulVecLin) :
    {y : Fin k.size → R // k.generators *ᵥ y = x.val} :=
  EffectiveModuleAlgorithms.lift k.generators x.val (k.range_eq_ker.symm ▸ x.property)

end Matrix.KernelGenerators
