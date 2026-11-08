/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Certified kernel coordinates

A `KernelCertificate B` supplies mutually inverse coordinates for the kernel of `B`.
It makes no assertion that kernels over arbitrary commutative rings are free: the caller
must provide the certificate. For consecutive matrices `A`, `B`, these coordinates identify
Mathlib's homology with the quotient by the image of `L * A`. All representative and
coordinate maps are executable; only the comparison with abstract homology is noncomputable.

Rows index targets and columns index sources, as in `FiniteFreeCochainComplex`.
-/

@[expose] public section

namespace ComputableCohomology

open CategoryTheory
open scoped Matrix

variable {R : Type*} [CommRing R] {a b c : ℕ}

/-- Finite free coordinates for the entire kernel of a matrix, with an executable retraction. -/
structure KernelCertificate (B : Matrix (Fin c) (Fin b) R) where
  /-- The number of kernel coordinates. -/
  size : ℕ
  /-- Columns are cocycles representing the coordinate basis. -/
  inclusion : Matrix (Fin b) (Fin size) R
  /-- Read the coordinates of a cocycle. Its values off the kernel are immaterial. -/
  retraction : Matrix (Fin size) (Fin b) R
  /-- Every represented vector is a cocycle. -/
  mul_inclusion : B * inclusion = 0
  /-- Reading the coordinates of a represented vector recovers that vector. -/
  retraction_mul_inclusion : retraction * inclusion = 1
  /-- Every cocycle is represented, not merely those in a chosen independent family. -/
  inclusion_retraction : ∀ x, B *ᵥ x = 0 → inclusion *ᵥ (retraction *ᵥ x) = x

namespace KernelCertificate

variable {B : Matrix (Fin c) (Fin b) R} (k : KernelCertificate B)

lemma inclusion_mem_ker (x : Fin k.size → R) : B *ᵥ (k.inclusion *ᵥ x) = 0 := by
  rw [Matrix.mulVec_mulVec, k.mul_inclusion, Matrix.zero_mulVec]

@[simp] lemma retraction_inclusion (x : Fin k.size → R) :
    k.retraction *ᵥ (k.inclusion *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, k.retraction_mul_inclusion, Matrix.one_mulVec]

/-- The certificate identifies coordinate vectors with all cocycles. -/
def cyclesEquiv : (Fin k.size → R) ≃ₗ[R] LinearMap.ker B.mulVecLin where
  toLinearMap := k.inclusion.mulVecLin.codRestrict _ k.inclusion_mem_ker
  invFun x := k.retraction *ᵥ x.val
  left_inv := k.retraction_inclusion
  right_inv x := Subtype.ext (k.inclusion_retraction x.val x.property)

@[simp] lemma cyclesEquiv_apply (x : Fin k.size → R) :
    (k.cyclesEquiv x).val = k.inclusion *ᵥ x := rfl

@[simp] lemma cyclesEquiv_symm_apply (x : LinearMap.ker B.mulVecLin) :
    k.cyclesEquiv.symm x = k.retraction *ᵥ x.val := rfl

variable (A : Matrix (Fin b) (Fin a) R) (hBA : B * A = 0)

include hBA in
/-- Boundary coordinates reconstruct the original incoming differential. -/
lemma inclusion_mul_retraction_mul : k.inclusion * (k.retraction * A) = A := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact k.inclusion_retraction _ (by rw [Matrix.mulVec_mulVec, hBA, Matrix.zero_mulVec])

include hBA in
/-- Solving the coordinate boundary equation gives the same preimage in the original complex. -/
lemma boundary_preimage_iff (x : Fin b → R) (hx : B *ᵥ x = 0) (y : Fin a → R) :
    (k.retraction * A) *ᵥ y = k.retraction *ᵥ x ↔ A *ᵥ y = x := by
  constructor
  · intro h
    calc
      A *ᵥ y = k.inclusion *ᵥ ((k.retraction * A) *ᵥ y) := by
        rw [Matrix.mulVec_mulVec, k.inclusion_mul_retraction_mul A hBA]
      _ = k.inclusion *ᵥ (k.retraction *ᵥ x) := congrArg _ h
      _ = x := k.inclusion_retraction x hx
  · intro h
    rw [← Matrix.mulVec_mulVec, h]

include hBA in
/-- The coordinate presentation detects every boundary. -/
lemma boundary_iff (x : Fin b → R) (hx : B *ᵥ x = 0) :
    (∃ y, A *ᵥ y = x) ↔ ∃ y, (k.retraction * A) *ᵥ y = k.retraction *ᵥ x :=
  exists_congr fun y => (k.boundary_preimage_iff A hBA x hx y).symm

/-- The local matrix data regarded as Mathlib's existing short complex of modules. -/
def shortComplex : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk A.mulVecLin B.mulVecLin
    (by rw [← Matrix.mulVecLin_mul, hBA, Matrix.mulVecLin_zero])

lemma cyclesEquiv_symm_boundary (x : Fin a → R) :
    k.cyclesEquiv.symm ((shortComplex A hBA).moduleCatToCycles x) =
      (k.retraction * A) *ᵥ x := by
  change k.retraction *ᵥ (A *ᵥ x) = (k.retraction * A) *ᵥ x
  exact Matrix.mulVec_mulVec _ _ _

lemma map_boundary_range :
    (LinearMap.range (shortComplex A hBA).moduleCatToCycles).map
        k.cyclesEquiv.symm.toLinearMap = LinearMap.range (k.retraction * A).mulVecLin := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, (k.cyclesEquiv_symm_boundary A hBA z).symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨_, ⟨z, rfl⟩, k.cyclesEquiv_symm_boundary A hBA z⟩

/-- Kernel coordinates carry the boundary quotient to the presentation matrix `L * A`. -/
def quotientEquiv :
    (LinearMap.ker B.mulVecLin ⧸ LinearMap.range (shortComplex A hBA).moduleCatToCycles) ≃ₗ[R]
      ((Fin k.size → R) ⧸ LinearMap.range (k.retraction * A).mulVecLin) :=
  Submodule.Quotient.equiv _ _ k.cyclesEquiv.symm (k.map_boundary_range A hBA)

@[simp] lemma quotientEquiv_mk (x : LinearMap.ker B.mulVecLin) :
    k.quotientEquiv A hBA (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (k.retraction *ᵥ x.val) := rfl

@[simp] lemma quotientEquiv_symm_mk (x : Fin k.size → R) :
    (k.quotientEquiv A hBA).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (k.cyclesEquiv x) := rfl

/-- The computed presentation is the homology of the original short complex.
Noncomputability is confined to Mathlib's choice of abstract homology objects. -/
noncomputable def homologyIso :
    (shortComplex A hBA).homology ≅
      ModuleCat.of R ((Fin k.size → R) ⧸ LinearMap.range (k.retraction * A).mulVecLin) :=
  (shortComplex A hBA).moduleCatHomologyIso ≪≫ (k.quotientEquiv A hBA).toModuleIso

end KernelCertificate

end ComputableCohomology
