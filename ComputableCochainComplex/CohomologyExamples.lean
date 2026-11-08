/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import ComputableCochainComplex.Cohomology

/-!
# Checks for certified cohomology

These initial examples check the kernel-coordinate bridge, including rectangular matrices,
boundary witnesses, zero-dimensional terms, and negative cohomological degrees.
They do not yet test a matrix-reduction backend.
-/

@[expose] public section

namespace ComputableCohomology.Examples

open CategoryTheory
open scoped Matrix

/-- A rectangular integer matrix whose kernel has the first and third standard basis vectors. -/
def rectangularKernel : KernelCertificate (!![0, 1, 0; 0, 2, 0] : Matrix (Fin 2) (Fin 3) ℤ) where
  size := 2
  inclusion := !![1, 0; 0, 0; 0, 1]
  retraction := !![1, 0, 0; 0, 0, 1]
  mul_inclusion := by decide
  retraction_mul_inclusion := by decide
  inclusion_retraction x hx := by
    have hx₁ : x 1 = 0 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using congrFun hx 0
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hx₁]

example : rectangularKernel.retraction *ᵥ ![6, 0, 5] = ![6, 5] := by decide

example : rectangularKernel.inclusion *ᵥ ![6, 5] = ![6, 0, 5] := by decide

example : ( !![2; 0; 0] : Matrix (Fin 3) (Fin 1) ℤ) *ᵥ ![3] = ![6, 0, 0] := by
  apply (rectangularKernel.boundary_preimage_iff !![2; 0; 0] (by decide)
    ![6, 0, 0] (by decide) ![3]).mp
  decide

example : ¬ ∃ y, ( !![2; 0; 0] : Matrix (Fin 3) (Fin 1) ℤ) *ᵥ y = ![0, 0, 1] := by
  rw [rectangularKernel.boundary_iff !![2; 0; 0] (by decide) ![0, 0, 1] (by decide)]
  rintro ⟨y, hy⟩
  have hW : rectangularKernel.retraction *
      ( !![2; 0; 0] : Matrix (Fin 3) (Fin 1) ℤ) = !![2; 0] := by decide
  rw [hW] at hy
  have : (0 : ℤ) = 1 := by
    simpa [rectangularKernel, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      using congrFun hy ⟨1, by decide⟩
  norm_num at this

/-- Empty coordinates certify the kernel in every degree of the zero complex. -/
def zeroKernel (R : Type*) [CommRing R] :
    KernelCertificate (0 : Matrix (Fin 0) (Fin 0) R) where
  size := 0
  inclusion := 0
  retraction := 0
  mul_inclusion := by simp
  retraction_mul_inclusion := Subsingleton.elim _ _
  inclusion_retraction _ _ := Subsingleton.elim _ _

example : Nonempty
    ((0 : FiniteFreeCochainComplex ℚ).toCochainComplex.homology (-3) ≅
      ModuleCat.of ℚ ((Fin 0 → ℚ) ⧸ LinearMap.range
        ((zeroKernel ℚ).retraction * (0 : FiniteFreeCochainComplex ℚ).incoming (-3)).mulVecLin)) :=
  ⟨(0 : FiniteFreeCochainComplex ℚ).cohomologyPresentationIso (-3) (zeroKernel ℚ)⟩

example : Nonempty
    ((0 : FiniteFreeCochainComplex (ZMod 2)).toCochainComplex.homology 4 ≅
      ModuleCat.of (ZMod 2) ((Fin 0 → ZMod 2) ⧸ LinearMap.range
        ((zeroKernel (ZMod 2)).retraction *
          (0 : FiniteFreeCochainComplex (ZMod 2)).incoming 4).mulVecLin)) :=
  ⟨(0 : FiniteFreeCochainComplex (ZMod 2)).cohomologyPresentationIso 4 (zeroKernel (ZMod 2))⟩

end ComputableCohomology.Examples
