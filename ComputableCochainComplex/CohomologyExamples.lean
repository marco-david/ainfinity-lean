/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import ComputableCochainComplex.CohomologyMap

/-!
# Checks for certified cohomology

Checks of the kernel-coordinate bridge and exact field reduction, including rectangular
matrices, boundary witnesses, zero-dimensional terms, and negative cohomological degrees.
All asserted answers are proved by kernel reduction, not by native evaluation.
-/

@[expose] public section

namespace ComputableCohomology.Examples

open CategoryTheory
open scoped Matrix

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

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

/-- Two rank-one terms in consecutive degrees, with scalar differential `r`. -/
def twoTerm (R : Type*) [CommRing R] (r : R) (start : ℤ := 0) :
    FiniteFreeCochainComplex R where
  size n := if n = start ∨ n = start + 1 then 1 else 0
  support := {start, start + 1}
  size_eq_zero_of_notMem_support n hn := by simpa using hn
  d n _ _ := if n = start then r else 0
  d_mul_d n := by
    by_cases hn : n = start
    · subst n
      have h : start + 1 ≠ start := by omega
      simp only [if_neg h]
      exact Matrix.zero_mul _
    · ext i j
      simp [Matrix.mul_apply, hn]

/-- A zero-differential complex with a gap in its support and a negative endpoint. -/
def gapped (R : Type*) [CommRing R] : FiniteFreeCochainComplex R where
  size n := if n = -2 ∨ n = 1 then 1 else 0
  support := {-2, 1}
  size_eq_zero_of_notMem_support n hn := by simpa using hn
  d _ := 0
  d_mul_d _ := by simp

example : Nonempty ((twoTerm ℚ 2).toCochainComplex.homology 1 ≅
    ModuleCat.of ℚ (Fin 0 → ℚ)) := by
  certify_cohomology (twoTerm ℚ 2) at 1

example : Nonempty ((twoTerm (ZMod 2) 2).toCochainComplex.homology 1 ≅
    ModuleCat.of (ZMod 2) (Fin 1 → ZMod 2)) := by
  certify_cohomology (twoTerm (ZMod 2) 2) at 1

example : Nonempty ((twoTerm ℚ 1).toCochainComplex.homology 0 ≅
    ModuleCat.of ℚ (Fin 0 → ℚ)) := by
  certify_cohomology (twoTerm ℚ 1) at 0

example : Nonempty ((twoTerm (ZMod 2) 1).toCochainComplex.homology 1 ≅
    ModuleCat.of (ZMod 2) (Fin 0 → ZMod 2)) := by
  certify_cohomology (twoTerm (ZMod 2) 1) at 1

example : Nonempty ((twoTerm ℚ 0).toCochainComplex.homology 0 ≅
    ModuleCat.of ℚ (Fin 1 → ℚ)) := by
  certify_cohomology (twoTerm ℚ 0) at 0

example : Nonempty ((gapped ℚ).toCochainComplex.homology (-2) ≅
    ModuleCat.of ℚ (Fin 1 → ℚ)) := by
  certify_cohomology (gapped ℚ) at (-2)

example : Nonempty ((gapped (ZMod 2)).toCochainComplex.homology 0 ≅
    ModuleCat.of (ZMod 2) (Fin 0 → ZMod 2)) := by
  certify_cohomology (gapped (ZMod 2)) at 0

example : Nonempty ((gapped ℚ).toCochainComplex.homology 5 ≅
    ModuleCat.of ℚ (Fin 0 → ℚ)) := by
  certify_cohomology (gapped ℚ) at 5

example : Nonempty ((twoTerm ℚ 2 (-2)).toCochainComplex.homology (-1) ≅
    ModuleCat.of ℚ (Fin 0 → ℚ)) := by
  certify_cohomology (twoTerm ℚ 2 (-2)) at (-1)

example : Nonempty
    ((KernelCertificate.shortComplex
      (!![1; -1] : Matrix (Fin 2) (Fin 1) ℚ)
      (B := !![1, 1]) (by decide +kernel)).homology ≅ ModuleCat.of ℚ (Fin 0 → ℚ)) := by
  certify_cohomology (!![1; -1] : Matrix (Fin 2) (Fin 1) ℚ), !![1, 1]

example : Nonempty
    ((KernelCertificate.shortComplex
      (!![1; -1] : Matrix (Fin 2) (Fin 1) (ZMod 2))
      (B := !![1, 1]) (by decide +kernel)).homology ≅
        ModuleCat.of (ZMod 2) (Fin 0 → ZMod 2)) := by
  certify_cohomology (!![1; -1] : Matrix (Fin 2) (Fin 1) (ZMod 2)), !![1, 1]

example : Nonempty
    ((KernelCertificate.shortComplex
      (!![1; 0; -1] : Matrix (Fin 3) (Fin 1) ℚ)
      (B := !![1, 0, 1; 2, 0, 2]) (by decide +kernel)).homology ≅
        ModuleCat.of ℚ (Fin 1 → ℚ)) := by
  certify_cohomology (!![1; 0; -1] : Matrix (Fin 3) (Fin 1) ℚ), !![1, 0, 1; 2, 0, 2]

example : Nonempty
    ((KernelCertificate.shortComplex
      (!![1; 0; -1] : Matrix (Fin 3) (Fin 1) (ZMod 2))
      (B := !![1, 0, 1; 2, 0, 2]) (by decide +kernel)).homology ≅
        ModuleCat.of (ZMod 2) (Fin 1 → ZMod 2)) := by
  certify_cohomology (!![1; 0; -1] : Matrix (Fin 3) (Fin 1) (ZMod 2)), !![1, 0, 1; 2, 0, 2]

/-- A computed rational model with a representative involving two original coordinates. -/
def rationalMiddle : FreeCohomologyCertificate
    (!![1; 0; -1] : Matrix (Fin 3) (Fin 1) ℚ) !![1, 1, 1; 2, 2, 2] :=
  (computeField _ _).toOption.get (by decide +kernel)

example : rationalMiddle.size = 1 := by decide +kernel

example : rationalMiddle.normalize ![3, 5, -8] = fun _ => 5 := by decide +kernel

example : rationalMiddle.representative (fun _ => 5) = ![-5, 5, 0] := by decide +kernel

example : rationalMiddle.preimage ![3, 5, -8] = ![8] := by decide +kernel

example : (rationalMiddle.boundaryPreimage ![3, 0, -3] (by decide +kernel)).map
    (fun y => y.val 0) = some 3 := by decide +kernel

example : (rationalMiddle.boundaryPreimage ![3, 5, -8] (by decide +kernel)).isSome = false := by
  decide +kernel

example : (computeField ( !![1] : Matrix (Fin 1) (Fin 1) ℚ) !![1]).toOption.isSome = false := by
  decide +kernel

/-- This map scales boundaries by two, cohomology by three, and outgoing coordinates by five. -/
def rationalMiddleMap : KernelCertificate.shortComplex _ rationalMiddle.square_zero ⟶
    KernelCertificate.shortComplex _ rationalMiddle.square_zero where
  τ₁ := ModuleCat.ofHom ( !![2] : Matrix (Fin 1) (Fin 1) ℚ).mulVecLin
  τ₂ := ModuleCat.ofHom ( !![5, 2, 3; 0, 3, 0; 0, 0, 2] :
    Matrix (Fin 3) (Fin 3) ℚ).mulVecLin
  τ₃ := ModuleCat.ofHom (5 • (1 : Matrix (Fin 2) (Fin 2) ℚ)).mulVecLin
  comm₁₂ := by
    apply ModuleCat.hom_ext
    change ( !![1; 0; -1] : Matrix (Fin 3) (Fin 1) ℚ).mulVecLin.comp
        ( !![2] : Matrix (Fin 1) (Fin 1) ℚ).mulVecLin =
      ( !![5, 2, 3; 0, 3, 0; 0, 0, 2] : Matrix (Fin 3) (Fin 3) ℚ).mulVecLin.comp
        ( !![1; 0; -1] : Matrix (Fin 3) (Fin 1) ℚ).mulVecLin
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul]
    congr 1
    decide +kernel
  comm₂₃ := by
    apply ModuleCat.hom_ext
    change ( !![1, 1, 1; 2, 2, 2] : Matrix (Fin 2) (Fin 3) ℚ).mulVecLin.comp
        ( !![5, 2, 3; 0, 3, 0; 0, 0, 2] : Matrix (Fin 3) (Fin 3) ℚ).mulVecLin =
      (5 • (1 : Matrix (Fin 2) (Fin 2) ℚ)).mulVecLin.comp
        ( !![1, 1, 1; 2, 2, 2] : Matrix (Fin 2) (Fin 3) ℚ).mulVecLin
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul]
    congr 1
    decide +kernel

example : rationalMiddle.mapMatrix rationalMiddle rationalMiddleMap = fun _ _ => 3 := by
  decide +kernel

/-- The same local complex after swapping the first two middle coordinates. -/
def rationalRebased : FreeCohomologyCertificate
    (!![0; 1; -1] : Matrix (Fin 3) (Fin 1) ℚ) !![1, 1, 1; 2, 2, 2] :=
  (computeField _ _).toOption.get (by decide +kernel)

/-- The coordinate swap is a map of the original local complexes. -/
def rationalBasisChangeMap : KernelCertificate.shortComplex _ rationalMiddle.square_zero ⟶
    KernelCertificate.shortComplex _ rationalRebased.square_zero where
  τ₁ := ModuleCat.ofHom (1 : Matrix (Fin 1) (Fin 1) ℚ).mulVecLin
  τ₂ := ModuleCat.ofHom ( !![0, 1, 0; 1, 0, 0; 0, 0, 1] :
    Matrix (Fin 3) (Fin 3) ℚ).mulVecLin
  τ₃ := ModuleCat.ofHom (1 : Matrix (Fin 2) (Fin 2) ℚ).mulVecLin
  comm₁₂ := by
    apply ModuleCat.hom_ext
    change ( !![0; 1; -1] : Matrix (Fin 3) (Fin 1) ℚ).mulVecLin.comp
        (1 : Matrix (Fin 1) (Fin 1) ℚ).mulVecLin =
      ( !![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℚ).mulVecLin.comp
        ( !![1; 0; -1] : Matrix (Fin 3) (Fin 1) ℚ).mulVecLin
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul]
    exact congrArg Matrix.mulVecLin (by decide +kernel)
  comm₂₃ := by
    apply ModuleCat.hom_ext
    change ( !![1, 1, 1; 2, 2, 2] : Matrix (Fin 2) (Fin 3) ℚ).mulVecLin.comp
        ( !![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℚ).mulVecLin =
      (1 : Matrix (Fin 2) (Fin 2) ℚ).mulVecLin.comp
        ( !![1, 1, 1; 2, 2, 2] : Matrix (Fin 2) (Fin 3) ℚ).mulVecLin
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul]
    exact congrArg Matrix.mulVecLin (by decide +kernel)

example : rationalMiddle.mapMatrix rationalRebased rationalBasisChangeMap = fun _ _ => -1 := by
  decide +kernel

/-- Scalar multiplication in every degree is an existing finite-free cochain map. -/
def scalarMap {R : Type*} [CommRing R] (C : FiniteFreeCochainComplex R) (r : R) : C ⟶ C where
  f _ := r • 1
  comm _ := by simp

/-- Computed cohomology at the negative endpoint of the gapped complex. -/
def gappedCohomology : FreeCohomologyCertificate
    ((gapped ℚ).incoming (-2)) ((gapped ℚ).d (-2)) :=
  ((gapped ℚ).computeFieldCohomology (-2)).toOption.get (by decide +kernel)

example : (scalarMap (gapped ℚ) 3).fieldCohomologyMatrix (-2)
    gappedCohomology gappedCohomology = fun _ _ => 3 := by decide +kernel

example : (scalarMap (gapped ℚ) 2 ≫ scalarMap (gapped ℚ) 3).fieldCohomologyMatrix (-2)
    gappedCohomology gappedCohomology = fun _ _ => 6 := by decide +kernel

end ComputableCohomology.Examples
