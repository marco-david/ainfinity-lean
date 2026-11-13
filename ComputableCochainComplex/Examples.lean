/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import ComputableCochainComplex.Cohomology
public import ComputableCochainComplex.BoundedCochainComplex
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Integral cohomology and a nonzero map on torsion

The two-term complexes `ℤ → ℤ`, with differentials multiplication by two and four, have
degree-one cohomology `ℤ / 2ℤ` and `ℤ / 4ℤ`. The cochain map given by the identity in degree
zero and multiplication by two in degree one induces the nonzero map `[x] ↦ [2x]`.

Explicit kernel, relation, and map certificates exercise the cohomology API over the actual
infinite ring `ℤ`, without enumerating or bounding its elements. Only the complexes' degree
support is bounded. This example uses the certificate API, not a general integer syzygy or
lifting backend, and is not imported by the cohomology implementation.

The final example puts `ℤ` in every degree with zero differentials. It has finite free
coordinates and certified cohomology in every degree, but admits no finite support bound.
-/

@[expose] public section

namespace ComputableCohomology.Examples

open CategoryTheory
open scoped Matrix

-- These explicit certificates unfold matrix dimensions and bundled module structures.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A two-term complex of free abelian groups, in degrees zero and one, with differential
multiplication by `r`. The integer coefficient is unrestricted. -/
def twoTerm (r : ℤ) : CochainComplex (ModuleCat ℤ) ℤ :=
  CochainComplex.ofMatrices
    (fun n => if n = 0 ∨ n = 1 then 1 else 0)
    (fun n => if n = 0 then fun _ _ => r else 0) (fun n => by
    by_cases hn : n = 0
    · subst n
      apply Matrix.ext
      intro i j
      exact Fin.elim0 i
    · simp only [ite_eq_right hn]
      exact Matrix.mul_zero _)

/-- The matrix constructor supplies coordinates independently of the support bound. -/
instance twoTermFiniteFreeComplex (r : ℤ) :
    FiniteFreeComplex (twoTerm r) := by
  unfold twoTerm
  infer_instance

/-- The same ordinary complex separately has support bounded by degrees zero and one. -/
instance twoTermBoundedComplex (r : ℤ) : BoundedComplex (twoTerm r) where
  support := {0, 1}
  isZero_of_notMem_support n hn := by
    rw [ModuleCat.isZero_iff_subsingleton]
    change Subsingleton (Fin (if n = 0 ∨ n = 1 then 1 else 0) → ℤ)
    rw [ite_eq_right (by simpa using hn)]
    infer_instance

@[simp] lemma twoTerm_dMatrix (r : ℤ) (n : ℤ) :
    (twoTerm r).dMatrix n (n + 1) = if n = 0 then Matrix.of (fun _ _ => r) else 0 := by
  unfold twoTerm twoTermFiniteFreeComplex
  exact CochainComplex.ofMatrices_dMatrix _ _ _ n

/-- In degree one every integer is a cocycle, its single generator has no intrinsic
relations, and the boundaries are the multiples of `r`. Thus the relation matrix is `[r]`.
Both kernel equalities certify completeness for all integers, not just tested values. -/
def presentation (r : ℤ) :
    CohomologyPresentation ((twoTerm r).incoming 1) ((twoTerm r).dMatrix 1 2) where
  kernel :=
    { size := 1
      generators := (1 : Matrix (Fin 1) (Fin 1) ℤ)
      range_eq_ker := by
        have hz : (twoTerm r).dMatrix 1 2 = 0 := by
          ext i j
          exact Fin.elim0 i
        rw [hz]
        change LinearMap.range (1 : Matrix (Fin 1) (Fin 1) ℤ).mulVecLin =
          LinearMap.ker (0 : Matrix (Fin 0) (Fin 1) ℤ).mulVecLin
        simp [Matrix.mulVecLin_one, Matrix.mulVecLin_zero] }
  relations :=
    { size := 0
      generators := 0
      range_eq_ker := by
        change LinearMap.range (0 : Matrix (Fin 1) (Fin 0) ℤ).mulVecLin =
          LinearMap.ker (1 : Matrix (Fin 1) (Fin 1) ℤ).mulVecLin
        simp [Matrix.mulVecLin_one, Matrix.mulVecLin_zero] }
  boundaries := fun _ _ => r
  generators_mul_boundaries := by
    change (1 : Matrix (Fin 1) (Fin 1) ℤ) * Matrix.of (fun (_ _ : Fin 1) => r) = _
    rw [Matrix.one_mul]
    change _ = (twoTerm r).dMatrix 0 (0 + 1)
    rw [twoTerm_dMatrix]
    rfl

/-- The degree-one cohomology presentation of the multiplication-by-two complex. -/
def source := presentation 2

/-- The degree-one cohomology presentation of the multiplication-by-four complex. -/
def target := presentation 4

/-- The identity in degree zero and multiplication by two in degree one intertwine the
differentials: `2 * 2 = 4 * 1`. On degree-one cohomology this includes `ℤ / 2ℤ` into `ℤ / 4ℤ`. -/
def inclusion : twoTerm 2 ⟶ twoTerm 4 :=
  CochainComplex.homOfMatrices
    (fun n => if n = 0 then fun _ _ => 1 else if n = 1 then fun _ _ => 2 else 0)
    (fun n => by
      by_cases hn : n = 0
      · subst n
        decide +kernel
      · simp only [twoTerm_dMatrix, ite_eq_right hn]
        calc
          _ = 0 := Matrix.zero_mul _
          _ = _ := (Matrix.mul_zero _).symm)

/-- The certified integer matrix for the induced map on cocycle generators. -/
def inducedMatrix : Matrix (Fin target.kernel.size) (Fin source.kernel.size) ℤ := !![2]

lemma generators_mul_inducedMatrix :
    target.kernel.generators * inducedMatrix =
      LinearMap.toMatrix' (inclusion.localMap 1).τ₂.hom * source.kernel.generators := by
  decide +kernel

/-- The executable map `[x] ↦ [2x]` on the presentation quotients, constructed without
an `EffectiveModuleAlgorithms ℤ` instance. -/
def inducedMap : source.PresentedModule →ₗ[ℤ] target.PresentedModule :=
  source.mapOfMatrix target (inclusion.localMap 1) inducedMatrix generators_mul_inducedMatrix

/-- The class of one generates the source's degree-one cohomology. -/
def generator : source.PresentedModule := Submodule.Quotient.mk ![1]

lemma inducedMap_generator :
    inducedMap generator = (Submodule.Quotient.mk ![2] : target.PresentedModule) := by
  change Submodule.Quotient.mk (inducedMatrix *ᵥ ![1]) = _
  apply congrArg Submodule.Quotient.mk
  decide +kernel

/-- The induced class is nonzero because the integer two is not a multiple of four. -/
lemma inducedMap_generator_ne_zero : inducedMap generator ≠ 0 := by
  rw [inducedMap_generator]
  intro hzero
  obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hzero
  change target.relationMatrix *ᵥ y = ![2] at hy
  rw [show target.relationMatrix = ( !![4] : Matrix (Fin 1) (Fin 1) ℤ) from by
    decide +kernel] at hy
  have h : 4 * y (0 : Fin 1) = (2 : ℤ) := by
    simpa only [Fin.sum_univ_one] using
      (show (∑ i : Fin 1, 4 * y i) = (2 : ℤ) from congrFun hy (0 : Fin 1))
  omega

/-- The source generator has order two; its image is therefore a nonzero torsion class. -/
lemma two_smul_generator : (2 : ℤ) • generator = 0 := by
  change (Submodule.Quotient.mk ((2 : ℤ) • ![1]) : source.PresentedModule) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨![1], by decide +kernel⟩

/-- The explicit induced map agrees with Mathlib's homology map on the local complexes. -/
lemma inducedMap_naturality :
    ShortComplex.homologyMap (inclusion.localMap 1) ≫
        (target.homologyIso ((twoTerm 4).d_mul_incoming 1)).hom =
      (source.homologyIso ((twoTerm 2).d_mul_incoming 1)).hom ≫
        ModuleCat.ofHom inducedMap :=
  source.mapOfMatrix_naturality target (inclusion.localMap 1)
    inducedMatrix generators_mul_inducedMatrix

/-- Check the integer presentations, the comparison with the original complexes' homology,
and a nonzero induced map from a torsion class, using only kernel-checked proofs. -/
example :
    source.relationMatrix = ( !![2] : Matrix (Fin 1) (Fin 1) ℤ) ∧
    target.relationMatrix = ( !![4] : Matrix (Fin 1) (Fin 1) ℤ) ∧
    Nonempty ((twoTerm 2).homology 1 ≅
      ModuleCat.of ℤ source.PresentedModule) ∧
    Nonempty ((twoTerm 4).homology 1 ≅
      ModuleCat.of ℤ target.PresentedModule) ∧
    (2 : ℤ) • generator = 0 ∧ inducedMap generator ≠ 0 := by
  exact ⟨by decide +kernel, by decide +kernel,
    ⟨(twoTerm 2).cohomologyPresentationIso 1 source⟩,
    ⟨(twoTerm 4).cohomologyPresentationIso 1 target⟩,
    two_smul_generator, inducedMap_generator_ne_zero⟩

/-- A copy of the integers in every degree, with zero differentials. -/
def unbounded : CochainComplex (ModuleCat ℤ) ℤ :=
  CochainComplex.ofMatrices (fun _ => 1) (fun _ => 0) (fun _ => Matrix.zero_mul _)

/-- Finite free terms do not require bounded degree support. -/
instance unboundedFiniteFreeComplex : FiniteFreeComplex unbounded := by
  unfold unbounded
  infer_instance

@[simp] lemma unbounded_dMatrix (n : ℤ) : unbounded.dMatrix n (n + 1) = 0 := by
  unfold unbounded unboundedFiniteFreeComplex
  exact CochainComplex.ofMatrices_dMatrix _ _ _ n

@[simp] lemma unbounded_incoming (n : ℤ) : unbounded.incoming n = 0 := by
  change unbounded.dMatrix (n - 1) n = 0
  convert unbounded_dMatrix (n - 1) using 1 <;> congr 1
  omega

/-- There is no finite support datum for a complex with a nonzero term in every degree. -/
lemma unbounded_not_boundedComplex : ¬ Nonempty (BoundedComplex unbounded) := by
  rintro ⟨h⟩
  let := h
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset (BoundedComplex.support unbounded)
  exact not_subsingleton (Fin 1 → ℤ) (ModuleCat.isZero_iff_subsingleton.mp
    (BoundedComplex.isZero_of_notMem_support (C := unbounded) n hn))

/-- The unbounded example has one cocycle generator and no nonzero relations in every degree. -/
def unboundedPresentation (n : ℤ) :
    CohomologyPresentation (unbounded.incoming n) (unbounded.dMatrix n (n + 1)) where
  kernel :=
    { size := 1
      generators := (1 : Matrix (Fin 1) (Fin 1) ℤ)
      range_eq_ker := by
        rw [unbounded_dMatrix]
        change LinearMap.range (1 : Matrix (Fin 1) (Fin 1) ℤ).mulVecLin =
          LinearMap.ker (0 : Matrix (Fin 1) (Fin 1) ℤ).mulVecLin
        simp [Matrix.mulVecLin_one, Matrix.mulVecLin_zero] }
  relations :=
    { size := 0
      generators := 0
      range_eq_ker := by
        change LinearMap.range (0 : Matrix (Fin 1) (Fin 0) ℤ).mulVecLin =
          LinearMap.ker (1 : Matrix (Fin 1) (Fin 1) ℤ).mulVecLin
        simp [Matrix.mulVecLin_one, Matrix.mulVecLin_zero] }
  boundaries := 0
  generators_mul_boundaries := by
    rw [unbounded_incoming]
    exact Matrix.mul_zero _

/-- The cohomology comparison applies in every degree despite the absence of finite support. -/
example (n : ℤ) :
    (unboundedPresentation n).relationMatrix = 0 ∧
    Nonempty (unbounded.homology n ≅ ModuleCat.of ℤ (unboundedPresentation n).PresentedModule) := by
  refine ⟨?_, ⟨unbounded.cohomologyPresentationIso n (unboundedPresentation n)⟩⟩
  change (Matrix.fromCols (0 : Matrix (Fin 1) (Fin 0) ℤ)
    (0 : Matrix (Fin 1) (Fin 1) ℤ)).submatrix id finSumFinEquiv.symm = 0
  simp

end ComputableCohomology.Examples
