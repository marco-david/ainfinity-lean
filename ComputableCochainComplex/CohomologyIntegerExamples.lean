/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import ComputableCochainComplex.CohomologyInteger
public import ComputableCochainComplex.CohomologyExamples

/-! # Kernel-checked integral cohomology calculations

These examples exercise nonunit pivots, invariant-factor normalization, free summands,
canonical cocycles, and boundary witnesses in the original integer coordinates.
-/

@[expose] public section

namespace ComputableCohomology.Examples

open CategoryTheory
open scoped Matrix

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Integral cohomology of multiplication by two, at its target. -/
def integerTwo : IntegerCohomologyCertificate
    ( !![2] : Matrix (Fin 1) (Fin 1) ℤ) (0 : Matrix (Fin 0) (Fin 1) ℤ) :=
  (computeInteger _ _).toOption.get (by decide +kernel)

example : integerTwo.quotient.freeRank = 0 := by decide +kernel
example : integerTwo.quotient.torsionFactors = [2] := by decide +kernel
example : integerTwo.representative (integerTwo.normalize ![3]) = ![1] := by decide +kernel
example : (integerTwo.boundaryPreimage ![6] (by decide +kernel)).map (fun y => y.val 0) =
    some 3 := by decide +kernel
example : (integerTwo.boundaryPreimage ![1] (by decide +kernel)).isSome = false := by
  decide +kernel

/-- A diagonal presentation requiring gcd/lcm normalization and retaining a free summand. -/
def integerMixed : IntegerCohomologyCertificate
    ( !![4, 0; 0, 6; 0, 0] : Matrix (Fin 3) (Fin 2) ℤ)
    (0 : Matrix (Fin 0) (Fin 3) ℤ) :=
  (computeInteger _ _).toOption.get (by decide +kernel)

example : integerMixed.quotient.freeRank = 1 := by decide +kernel
example : integerMixed.quotient.torsionFactors = [2, 12] := by decide +kernel
example : (integerMixed.boundaryPreimage ![8, -12, 0] (by decide +kernel)).map
    Subtype.val = some ![2, -2] := by decide +kernel
example : (integerMixed.boundaryPreimage ![0, 0, 1] (by decide +kernel)).isSome = false := by
  decide +kernel

/-- Both differentials nonzero: the kernel must first be computed integrally. -/
def integerMiddle : IntegerCohomologyCertificate
    ( !![2; 0; -2] : Matrix (Fin 3) (Fin 1) ℤ) !![1, 1, 1; 2, 2, 2] :=
  (computeInteger _ _).toOption.get (by decide +kernel)

example : integerMiddle.quotient.freeRank = 1 := by decide +kernel
example : integerMiddle.quotient.torsionFactors = [2] := by decide +kernel
example : (integerMiddle.boundaryPreimage ![6, 0, -6] (by decide +kernel)).map
    (fun y => y.val 0) = some 3 := by decide +kernel

/-- The same torsion computation through the existing complex at a negative degree. -/
def integerNegative : IntegerCohomologyCertificate
    ((twoTerm ℤ 2 (-2)).incoming (-1)) ((twoTerm ℤ 2 (-2)).d (-1)) :=
  ((twoTerm ℤ 2 (-2)).computeIntegerCohomology (-1)).toOption.get (by decide +kernel)

example : integerNegative.quotient.torsionFactors = [2] := by decide +kernel

example : Nonempty ((twoTerm ℤ 2 (-2)).toCochainComplex.homology (-1) ≅
    ModuleCat.of ℤ integerNegative.Model) :=
  ⟨(twoTerm ℤ 2 (-2)).integerCohomologyIso (-1) integerNegative⟩

example : (computeInteger ( !![1] : Matrix (Fin 1) (Fin 1) ℤ) !![1]).toOption.isSome = false := by
  decide +kernel

/-- The computed model for multiplication by two is explicitly the usual `ZMod 2`. -/
def integerTwoEquiv : integerTwo.Model ≃ₗ[ℤ] ZMod 2 := by
  refine integerTwo.quotient.splitEquiv.symm.trans
    (show integerTwo.quotient.Coordinates ≃ₗ[ℤ] ZMod 2 from ?_)
  change (∀ i, ZMod (integerTwo.quotient.diagonal i)) ≃ₗ[ℤ] ZMod 2
  rw [show integerTwo.quotient.diagonal = fun _ => 2 from by decide +kernel]
  exact (LinearEquiv.funCongrLeft ℤ (ZMod 2) (finCongr (by decide +kernel))).trans
    (LinearEquiv.funUnique (Fin 1) ℤ (ZMod 2))

example : Nonempty ((KernelCertificate.shortComplex _ integerTwo.square_zero).homology ≅
    ModuleCat.of ℤ (ZMod 2)) :=
  ⟨integerTwo.homologyIso ≪≫ integerTwoEquiv.toModuleIso⟩

example : Nonempty ((twoTerm ℤ 2 (-2)).toCochainComplex.homology (-1) ≅
    ModuleCat.of ℤ (ZMod 2)) := by
  refine ⟨(twoTerm ℤ 2 (-2)).integerCohomologyIso (-1) integerNegative ≪≫
    (integerNegative.quotient.splitEquiv.symm.trans
      (show integerNegative.quotient.Coordinates ≃ₗ[ℤ] ZMod 2 from ?_)).toModuleIso⟩
  change (∀ i, ZMod (integerNegative.quotient.diagonal i)) ≃ₗ[ℤ] ZMod 2
  rw [show integerNegative.quotient.diagonal = fun _ => 2 from by decide +kernel]
  exact (LinearEquiv.funCongrLeft ℤ (ZMod 2) (finCongr (by decide +kernel))).trans
    (LinearEquiv.funUnique (Fin 1) ℤ (ZMod 2))

/-- A nontrivial torsion automorphism will act on this `ℤ/4` model. -/
def integerFour : IntegerCohomologyCertificate
    ((twoTerm ℤ 4).incoming 1) ((twoTerm ℤ 4).d 1) :=
  ((twoTerm ℤ 4).computeIntegerCohomology 1).toOption.get (by decide +kernel)

example : (scalarMap (twoTerm ℤ 4) 3).integerCohomologyMap 1 integerFour integerFour
    (integerFour.normalize ![1]) = integerFour.normalize ![3] := by decide +kernel

example : (scalarMap (twoTerm ℤ 4) 3 ≫ scalarMap (twoTerm ℤ 4) 3).integerCohomologyMap 1
    integerFour integerFour (integerFour.normalize ![1]) = integerFour.normalize ![1] := by
  decide +kernel

example : integerFour.normalize ![3] ≠ integerFour.normalize ![1] := by decide +kernel

/-- A nonunit outgoing row tests that the integral kernel is saturated. -/
def integerSaturated : IntegerCohomologyCertificate
    (0 : Matrix (Fin 3) (Fin 0) ℤ) ( !![6, 10, 15] : Matrix (Fin 1) (Fin 3) ℤ) :=
  (computeInteger _ _).toOption.get (by decide +kernel)

example : integerSaturated.quotient.freeRank = 2 := by decide +kernel
example : integerSaturated.quotient.torsionFactors = [] := by decide +kernel

example : (((gapped ℤ).computeIntegerCohomology 0).toOption.get
    (by decide +kernel)).quotient.freeRank = 0 := by decide +kernel

example : (((gapped ℤ).computeIntegerCohomology (-2)).toOption.get
    (by decide +kernel)).quotient.freeRank = 1 := by decide +kernel

example : (((twoTerm ℤ (-1)).computeIntegerCohomology 1).toOption.get
    (by decide +kernel)).quotient.torsionFactors = [] := by decide +kernel

example : (((twoTerm ℤ 2).computeIntegerCohomology 0).toOption.get
    (by decide +kernel)).quotient.freeRank = 0 := by decide +kernel

/-- Exhaustive checked coverage for all two-by-two matrices with entries in `{-1, 0, 1}`. -/
theorem small_integer_matrices_checked : ∀ i j k l : Fin 3,
    let M : Matrix (Fin 2) (Fin 2) ℤ :=
      !![(i.val : ℤ) - 1, (j.val : ℤ) - 1; (k.val : ℤ) - 1, (l.val : ℤ) - 1]
    (match integerReduce M with
    | .ok s => decide (s.kernelData.Valid M ∧ s.smithPresentationData.Valid M)
    | .error _ => false) = true := by
  decide +kernel

end ComputableCohomology.Examples
