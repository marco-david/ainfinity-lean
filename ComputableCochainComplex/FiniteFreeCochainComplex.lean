/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Finite free coordinates on ordinary cochain complexes

`FiniteFreeComplex C` supplies explicit finite coordinates on each term of
an existing module complex. It is independent of finite support: the complex may be unbounded.
`CochainComplex.dMatrix` expresses its differentials in these coordinates, with target rows
and source columns. `ofMatrices` and `homOfMatrices` construct ordinary Mathlib complexes
and cochain maps, reusing their category, additive structure, and shift functor.

The coordinate data imply Mathlib's `Module.Free` and `Module.Finite` properties termwise.
No assumption is made that kernels or cohomology are free, or that the ring is nonzero.
-/

@[expose] public section

open CategoryTheory
open scoped Matrix


/-- Chosen finite free coordinates on each term of an existing module complex.
This executable data imposes no support bound on the degrees of the complex. -/
class FiniteFreeComplex {R : Type*} [Ring R] (C : CochainComplex (ModuleCat R) ℤ) where
  /-- Number of coordinates in each degree, without any support restriction. -/
  size : ℤ → ℕ
  /-- The supplied linear equivalence with the finite coordinate module. -/
  coordinates : ∀ n, C.X n ≃ₗ[R] (Fin (size n) → R)

namespace CochainComplex

section Coordinates

variable {R : Type*} [Ring R] (C : CochainComplex (ModuleCat R) ℤ)
  [FiniteFreeComplex C]

/-- The number of supplied coordinates in a term of the complex. -/
abbrev size : ℤ → ℕ := FiniteFreeComplex.size C

/-- The chosen finite coordinates of a term of the complex. -/
abbrev coordinates (n : ℤ) : C.X n ≃ₗ[R] (Fin (C.size n) → R) :=
  FiniteFreeComplex.coordinates (C := C) n

/-- Chosen coordinates exhibit each term as a free module. -/
instance moduleFree (n : ℤ) : Module.Free R (C.X n) :=
  Module.Free.of_equiv (C.coordinates n).symm

/-- Each term is finitely generated because it has finitely many coordinates. -/
instance moduleFinite (n : ℤ) : Module.Finite R (C.X n) :=
  Module.Finite.equiv (C.coordinates n).symm

/-- Shifts transport the coordinate data independently of any support bound. -/
instance finiteFreeComplexShift (n : ℤ) :
    FiniteFreeComplex ((CochainComplex.shiftFunctor (ModuleCat R) n).obj C) where
  size i := C.size (i + n)
  coordinates i := C.coordinates (i + n)

end Coordinates

section Matrices

variable {R : Type*} [CommRing R]

/-- Express a differential of the original complex in the chosen finite coordinates. -/
def dMatrix (C : CochainComplex (ModuleCat R) ℤ) [FiniteFreeComplex C] (i j : ℤ) :
    Matrix (Fin (C.size j)) (Fin (C.size i)) R :=
  LinearMap.toMatrix' ((C.coordinates j).toLinearMap.comp
    ((C.d i j).hom.comp (C.coordinates i).symm.toLinearMap))

/-- Differential matrices act by converting to the module, applying its map, and converting back. -/
lemma dMatrix_mulVec (C : CochainComplex (ModuleCat R) ℤ) [FiniteFreeComplex C]
    (i j : ℤ) (x : Fin (C.size i) → R) :
    C.dMatrix i j *ᵥ x = C.coordinates j ((C.d i j).hom ((C.coordinates i).symm x)) :=
  LinearMap.toMatrix'_mulVec _ _

/-- The chosen coordinates commute with the differential matrix. -/
lemma dMatrix_coordinates (C : CochainComplex (ModuleCat R) ℤ) [FiniteFreeComplex C]
    (i j : ℤ) (x : C.X i) :
    C.dMatrix i j *ᵥ C.coordinates i x = C.coordinates j ((C.d i j).hom x) := by
  rw [dMatrix_mulVec, LinearEquiv.symm_apply_apply]

/-- Square-zero for coordinate matrices follows from the original complex differential. -/
lemma dMatrix_mul_dMatrix (C : CochainComplex (ModuleCat R) ℤ) [FiniteFreeComplex C]
    (i j k : ℤ) : C.dMatrix j k * C.dMatrix i j = 0 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [← Matrix.mulVec_mulVec, C.dMatrix_mulVec, C.dMatrix_mulVec,
    LinearEquiv.symm_apply_apply]
  have h := congrArg (fun f => f.hom ((C.coordinates i).symm x)) (C.d_comp_d i j k)
  change (C.d j k).hom ((C.d i j).hom ((C.coordinates i).symm x)) = 0 at h
  rw [h, map_zero, Matrix.zero_mulVec]

/-- Construct an ordinary complex from square-zero matrices, with no boundedness assumption.
The associated coordinate instance uses the identity equivalence in each degree. -/
def ofMatrices (size : ℤ → ℕ)
    (d : ∀ n, Matrix (Fin (size (n + 1))) (Fin (size n)) R)
    (hd : ∀ n, d (n + 1) * d n = 0) : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of R (Fin (size n) → R))
    (fun n => ModuleCat.ofHom (d n).mulVecLin) (fun n => by
      apply ModuleCat.hom_ext
      change (d (n + 1)).mulVecLin.comp (d n).mulVecLin = 0
      rw [← Matrix.mulVecLin_mul, hd, Matrix.mulVecLin_zero])

/-- Direct matrix input has the given coordinate counts and identity coordinates. -/
instance finiteFreeComplexOfMatrices (size : ℤ → ℕ)
    (d : ∀ n, Matrix (Fin (size (n + 1))) (Fin (size n)) R)
    (hd : ∀ n, d (n + 1) * d n = 0) : FiniteFreeComplex (ofMatrices size d hd) where
  size := size
  coordinates _ := LinearEquiv.refl R _

/-- Reading an adjacent differential from matrix input recovers the original matrix. -/
@[simp] lemma ofMatrices_dMatrix (size : ℤ → ℕ)
    (d : ∀ n, Matrix (Fin (size (n + 1))) (Fin (size n)) R)
    (hd : ∀ n, d (n + 1) * d n = 0) (n : ℤ) :
    (ofMatrices size d hd).dMatrix n (n + 1) = d n := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [dMatrix_mulVec]
  simp only [ofMatrices, CochainComplex.of_d]
  rfl

/-- Construct an ordinary cochain map from matrices commuting with the differentials.
Its components use the source and target coordinate equivalences. -/
def homOfMatrices {C D : CochainComplex (ModuleCat R) ℤ}
    [FiniteFreeComplex C] [FiniteFreeComplex D]
    (f : ∀ n, Matrix (Fin (D.size n)) (Fin (C.size n)) R)
    (comm : ∀ n, D.dMatrix n (n + 1) * f n = f (n + 1) * C.dMatrix n (n + 1)) : C ⟶ D where
  f n := ModuleCat.ofHom ((D.coordinates n).symm.toLinearMap.comp
    ((f n).mulVecLin.comp (C.coordinates n).toLinearMap))
  comm' i j hij := by
    have h : i + 1 = j := hij
    subst j
    apply ModuleCat.hom_ext
    ext x
    apply (D.coordinates (i + 1)).injective
    change D.coordinates (i + 1)
        ((D.d i (i + 1)).hom ((D.coordinates i).symm (f i *ᵥ C.coordinates i x))) =
      D.coordinates (i + 1) ((D.coordinates (i + 1)).symm
        (f (i + 1) *ᵥ C.coordinates (i + 1) ((C.d i (i + 1)).hom x)))
    rw [LinearEquiv.apply_symm_apply, ← D.dMatrix_mulVec, ← C.dMatrix_coordinates,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, comm]

end Matrices

end CochainComplex
