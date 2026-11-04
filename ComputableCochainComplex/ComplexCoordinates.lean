/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import ComputableCochainComplex.BoundedCochainComplex
public import ComputableCochainComplex.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Coordinates and matrices for categorical complexes

The input remains a bounded complex in `CMat_ C`. An additive realization and explicit
coordinates for this particular complex connect it to the independent matrix representation.
The coefficient ring is any commutative ring, including the zero ring. Finite free coordinates
are supplied for the chain terms; kernels, images, and cohomology need not be free.
`coordinateIso` identifies the realized complex with the matrix interpretation. This module
provides no rank or cohomology computation algorithms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Matrix

universe u v w

/-- Explicit finite free coordinates for one categorical complex after additive realization.
The matrices are supplied explicitly; their square-zero condition follows from compatibility. -/
structure ComplexCoordinates (R : Type u) [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C]
    (K : BoundedCochainComplex (CMat_ C)) where
  /-- The interpretation of categorical objects and maps as modules and linear maps. -/
  realization : CMat_ C ⥤ ModuleCat.{u} R
  /-- The realization preserves addition of morphisms. -/
  additive : realization.Additive
  /-- The number of supplied coordinates in each degree. -/
  size : ℤ → ℕ
  /-- Chosen coordinate counts vanish outside the supplied support bound.
  This is explicit because zero modules over the zero ring can have nonempty coordinates. -/
  size_eq_zero_of_notMem_support : ∀ n, n ∉ K.support → size n = 0
  /-- Explicit coordinates, rather than an existence assertion for a basis. -/
  coordinates : ∀ n, realization.obj (K.X n) ≃ₗ[R] (Fin (size n) → R)
  /-- Differential matrices, with target rows and source columns. -/
  differential : ∀ n, Matrix (Fin (size (n + 1))) (Fin (size n)) R
  /-- Applying the realized differential agrees with matrix multiplication. -/
  differential_apply : ∀ n x,
    coordinates (n + 1) ((realization.map (K.d n (n + 1))) x) =
      differential n *ᵥ coordinates n x

namespace ComplexCoordinates

variable {R : Type u} [CommRing R] {C : Type v} [Category.{w} C] [Preadditive C]
  {K : BoundedCochainComplex (CMat_ C)} (data : ComplexCoordinates R K)

attribute [instance] ComplexCoordinates.additive

/-- The realized bounded module complex, retaining the original support bound. -/
def realized : BoundedCochainComplex (ModuleCat.{u} R) :=
  BoundedCochainComplex.ofComplex
    ((data.realization.mapHomologicalComplex (.up ℤ)).obj K.toHomologicalComplex)
    (fun n hn => data.realization.map_isZero (K.isZero_of_notMem_support n hn))

/-- Matrix square-zero is inherited from the original categorical complex. -/
lemma differential_mul_differential (n : ℤ) :
    data.differential (n + 1) * data.differential n = 0 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  obtain ⟨y, rfl⟩ := (data.coordinates n).surjective x
  rw [← Matrix.mulVec_mulVec, ← data.differential_apply, ← data.differential_apply]
  have h := congrArg (fun f => data.realization.map f) (K.d_comp_d n (n + 1) (n + 1 + 1))
  dsimp only at h
  rw [data.realization.map_comp, data.realization.map_zero] at h
  rw [← ModuleCat.comp_apply, h]
  simp

/-- The existing finite-free representation, with square-zero derived from the input. -/
def toFiniteFree : FiniteFreeCochainComplex R where
  size := data.size
  support := K.support
  size_eq_zero_of_notMem_support := data.size_eq_zero_of_notMem_support
  d := data.differential
  d_mul_d := data.differential_mul_differential

@[simp] lemma toFiniteFree_support : data.toFiniteFree.support = K.support := rfl

/-- The chosen coordinates identify the realized complex with its matrix interpretation. -/
def coordinateIso : data.realized.toHomologicalComplex ≅ data.toFiniteFree.toCochainComplex :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (data.coordinates n).toModuleIso)
    (fun i j hij => by
      have h : i + 1 = j := hij
      subst j
      apply ModuleCat.hom_ext
      ext x
      change (data.toFiniteFree.toCochainComplex.d i (i + 1)).hom
          (data.coordinates i x) = _
      rw [FiniteFreeCochainComplex.toCochainComplex_d_apply]
      exact (data.differential_apply i x).symm)

section Support

variable (F : CMat_ C ⥤ ModuleCat.{u} R) [F.Additive]
  (r : {n // n ∈ K.support} → ℕ)
  (e : ∀ n : {n // n ∈ K.support}, F.obj (K.X n) ≃ₗ[R] (Fin (r n) → R))

/-- Extend coordinate counts by zero outside the supplied support. -/
def supportSize (n : ℤ) : ℕ := if hn : n ∈ K.support then r ⟨n, hn⟩ else 0

/-- Extend supplied coordinates using the unique maps between zero modules outside support. -/
def supportCoordinates (n : ℤ) :
    F.obj (K.X n) ≃ₗ[R] (Fin (supportSize r n) → R) := by
  by_cases hn : n ∈ K.support
  · have h : supportSize r n = r ⟨n, hn⟩ := dif_pos hn
    exact (e ⟨n, hn⟩).trans (LinearEquiv.funCongrLeft R R (finCongr h))
  · haveI : Subsingleton (F.obj (K.X n)) :=
      ModuleCat.isZero_iff_subsingleton.mp (F.map_isZero (K.isZero_of_notMem_support n hn))
    have h : supportSize r n = 0 := dif_neg hn
    haveI : IsEmpty (Fin (supportSize r n)) := ⟨fun i => Fin.elim0 (Fin.cast h i)⟩
    exact LinearEquiv.ofSubsingleton (R := R) (F.obj (K.X n)) _

variable
  (d : ∀ n (hn : n ∈ K.support) (hn' : n + 1 ∈ K.support),
    Matrix (Fin (r ⟨n + 1, hn'⟩)) (Fin (r ⟨n, hn⟩)) R)

/-- Extend the differentials by zero whenever either endpoint is outside support. -/
def supportDifferential (n : ℤ) :
    Matrix (Fin (supportSize r (n + 1))) (Fin (supportSize r n)) R :=
  if hn : n ∈ K.support then
    if hn' : n + 1 ∈ K.support then
      (d n hn hn').submatrix (finCongr (dif_pos hn')) (finCongr (dif_pos hn))
    else 0
  else 0

/-- Construct computational input from coordinates and matrices only on the finite support. -/
def ofSupport
    (hd : ∀ n (hn : n ∈ K.support) (hn' : n + 1 ∈ K.support) x,
      e ⟨n + 1, hn'⟩ ((F.map (K.d n (n + 1))) x) = d n hn hn' *ᵥ e ⟨n, hn⟩ x) :
    ComplexCoordinates R K where
  realization := F
  additive := inferInstance
  size := supportSize r
  size_eq_zero_of_notMem_support := fun _ hn => dif_neg hn
  coordinates := supportCoordinates F r e
  differential := supportDifferential r d
  differential_apply n x := by
    by_cases hn' : n + 1 ∈ K.support
    · by_cases hn : n ∈ K.support
      · simp only [supportCoordinates, supportDifferential, dif_pos hn, dif_pos hn',
          LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply]
        rw [hd n hn hn' x]
        erw [Matrix.submatrix_mulVec_equiv (d n hn hn') _ _
          (finCongr (show supportSize r n = r ⟨n, hn⟩ from dif_pos hn))]
        rfl
      · haveI : Subsingleton (F.obj (K.X n)) :=
          ModuleCat.isZero_iff_subsingleton.mp
            (F.map_isZero (K.isZero_of_notMem_support n hn))
        have hx : x = 0 := Subsingleton.elim _ _
        simp [supportDifferential, hn, hx]
    · haveI : IsEmpty (Fin (supportSize r (n + 1))) := by
        rw [supportSize, dif_neg hn']; infer_instance
      exact Subsingleton.elim _ _

end Support

/-- Explicit products give executable binary biproducts for the module realization. -/
abbrev moduleBiproducts (R : Type u) [CommRing R] :
    ComputableBinaryBiproduct (ModuleCat.{u} R) where
  computableBinaryBiproductData M N :=
    BinaryBiproductData.mkOfProduct M N (ModuleCat.of R (M × N))
      (ModuleCat.ofHom (LinearMap.fst R M N)) (ModuleCat.ofHom (LinearMap.snd R M N))
      (fun _ f g => ModuleCat.ofHom (f.hom.prod g.hom))
      (by intros; rfl) (by intros; rfl) (by intros; rfl)

/-- The zero-dimensional coordinate module is an explicit zero object. -/
abbrev moduleZero (R : Type u) [CommRing R] : HasExplicitZeroObject (ModuleCat.{u} R) where
  zero := ModuleCat.of R (Fin 0 → R)
  isZero := ModuleCat.isZero_of_subsingleton _

/-- Extend an additive module realization using the existing computable additive completion. -/
def extendRealization (F : C ⥤ ModuleCat.{u} R) [F.Additive] : CMat_ C ⥤ ModuleCat.{u} R :=
  letI := moduleBiproducts R
  letI := moduleZero R
  CMat_.extend F

instance (F : C ⥤ ModuleCat.{u} R) [F.Additive] : (extendRealization F).Additive := by
  unfold extendRealization
  infer_instance

end ComplexCoordinates
