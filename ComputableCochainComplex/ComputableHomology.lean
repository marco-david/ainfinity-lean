/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import ComputableCochainComplex.BoundedCochainComplex
public import ComputableCochainComplex.Finite
public import ComputableCochainComplex.MatrixHomology
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!+# Coordinates for realized categorical complexes

The input remains a bounded complex in `CMat_ C`. An additive realization and explicit
coordinates for this particular complex connect it to the independent matrix representation.
All cohomology statements concern the realized module complex, not the category `CMat_ C`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Matrix

universe u v w

/-- Additional finite coordinates for one categorical complex after additive realization.
The matrices are supplied explicitly; their square-zero condition follows from compatibility. -/
structure ComputableCohomologyData (k : Type u) [Field k]
    {C : Type v} [Category.{w} C] [Preadditive C]
    (K : BoundedCochainComplex (CMat_ C)) where
  /-- The module-valued interpretation whose cohomology is to be computed. -/
  realization : CMat_ C ⥤ ModuleCat.{u} k
  /-- The realization preserves addition of morphisms. -/
  additive : realization.Additive
  /-- The number of supplied coordinates in each degree. -/
  size : ℤ → ℕ
  /-- Explicit coordinates, rather than an existence assertion for a basis. -/
  coordinates : ∀ n, realization.obj (K.X n) ≃ₗ[k] (Fin (size n) → k)
  /-- Differential matrices, with target rows and source columns. -/
  differential : ∀ n, Matrix (Fin (size (n + 1))) (Fin (size n)) k
  /-- Applying the realized differential agrees with matrix multiplication. -/
  differential_apply : ∀ n x,
    coordinates (n + 1) ((realization.map (K.d n (n + 1))) x) =
      differential n *ᵥ coordinates n x

namespace ComputableCohomologyData

variable {k : Type u} [Field k] {C : Type v} [Category.{w} C] [Preadditive C]
  {K : BoundedCochainComplex (CMat_ C)} (data : ComputableCohomologyData k K)

attribute [instance] ComputableCohomologyData.additive

/-- The realized bounded module complex, retaining the original support bound. -/
def realized : BoundedCochainComplex (ModuleCat.{u} k) :=
  BoundedCochainComplex.mkOfBounded
    ((data.realization.mapHomologicalComplex (.up ℤ)).obj K.toHomologicalComplex)
    (fun n hn => data.realization.map_isZero (K.isZero_of_notMem_support n hn))

/-- Coordinates outside the categorical support are necessarily empty. -/
lemma size_eq_zero_of_notMem_support (n : ℤ) (hn : n ∉ K.support) : data.size n = 0 := by
  haveI : Subsingleton (data.realization.obj (K.X n)) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (data.realization.map_isZero (K.isZero_of_notMem_support n hn))
  haveI : Subsingleton (Fin (data.size n) → k) :=
    data.coordinates n |>.symm.injective.subsingleton
  by_contra h
  have i : Fin (data.size n) := ⟨0, Nat.pos_of_ne_zero h⟩
  exact zero_ne_one (congrFun (Subsingleton.elim (0 : Fin (data.size n) → k) 1) i)

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
def toFiniteFree : FiniteFreeCochainComplex k where
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

section Dimensions

variable [DecidableEq k]

/-- Compute cohomology dimension in any specified degree by automatic exact rank calculation. -/
def computeCohomologyDimension (n : ℤ) : ℕ :=
  data.size n - MatrixHomology.computeRank (data.differential (n - 1)) -
    MatrixHomology.computeRank (data.differential n)

/-- Compute precisely the degrees in the original finite bound, in ascending order. -/
def computeAllCohomologyDimensions : List (ℤ × ℕ) :=
  (K.support.sort (· ≤ ·)).map fun n => (n, data.computeCohomologyDimension n)

@[simp] lemma computeAllCohomologyDimensions_degrees :
    data.computeAllCohomologyDimensions.map Prod.fst = K.support.sort (· ≤ ·) := by
  simp [computeAllCohomologyDimensions, Function.comp_def]

/-- Degrees outside the stored support have zero cohomology dimension. -/
lemma computeCohomologyDimension_eq_zero (n : ℤ) (hn : n ∉ K.support) :
    data.computeCohomologyDimension n = 0 := by
  simp [computeCohomologyDimension, data.size_eq_zero_of_notMem_support n hn]

omit [DecidableEq k] in
private lemma finrank_range_coordinate_d (n j : ℤ) (hj : n + 1 = j) :
    Module.finrank k (LinearMap.range
      (data.toFiniteFree.toCochainComplex.d n j).hom) = (data.differential n).rank := by
  subst j
  rw [FiniteFreeCochainComplex.toCochainComplex_d]
  rfl

/-- The executable answer agrees with the homology of the realized categorical complex. -/
theorem computeCohomologyDimension_eq_finrank (n : ℤ) :
    data.computeCohomologyDimension n =
      Module.finrank k (data.realized.toHomologicalComplex.homology n) := by
  let Q := data.toFiniteFree.toCochainComplex
  let e := (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℤ) n).mapIso data.coordinateIso
  have he : Module.finrank k (data.realized.homology n) = Module.finrank k (Q.homology n) :=
    e.toLinearEquiv.finrank_eq
  rw [he]
  have hs := Q.homologyIsoSc' (n - 1) n (n + 1) (by simp) (by simp)
  rw [hs.toLinearEquiv.finrank_eq]
  haveI : FiniteDimensional k (Q.sc' (n - 1) n (n + 1)).X₂ :=
    inferInstanceAs (FiniteDimensional k (Fin (data.size n) → k))
  rw [MatrixHomology.finrank_homology]
  change data.computeCohomologyDimension n = Module.finrank k (Fin (data.size n) → k) -
    Module.finrank k (LinearMap.range (Q.d (n - 1) n).hom) -
    Module.finrank k (LinearMap.range (Q.d n (n + 1)).hom)
  rw [Module.finrank_fin_fun, data.finrank_range_coordinate_d (n - 1) n (by omega),
    data.finrank_range_coordinate_d n (n + 1) rfl]
  simp only [computeCohomologyDimension, MatrixHomology.computeRank_eq_rank]

end Dimensions

section Support

variable (F : CMat_ C ⥤ ModuleCat.{u} k) [F.Additive]
  (r : {n // n ∈ K.support} → ℕ)
  (e : ∀ n : {n // n ∈ K.support}, F.obj (K.X n) ≃ₗ[k] (Fin (r n) → k))

/-- Extend coordinate counts by zero outside the supplied support. -/
def supportSize (n : ℤ) : ℕ := if hn : n ∈ K.support then r ⟨n, hn⟩ else 0

/-- Extend supplied coordinates using the unique maps between zero modules outside support. -/
def supportCoordinates (n : ℤ) :
    F.obj (K.X n) ≃ₗ[k] (Fin (supportSize r n) → k) := by
  by_cases hn : n ∈ K.support
  · have h : supportSize r n = r ⟨n, hn⟩ := dif_pos hn
    exact (e ⟨n, hn⟩).trans (LinearEquiv.funCongrLeft k k (finCongr h))
  · haveI : Subsingleton (F.obj (K.X n)) :=
      ModuleCat.isZero_iff_subsingleton.mp (F.map_isZero (K.isZero_of_notMem_support n hn))
    have h : supportSize r n = 0 := dif_neg hn
    haveI : IsEmpty (Fin (supportSize r n)) := ⟨fun i => Fin.elim0 (Fin.cast h i)⟩
    exact LinearEquiv.ofSubsingleton (R := k) (F.obj (K.X n)) _

variable
  (d : ∀ n (hn : n ∈ K.support) (hn' : n + 1 ∈ K.support),
    Matrix (Fin (r ⟨n + 1, hn'⟩)) (Fin (r ⟨n, hn⟩)) k)

/-- Extend the differentials by zero whenever either endpoint is outside support. -/
def supportDifferential (n : ℤ) :
    Matrix (Fin (supportSize r (n + 1))) (Fin (supportSize r n)) k :=
  if hn : n ∈ K.support then
    if hn' : n + 1 ∈ K.support then
      (d n hn hn').submatrix (finCongr (dif_pos hn')) (finCongr (dif_pos hn))
    else 0
  else 0

/-- Construct computational input from coordinates and matrices only on the finite support. -/
def ofSupport
    (hd : ∀ n (hn : n ∈ K.support) (hn' : n + 1 ∈ K.support) x,
      e ⟨n + 1, hn'⟩ ((F.map (K.d n (n + 1))) x) = d n hn hn' *ᵥ e ⟨n, hn⟩ x) :
    ComputableCohomologyData k K where
  realization := F
  additive := inferInstance
  size := supportSize r
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
abbrev moduleBiproducts (k : Type u) [Field k] : ComputableBinaryBiproduct (ModuleCat.{u} k) where
  computableBinaryBiproductData M N :=
    BinaryBiproductData.mkOfProduct M N (ModuleCat.of k (M × N))
      (ModuleCat.ofHom (LinearMap.fst k M N)) (ModuleCat.ofHom (LinearMap.snd k M N))
      (fun _ f g => ModuleCat.ofHom (f.hom.prod g.hom))
      (by intros; rfl) (by intros; rfl) (by intros; rfl)

/-- The zero-dimensional coordinate module is an explicit zero object. -/
abbrev moduleZero (k : Type u) [Field k] : HasExplicitZeroObject (ModuleCat.{u} k) :=
  .mkOfPreadditive _ (ModuleCat.of k (Fin 0 → k))
    (fun _ f => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      have : x = 0 := Subsingleton.elim _ _
      simp [this])
    (fun _ _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact Subsingleton.elim _ _)

/-- Extend an additive module realization using the existing computable additive completion. -/
def extendRealization (F : C ⥤ ModuleCat.{u} k) [F.Additive] : CMat_ C ⥤ ModuleCat.{u} k :=
  letI := moduleBiproducts k
  letI := moduleZero k
  CMat_.extend F

instance (F : C ⥤ ModuleCat.{u} k) [F.Additive] : (extendRealization F).Additive := by
  unfold extendRealization
  infer_instance

end ComputableCohomologyData
