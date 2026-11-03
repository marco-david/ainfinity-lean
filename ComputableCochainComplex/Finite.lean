/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Int.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Finite free coordinates for bounded cochain complexes

Explicit differential matrices, matrix cochain maps, and their interpretation in mathlib's
module complexes. Rows index targets and columns index sources. The stored finite support is
an upper bound and may contain zero terms. These definitions work over a commutative ring and
do not assume that kernels, images, or cohomology are free.
-/

@[expose] public section

/-- A bounded cochain complex presented in specified finite free coordinates.
The sizes are supplied coordinate counts, and `support` may contain zero-sized terms. -/
structure FiniteFreeCochainComplex (R : Type*) [CommRing R] where
  /-- The number of coordinates in each cohomological degree. -/
  size : ℤ → ℕ
  /-- A finite bound on the degrees with nonzero coordinate count. -/
  support : Finset ℤ
  /-- There are no coordinates outside the stored support bound. -/
  size_eq_zero_of_notMem_support : ∀ n, n ∉ support → size n = 0
  /-- The differential, with target coordinates indexing rows. -/
  d : ∀ n, Matrix (Fin (size (n + 1))) (Fin (size n)) R
  /-- Consecutive differentials compose to zero. -/
  d_mul_d : ∀ n, d (n + 1) * d n = 0

namespace FiniteFreeCochainComplex

variable {R : Type*} [CommRing R] (C : FiniteFreeCochainComplex R)

lemma mem_support_of_size_ne_zero {n : ℤ} (h : C.size n ≠ 0) : n ∈ C.support := by
  by_contra hn
  exact h (C.size_eq_zero_of_notMem_support n hn)

/-- A differential with no source coordinates is zero. -/
lemma d_eq_zero_of_source_size_eq_zero {n : ℤ} (h : C.size n = 0) : C.d n = 0 := by
  ext i j
  exact (Nat.not_lt_zero j.val (h ▸ j.isLt)).elim

/-- A differential with no target coordinates is zero. -/
lemma d_eq_zero_of_target_size_eq_zero {n : ℤ} (h : C.size (n + 1) = 0) :
    C.d n = 0 := by
  ext i j
  exact (Nat.not_lt_zero i.val (h ▸ i.isLt)).elim

lemma d_eq_zero_of_notMem_support {n : ℤ} (h : n ∉ C.support) : C.d n = 0 :=
  C.d_eq_zero_of_source_size_eq_zero (C.size_eq_zero_of_notMem_support n h)

lemma d_eq_zero_of_add_one_notMem_support {n : ℤ} (h : n + 1 ∉ C.support) : C.d n = 0 :=
  C.d_eq_zero_of_target_size_eq_zero (C.size_eq_zero_of_notMem_support (n + 1) h)

instance : Zero (FiniteFreeCochainComplex R) where
  zero :=
    { size := fun _ => 0
      support := ∅
      size_eq_zero_of_notMem_support := fun _ _ => rfl
      d := fun _ => 0
      d_mul_d := fun _ => Matrix.zero_mul _ }

@[simp] lemma zero_size (n : ℤ) : (0 : FiniteFreeCochainComplex R).size n = 0 := rfl

@[simp] lemma zero_support : (0 : FiniteFreeCochainComplex R).support = ∅ := rfl

@[simp] lemma zero_d (n : ℤ) : (0 : FiniteFreeCochainComplex R).d n = 0 := rfl

end FiniteFreeCochainComplex


namespace FiniteFreeCochainComplex

open CategoryTheory

variable {R : Type*} [CommRing R]

/-- A cochain map in finite free coordinates. -/
@[ext]
structure Hom (C D : FiniteFreeCochainComplex R) where
  /-- The component matrix, with target coordinates indexing rows. -/
  f : ∀ n, Matrix (Fin (D.size n)) (Fin (C.size n)) R
  /-- The component matrices commute with the differentials. -/
  comm : ∀ n, D.d n * f n = f (n + 1) * C.d n

/-- The identity cochain map has identity matrices in every degree. -/
def Hom.id (C : FiniteFreeCochainComplex R) : Hom C C where
  f _ := 1
  comm _ := by simp

/-- Compose cochain maps by multiplying the second component matrix by the first. -/
def Hom.comp {C D E : FiniteFreeCochainComplex R} (f : Hom C D) (g : Hom D E) :
    Hom C E where
  f n := g.f n * f.f n
  comm n := by
    rw [← Matrix.mul_assoc, g.comm, Matrix.mul_assoc, f.comm, ← Matrix.mul_assoc]

instance : Category (FiniteFreeCochainComplex R) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext (funext fun n => Matrix.mul_one (f.f n))
  comp_id f := Hom.ext (funext fun n => Matrix.one_mul (f.f n))
  assoc f g h := Hom.ext (funext fun n => (Matrix.mul_assoc (h.f n) (g.f n) (f.f n)).symm)

variable {C D E : FiniteFreeCochainComplex R}

/-- Matrix cochain maps are determined by their components. -/
@[ext] lemma hom_ext {f g : C ⟶ D} (h : ∀ n, f.f n = g.f n) : f = g :=
  Hom.ext (funext h)

@[simp] lemma id_f (C : FiniteFreeCochainComplex R) (n : ℤ) :
    (𝟙 C : C ⟶ C).f n = 1 := rfl

@[simp] lemma comp_f (f : C ⟶ D) (g : D ⟶ E) (n : ℤ) :
    (f ≫ g).f n = g.f n * f.f n := rfl

instance : Zero (C ⟶ D) where
  zero := { f := fun _ => 0, comm := fun _ => by simp }

@[simp] lemma zero_f (n : ℤ) : (0 : C ⟶ D).f n = 0 := rfl

@[simp] lemma comp_zero (f : C ⟶ D) : f ≫ (0 : D ⟶ E) = 0 := by
  apply hom_ext
  intro n
  simp

@[simp] lemma zero_comp (g : D ⟶ E) : (0 : C ⟶ D) ≫ g = 0 := by
  apply hom_ext
  intro n
  simp

/-- A map component with no source coordinates is zero. -/
lemma Hom.f_eq_zero_of_source_size_eq_zero (f : C ⟶ D) {n : ℤ} (h : C.size n = 0) :
    f.f n = 0 := by
  ext i j
  exact (Nat.not_lt_zero j.val (h ▸ j.isLt)).elim

/-- A map component with no target coordinates is zero. -/
lemma Hom.f_eq_zero_of_target_size_eq_zero (f : C ⟶ D) {n : ℤ} (h : D.size n = 0) :
    f.f n = 0 := by
  ext i j
  exact (Nat.not_lt_zero i.val (h ▸ i.isLt)).elim

lemma Hom.f_eq_zero_of_notMem_source_support (f : C ⟶ D) {n : ℤ} (h : n ∉ C.support) :
    f.f n = 0 :=
  f.f_eq_zero_of_source_size_eq_zero (C.size_eq_zero_of_notMem_support n h)

lemma Hom.f_eq_zero_of_notMem_target_support (f : C ⟶ D) {n : ℤ} (h : n ∉ D.support) :
    f.f n = 0 :=
  f.f_eq_zero_of_target_size_eq_zero (D.size_eq_zero_of_notMem_support n h)

end FiniteFreeCochainComplex


namespace FiniteFreeCochainComplex

open CategoryTheory CategoryTheory.Limits
open scoped Matrix

variable {R : Type*} [CommRing R]

/-- Interpret the differential matrices as linear maps of finite coordinate modules. -/
def toCochainComplex (C : FiniteFreeCochainComplex R) : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of R (Fin (C.size n) → R))
    (fun n => ModuleCat.ofHom (C.d n).mulVecLin) (fun n => by
      apply ModuleCat.hom_ext
      change (C.d (n + 1)).mulVecLin.comp (C.d n).mulVecLin = 0
      rw [← Matrix.mulVecLin_mul, C.d_mul_d, Matrix.mulVecLin_zero])

@[simp] lemma toCochainComplex_X (C : FiniteFreeCochainComplex R) (n : ℤ) :
    C.toCochainComplex.X n = ModuleCat.of R (Fin (C.size n) → R) := rfl

@[simp] lemma toCochainComplex_d (C : FiniteFreeCochainComplex R) (n : ℤ) :
    C.toCochainComplex.d n (n + 1) = ModuleCat.ofHom (C.d n).mulVecLin :=
  CochainComplex.of_d _ _ _ n

/-- The interpreted differential acts by matrix-vector multiplication. -/
lemma toCochainComplex_d_apply (C : FiniteFreeCochainComplex R) (n : ℤ)
    (x : Fin (C.size n) → R) :
    (C.toCochainComplex.d n (n + 1)).hom x = C.d n *ᵥ x := by
  rw [toCochainComplex_d]
  rfl

/-- The supplied support bound also bounds the interpreted module complex. -/
lemma isZero_toCochainComplex_X (C : FiniteFreeCochainComplex R) {n : ℤ}
    (h : n ∉ C.support) : IsZero (C.toCochainComplex.X n) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  change Subsingleton (Fin (C.size n) → R)
  rw [C.size_eq_zero_of_notMem_support n h]
  infer_instance

/-- Interpret a matrix cochain map using the supplied finite coordinates. -/
def Hom.toCochainMap {C D : FiniteFreeCochainComplex R} (f : C ⟶ D) :
    C.toCochainComplex ⟶ D.toCochainComplex :=
  CochainComplex.ofHom _ _ _ _ _ _ (fun n => ModuleCat.ofHom (f.f n).mulVecLin)
    (fun n => by
      apply ModuleCat.hom_ext
      change (D.d n).mulVecLin.comp (f.f n).mulVecLin =
        (f.f (n + 1)).mulVecLin.comp (C.d n).mulVecLin
      rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, f.comm])

@[simp] lemma Hom.toCochainMap_f {C D : FiniteFreeCochainComplex R} (f : C ⟶ D) (n : ℤ) :
    f.toCochainMap.f n = ModuleCat.ofHom (f.f n).mulVecLin := rfl

/-- Interpreting a component matrix agrees with its action on column vectors. -/
lemma Hom.toCochainMap_f_apply {C D : FiniteFreeCochainComplex R} (f : C ⟶ D) (n : ℤ)
    (x : Fin (C.size n) → R) : (f.toCochainMap.f n).hom x = f.f n *ᵥ x := rfl

@[simp] lemma toCochainMap_id (C : FiniteFreeCochainComplex R) :
    (𝟙 C : C ⟶ C).toCochainMap = 𝟙 C.toCochainComplex := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  exact Matrix.mulVecLin_one

@[simp] lemma toCochainMap_comp {C D E : FiniteFreeCochainComplex R}
    (f : C ⟶ D) (g : D ⟶ E) :
    (f ≫ g).toCochainMap = f.toCochainMap ≫ g.toCochainMap := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  exact Matrix.mulVecLin_mul (g.f n) (f.f n)

@[simp] lemma toCochainMap_zero (C D : FiniteFreeCochainComplex R) :
    (0 : C ⟶ D).toCochainMap = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  exact Matrix.mulVecLin_zero

/-- The correctness bridge from matrix complexes to mathlib's module complexes. -/
def toCochainComplexFunctor : FiniteFreeCochainComplex R ⥤ CochainComplex (ModuleCat R) ℤ where
  obj := toCochainComplex
  map f := f.toCochainMap
  map_id := toCochainMap_id
  map_comp := toCochainMap_comp

@[simp] lemma toCochainComplexFunctor_obj (C : FiniteFreeCochainComplex R) :
    toCochainComplexFunctor.obj C = C.toCochainComplex := rfl

@[simp] lemma toCochainComplexFunctor_map {C D : FiniteFreeCochainComplex R} (f : C ⟶ D) :
    toCochainComplexFunctor.map f = f.toCochainMap := rfl

end FiniteFreeCochainComplex
