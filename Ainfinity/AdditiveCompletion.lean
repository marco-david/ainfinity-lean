import Mathlib

open CategoryTheory

structure CMat_ (C : Type*) where
  ofList ::
    toList : List C

namespace CMat_

section definition
variable {C : Type*} [Category C] [Preadditive C] (M N K : CMat_ C)

/-- Mirrors the API of `CategoryTheory.Mat_.ι` -/
def ι : Type := Fin M.toList.length

/- Auxillary definitions that are used to avoid defeq abuse. -/
def ι.toFin (i : M.ι) : Fin M.toList.length := i
def ι.ofFin (i : Fin M.toList.length) : M.ι := i

instance fintype : Fintype M.ι := inferInstanceAs <| Fintype (Fin M.toList.length)
instance : DecidableEq M.ι := inferInstanceAs <| DecidableEq (Fin M.toList.length)

/-- Mirrors the API of `CategoryTheory.Mat_.X` -/
def X : M.ι → C := fun i ↦ M.toList[i.toFin]

/-- Mirrors the API of `CategoryTheory.Mat_.Hom` -/
def Hom : Type* := DMatrix M.ι N.ι fun i j => M.X i ⟶ N.X j

/-- Mirrors the API of `CategoryTheory.Mat_.Hom.id` -/
def Hom.id : Hom M M :=
  fun i j => if h : i = j then eqToHom (congr_arg M.X h) else 0

/-- Mirrors the API of `CategoryTheory.Mat_.Hom.comp` -/
def Hom.comp {M N K : CMat_ C} (f : Hom M N) (g : Hom N K) : Hom M K :=
  fun i k => ∑ j : N.ι, f i j ≫ g j k

instance : Category (CMat_ C) where
  Hom := CMat_.Hom
  id := CMat_.Hom.id
  comp f g := f.comp g
  -- These proofs are based on those in `CategoryTheory.Mat_`.
  -- We add more to the simp set because we don't have a `local simp` attribute immediately above.
  id_comp f := by simp +unfoldPartialApp [dite_comp, Hom.id, Hom.comp]
  comp_id f := by simp +unfoldPartialApp [comp_dite, Hom.id, Hom.comp]
  assoc f g h := by
    apply DMatrix.ext
    intros
    simp_rw [Hom.comp, CategoryTheory.Preadditive.sum_comp, CategoryTheory.Preadditive.comp_sum,
      Category.assoc]
    rw [Finset.sum_comm]

-- These theorems and instances are almost directly copied from `CategoryTheory.Mat_`.
@[ext] theorem hom_ext {M N : CMat_ C} (f g : M ⟶ N) (H : ∀ i j, f i j = g i j) : f = g :=
  DMatrix.ext_iff.mp H
theorem id_def (M : CMat_ C) :
    (𝟙 M : Hom M M) = fun i j => if h : i = j then eqToHom (congr_arg M.X h) else 0 := rfl
theorem id_apply (M : CMat_ C) (i j : M.ι) :
    (𝟙 M : Hom M M) i j = if h : i = j then eqToHom (congr_arg M.X h) else 0 := rfl
@[simp] theorem id_apply_self (M : CMat_ C) (i : M.ι) : (𝟙 M : Hom M M) i i = 𝟙 _ := by
  simp [id_apply]
@[simp] theorem id_apply_of_ne (M : CMat_ C) (i j : M.ι) (h : i ≠ j) : (𝟙 M : Hom M M) i j = 0 := by
  simp [id_apply, h]
theorem comp_def {M N K : CMat_ C} (f : M ⟶ N) (g : N ⟶ K) :
    f ≫ g = fun i k => ∑ j : N.ι, f i j ≫ g j k := rfl
@[simp] theorem comp_apply {M N K : CMat_ C} (f : M ⟶ N) (g : N ⟶ K) (i k) :
    (f ≫ g) i k = ∑ j : N.ι, f i j ≫ g j k := rfl
instance : Inhabited (M ⟶ N) := ⟨fun i j => (0 : M.X i ⟶ N.X j)⟩
instance : AddCommGroup (M ⟶ N) := inferInstanceAs <| AddCommGroup (DMatrix M.ι N.ι _)
@[simp] theorem add_apply {M N : CMat_ C} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j := rfl
instance : Preadditive (CMat_ C) where
  add_comp M N K f f' g := by ext; simp [Finset.sum_add_distrib]
  comp_add M N K f g g' := by ext; simp [Finset.sum_add_distrib]

-- Idea: Maybe we can translate the `HasFiniteBiproducts` instance from `CategoryTheory.Mat_` using
-- an equivalence. I don't know if this would make it computable though, which we might need.

-- We split the equivalence into two parts rather than just having a singular
-- `CategoryTheory.Equivalence` structure because one direction is computable.
def toMat_ : CMat_ C ⥤ Mat_ C where
  obj M := {
    ι := M.ι
    fintype := M.fintype
    X := M.X
  }
  map f := f
  map_id M := by
    rw [id_def, Mat_.id_def]
    convert rfl

noncomputable def fullyFaithful_toMat_ : (toMat_ (C := C)).FullyFaithful := by
  sorry

theorem essSurj_toMat_ : (toMat_ (C := C)).EssSurj := by
  sorry

/-- Computable version of `CategoryTheory.Limits.biprod` -/
def cbiprod : CMat_ C := CMat_.ofList (M.toList ++ N.toList)

@[inherit_doc] infixl:65 " ⊞ₖ " => cbiprod

omit [Category C] [Preadditive C]
theorem cbiprod_assoc : M ⊞ₖ N ⊞ₖ K = M ⊞ₖ (N ⊞ₖ K) := by
  simp [cbiprod]

end definition

section embedding

variable (C : Type*) [Category C] [Preadditive C]

def embedding : C ⥤ CMat_ C where
  obj X := CMat_.ofList [X]
  map {M N} f i j :=
    have : (M ⟶ N) = ((CMat_.ofList [M]).X i ⟶ (CMat_.ofList [N]).X j) := by
      have hi : i.toFin.val = 0 := sorry
      have hj : j.toFin.val = 0 := sorry
      sorry
    cast this f
  map_id f := by sorry
  map_comp f g := by sorry

namespace Embedding
instance : (embedding C).Faithful where
  map_injective h := sorry

instance : (embedding C).Full where
  map_surjective f := sorry

instance : Functor.Additive (embedding C) where
  map_add {M N f g} := sorry
end Embedding

end embedding

-- TODO: Pick a simp normal form
-- TODO: implement Repr using cibiprod and the embedding

section Linear

variable {R : Type*} [CommRing R]
  {C : Type*} [Category C] [Preadditive C] [Linear R C] (M N : CMat_ C)

end Linear

end CMat_
