import Mathlib

open CategoryTheory

-- TODO: Consider renaming to something like `ComputableMat_` or `CMat_`

structure AdditiveCompletion (C : Type*) where
  ofList ::
    toList : List C

variable {R : Type*} [CommRing R]
  {C : Type*} [Category C] [Preadditive C] [Linear R C]
  (M N : AdditiveCompletion C)

/-- Mirrors the API of `CategoryTheory.Mat_.ι` -/
def AdditiveCompletion.ι : Type := Fin M.toList.length

/- Auxillary definitions that are used to avoid defeq abuse. -/
def AdditiveCompletion.ι.toFin (i : M.ι) : Fin M.toList.length := i
def AdditiveCompletion.ι.ofFin (i : Fin M.toList.length) : M.ι := i

instance AdditiveCompletion.fintype : Fintype M.ι := inferInstanceAs (Fintype (Fin M.toList.length))
instance : DecidableEq M.ι := inferInstanceAs (DecidableEq (Fin M.toList.length))

/-- Mirrors the API of `CategoryTheory.Mat_.X` -/
def AdditiveCompletion.X : M.ι → C := fun i ↦ M.toList[i.toFin]

/-- Mirrors the API of `CategoryTheory.Mat_.Hom` -/
def AdditiveCompletion.Hom : Type* := DMatrix M.ι N.ι fun i j => M.X i ⟶ N.X j

/-- Mirrors the API of `CategoryTheory.Mat_.id` -/
def AdditiveCompletion.id : Hom M M :=
  fun i j => if h : i = j then eqToHom (congr_arg M.X h) else 0

/-- Mirrors the API of `CategoryTheory.Mat_.comp` -/
def AdditiveCompletion.comp {M N K : AdditiveCompletion C} (f : Hom M N) (g : Hom N K) : Hom M K :=
  fun i k => ∑ j : N.ι, f i j ≫ g j k

instance : Category (AdditiveCompletion C) where
  Hom := AdditiveCompletion.Hom
  id := AdditiveCompletion.id
  comp := AdditiveCompletion.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry
