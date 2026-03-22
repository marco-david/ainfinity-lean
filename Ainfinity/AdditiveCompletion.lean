import Mathlib

open CategoryTheory

-- TODO: Consider renaming to something like `ComputableMat_` or `CMat_`

structure CMat_ (C : Type*) where
  ofList ::
    toList : List C

variable {R : Type*} [CommRing R]
  {C : Type*} [Category C] [Preadditive C] [Linear R C]
  (M N : CMat_ C)

namespace CMat_

/-- Mirrors the API of `CategoryTheory.Mat_.ι` -/
def ι : Type := Fin M.toList.length

/- Auxillary definitions that are used to avoid defeq abuse. -/
def ι.toFin (i : M.ι) : Fin M.toList.length := i
def ι.ofFin (i : Fin M.toList.length) : M.ι := i

instance fintype : Fintype M.ι := inferInstanceAs (Fintype (Fin M.toList.length))
instance : DecidableEq M.ι := inferInstanceAs (DecidableEq (Fin M.toList.length))

/-- Mirrors the API of `CategoryTheory.Mat_.X` -/
def X : M.ι → C := fun i ↦ M.toList[i.toFin]

/-- Mirrors the API of `CategoryTheory.Mat_.Hom` -/
def Hom : Type* := DMatrix M.ι N.ι fun i j => M.X i ⟶ N.X j

/-- Mirrors the API of `CategoryTheory.Mat_.id` -/
def id : Hom M M :=
  fun i j => if h : i = j then eqToHom (congr_arg M.X h) else 0

/-- Mirrors the API of `CategoryTheory.Mat_.comp` -/
def comp {M N K : CMat_ C} (f : Hom M N) (g : Hom N K) : Hom M K :=
  fun i k => ∑ j : N.ι, f i j ≫ g j k

instance : Category (CMat_ C) where
  Hom := CMat_.Hom
  id := CMat_.id
  comp := CMat_.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

end CMat_
