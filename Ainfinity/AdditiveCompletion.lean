import Mathlib

open CategoryTheory

structure AdditiveCompletion (C : Type*) where
  ofList ::
    toList : List C

abbrev AdditiveCompletion.length {C : Type*} (X : AdditiveCompletion C) : ℕ :=
  X.toList.length

variable {R : Type*} [CommRing R]
  {C : Type*} [Category C] [Preadditive C] [Linear R C]

instance : Category (AdditiveCompletion C) where
  Hom X Y := DMatrix (Fin X.length) (Fin Y.length) (fun i j ↦ X.toList[i] ⟶ Y.toList[j])
  id X i j := if h : i = j then eqToHom (congrArg _ h) else 0
  comp {X Y Z} f g := g * f
