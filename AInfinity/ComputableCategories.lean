module

public import Mathlib

@[expose] public section

open CategoryTheory Limits

class ComputableBinaryBiproduct (C : Type*) [Category C] [HasZeroMorphisms C] where
  computableBinaryBiproductData (P Q : C) : BinaryBiproductData P Q

open ComputableBinaryBiproduct

variable {C : Type*} [Category C] [HasZeroMorphisms C] [ComputableBinaryBiproduct C] (X Y : C)

/--
If C has computable biproducuts, it also has noncomputable biproducts.
-/
instance : HasBinaryBiproducts C where
  has_binary_biproduct P Q := ⟨⟨computableBinaryBiproductData P Q⟩⟩

abbrev cbicone : BinaryBicone X Y := (computableBinaryBiproductData X Y).bicone

@[simp] theorem ComputableBinaryBiproduct.bicone_computableBinaryBiproductData :
    (computableBinaryBiproductData X Y).bicone = cbicone X Y := rfl

def isBilimit_cbicone : (cbicone X Y).IsBilimit := (computableBinaryBiproductData X Y).isBilimit

/--
Computable version of `CategoryTheory.Limits.biprod`.
-/
def cbiprod : C := (cbicone X Y).pt

@[inherit_doc] infixl:65 " ⊞ᶜ " => cbiprod

abbrev cbiprod.fst {X Y : C} : X ⊞ᶜ Y ⟶ X := (computableBinaryBiproductData X Y).bicone.fst
abbrev cbiprod.snd {X Y : C} : X ⊞ᶜ Y ⟶ Y := (computableBinaryBiproductData X Y).bicone.snd
abbrev cbiprod.inl {X Y : C} : X ⟶ X ⊞ᶜ Y := (computableBinaryBiproductData X Y).bicone.inl
abbrev cbiprod.inr {X Y : C} : Y ⟶ X ⊞ᶜ Y := (computableBinaryBiproductData X Y).bicone.inr
