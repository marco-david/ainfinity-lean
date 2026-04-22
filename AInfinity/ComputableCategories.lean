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

/--
Computable version of `CategoryTheory.Limits.biprod`.
-/
def cbiprod : C := (computableBinaryBiproductData X Y).bicone.pt

@[inherit_doc] infixl:65 " ⊞ₘ " => cbiprod

abbrev cbiprod.fst {X Y : C} : X ⊞ₘ Y ⟶ X := (computableBinaryBiproductData X Y).bicone.fst
abbrev cbiprod.snd {X Y : C} : X ⊞ₘ Y ⟶ Y := (computableBinaryBiproductData X Y).bicone.snd
abbrev cbiprod.inl {X Y : C} : X ⟶ X ⊞ₘ Y := (computableBinaryBiproductData X Y).bicone.inl
abbrev cbiprod.inr {X Y : C} : Y ⟶ X ⊞ₘ Y := (computableBinaryBiproductData X Y).bicone.inr

@[simp] theorem ComputableBinaryBiproduct.computableBinaryBiproductData_bicone_fst :
  (computableBinaryBiproductData X Y).bicone.fst = cbiprod.fst := rfl
@[simp] theorem ComputableBinaryBiproduct.computableBinaryBiproductData_bicone_snd :
  (computableBinaryBiproductData X Y).bicone.snd = cbiprod.snd := rfl
@[simp] theorem ComputableBinaryBiproduct.computableBinaryBiproductData_bicone_inl :
  (computableBinaryBiproductData X Y).bicone.inl = cbiprod.inl := rfl
@[simp] theorem ComputableBinaryBiproduct.computableBinaryBiproductData_bicone_inr :
  (computableBinaryBiproductData X Y).bicone.inr = cbiprod.inr := rfl
