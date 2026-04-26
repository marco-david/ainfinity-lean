module

public import Mathlib

@[expose] public section

open CategoryTheory Limits

abbrev BinaryBiproductData.mkOfMaps {C : Type*} [Category C] [HasZeroMorphisms C] (P Q : C)
    (pt : C) (fst : pt ⟶ P) (snd : pt ⟶ Q) (inl : P ⟶ pt) (inr : Q ⟶ pt)
    (pair : ∀ X, (X ⟶ P) → (X ⟶ Q) → (X ⟶ pt)) (copair : ∀ X, (P ⟶ X) → (Q ⟶ X) → (pt ⟶ X))
    (inl_fst : inl ≫ fst = 𝟙 P := by aesop) (inl_snd : inl ≫ snd = 0 := by aesop)
    (inr_fst : inr ≫ fst = 0 := by aesop) (inr_snd : inr ≫ snd = 𝟙 Q := by aesop)
    (pair_fst : ∀ X (f : X ⟶ P) (g : X ⟶ Q), pair X f g ≫ fst = f := by aesop)
    (pair_snd : ∀ X (f : X ⟶ P) (g : X ⟶ Q), pair X f g ≫ snd = g := by aesop)
    (inl_copair : ∀ X (f : P ⟶ X) (g : Q ⟶ X), inl ≫ copair X f g = f := by aesop)
    (inr_copair : ∀ X (f : P ⟶ X) (g : Q ⟶ X), inr ≫ copair X f g = g := by aesop)
    : BinaryBiproductData P Q where
  bicone := ⟨pt, fst, snd, inl, inr, inl_fst, inl_snd, inr_fst, inr_snd⟩
  isBilimit := {
    isLimit := {
      lift s := sorry
      fac s j := sorry
      uniq s m := sorry
    }
    isColimit := {
      desc s := sorry
      fac s j := sorry
      uniq s m := sorry
    }
  }

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

noncomputable def cbiprod_iso_biprod : cbiprod X Y ≅ biprod X Y := sorry
