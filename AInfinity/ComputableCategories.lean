module

public import Mathlib

@[expose] public section

open CategoryTheory Limits

abbrev CategoryTheory.Limits.BinaryBiproductData.mkOfMaps
    {C : Type*} [Category C] [HasZeroMorphisms C] (P Q : C)
    (pt : C) (fst : pt ⟶ P) (snd : pt ⟶ Q) (inl : P ⟶ pt) (inr : Q ⟶ pt)
    (pair : ∀ X, (X ⟶ P) → (X ⟶ Q) → (X ⟶ pt)) (copair : ∀ X, (P ⟶ X) → (Q ⟶ X) → (pt ⟶ X))
    (inl_fst : inl ≫ fst = 𝟙 P := by aesop) (inl_snd : inl ≫ snd = 0 := by aesop)
    (inr_fst : inr ≫ fst = 0 := by aesop) (inr_snd : inr ≫ snd = 𝟙 Q := by aesop)
    (pair_fst : ∀ X (f : X ⟶ P) (g : X ⟶ Q), pair X f g ≫ fst = f := by aesop)
    (pair_snd : ∀ X (f : X ⟶ P) (g : X ⟶ Q), pair X f g ≫ snd = g := by aesop)
    (inl_copair : ∀ X (f : P ⟶ X) (g : Q ⟶ X), inl ≫ copair X f g = f := by aesop)
    (inr_copair : ∀ X (f : P ⟶ X) (g : Q ⟶ X), inr ≫ copair X f g = g := by aesop)
    (pair_eta : ∀ X (h : X ⟶ pt), pair X (h ≫ fst) (h ≫ snd) = h := by aesop)
    (copair_eta : ∀ X (h : pt ⟶ X), copair X (inl ≫ h) (inr ≫ h) = h := by aesop)
    : BinaryBiproductData P Q where
  bicone := ⟨pt, fst, snd, inl, inr, inl_fst, inl_snd, inr_fst, inr_snd⟩
  isBilimit := {
    isLimit := {
      lift s := pair s.pt (s.π.app ⟨.left⟩) (s.π.app ⟨.right⟩)
      fac s j := by
        -- Written by Claude code
        rcases j with ⟨_ | _⟩
        · rw [BinaryBicone.toCone_π_app_left]; exact pair_fst _ _ _
        · rw [BinaryBicone.toCone_π_app_right]; exact pair_snd _ _ _
      uniq s m hm := by
        -- Written by Claude code
        have hl := hm ⟨.left⟩
        have hr := hm ⟨.right⟩
        simp [BinaryBicone.toCone_π_app_left] at hl
        simp [BinaryBicone.toCone_π_app_right] at hr
        rw [← hl, ← hr]
        exact (pair_eta s.pt m).symm
    }
    isColimit := {
      desc s := copair s.pt (s.ι.app ⟨.left⟩) (s.ι.app ⟨.right⟩)
      fac s j := by
        -- Written by Claude code
        rcases j with ⟨_ | _⟩
        · rw [BinaryBicone.toCocone_ι_app_left]; exact inl_copair _ _ _
        · rw [BinaryBicone.toCocone_ι_app_right]; exact inr_copair _ _ _
      uniq s m hm := by
        -- Written by Claude code
        have hl := hm ⟨.left⟩
        have hr := hm ⟨.right⟩
        simp [BinaryBicone.toCocone_ι_app_left] at hl
        simp [BinaryBicone.toCocone_ι_app_right] at hr
        rw [← hl, ← hr]
        exact (copair_eta s.pt m).symm
    }
  }

/--
In a preadditive category, you can construct a binary biproduct out of a product.
-/
abbrev CategoryTheory.Limits.BinaryBiproductData.mkOfProduct
    {C : Type*} [Category C] [Preadditive C] (P Q : C)
    (pt : C) (fst : pt ⟶ P) (snd : pt ⟶ Q) (pair : ∀ X, (X ⟶ P) → (X ⟶ Q) → (X ⟶ pt))
    (pair_fst : ∀ X (f : X ⟶ P) (g : X ⟶ Q), pair X f g ≫ fst = f := by aesop)
    (pair_snd : ∀ X (f : X ⟶ P) (g : X ⟶ Q), pair X f g ≫ snd = g := by aesop)
    (pair_eta : ∀ X (h : X ⟶ pt), pair X (h ≫ fst) (h ≫ snd) = h := by aesop)
    : BinaryBiproductData P Q := .mkOfMaps P Q pt
      (fst := fst)
      (snd := snd)
      (inl := sorry)
      (inr := sorry)
      (pair := pair)
      (copair := sorry)
      (inl_fst := sorry) (inl_snd := sorry)
      (inr_fst := sorry ) (inr_snd := sorry)
      (pair_fst := pair_fst)
      (pair_snd := pair_snd)
      (inl_copair := sorry)
      (inr_copair := sorry)
      (pair_eta := sorry)
      (copair_eta := sorry)

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
