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
      (inl := pair P (𝟙 P) 0)
      (inr := pair Q 0 (𝟙 Q))
      (pair := pair)
      (copair := fun X f g => fst ≫ f + snd ≫ g)
      -- These proofs were written by Claude code
      (inl_fst := pair_fst P (𝟙 P) 0) (inl_snd := pair_snd P (𝟙 P) 0)
      (inr_fst := pair_fst Q 0 (𝟙 Q)) (inr_snd := pair_snd Q 0 (𝟙 Q))
      (pair_fst := pair_fst)
      (pair_snd := pair_snd)
      (inl_copair := fun X f g => by
        simp only [Preadditive.comp_add, ← Category.assoc, pair_fst, pair_snd,
          Category.id_comp, zero_comp, add_zero])
      (inr_copair := fun X f g => by
        simp only [Preadditive.comp_add, ← Category.assoc, pair_fst, pair_snd,
          Category.id_comp, zero_comp, zero_add])
      (pair_eta := pair_eta)
      (copair_eta := fun X h => by
        have key : fst ≫ pair P (𝟙 P) 0 + snd ≫ pair Q 0 (𝟙 Q) = 𝟙 pt := by
          have h1 : pair pt fst snd = fst ≫ pair P (𝟙 P) 0 + snd ≫ pair Q 0 (𝟙 Q) := by
            have := pair_eta pt (fst ≫ pair P (𝟙 P) 0 + snd ≫ pair Q 0 (𝟙 Q))
            simp only [Preadditive.add_comp, Category.assoc, pair_fst, pair_snd,
              Category.comp_id, comp_zero, add_zero, zero_add] at this
            exact this
          have h2 : pair pt fst snd = 𝟙 pt := by
            have := pair_eta pt (𝟙 pt)
            simp only [Category.id_comp] at this
            exact this
          exact h1.symm.trans h2
        simp only [← Category.assoc, ← Preadditive.add_comp, key, Category.id_comp])

section computable_biproduct

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

end computable_biproduct

section explicit_zero

class HasExplicitZeroObject (C : Type*) [Category C] where
  zero : C
  uniqueTo (Y : C) : Unique (zero ⟶ Y)
  uniqueFrom (Y : C) : Unique (Y ⟶ zero)

notation "𝟎" => HasExplicitZeroObject.zero

variable {C : Type*} [Category C] [HasExplicitZeroObject C]

instance (Y : C) : Unique (𝟎 ⟶ Y) := HasExplicitZeroObject.uniqueTo Y
instance (Y : C) : Unique (Y ⟶ 𝟎) := HasExplicitZeroObject.uniqueFrom Y

def explicitZeroTo (Y : C) : 𝟎 ⟶ Y := default
def explicitZeroFrom (Y : C) : Y ⟶ 𝟎 := default

theorem explicitZeroTo_eq_zero [HasZeroMorphisms C] (Y : C) : explicitZeroTo Y = 0 :=
  (Unique.uniq _ 0).symm

theorem explicitZeroFrom_eq_zero [HasZeroMorphisms C] (Y : C) : explicitZeroFrom Y = 0 :=
  (Unique.uniq _ 0).symm

theorem isZero_explicitZero : IsZero (𝟎 : C) := ⟨fun _ ↦ ⟨inferInstance⟩, fun _ ↦ ⟨inferInstance⟩⟩

/--
Special constructor for preadditive categories
-/
abbrev HasExplicitZeroObject.mkOfPreadditive (C : Type*) [Category C] [Preadditive C]
    (zero : C) (h₁ : ∀ (Y : C) (h : zero ⟶ Y), h = 0) (h₂ : ∀ (Y : C) (h : Y ⟶ zero), h = 0)
    : HasExplicitZeroObject C where
  zero := zero
  uniqueTo Y := ⟨⟨0⟩, h₁ Y⟩
  uniqueFrom Y := ⟨⟨0⟩, h₂ Y⟩

instance : HasZeroObject C where
  zero := ⟨𝟎, isZero_explicitZero⟩

end explicit_zero
