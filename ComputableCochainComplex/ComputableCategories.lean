/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.OfFn

/-!
# Computable categorical constructions

Explicit binary biproduct data and a chosen zero object support executable finite biproducts.
The zero-object class stores only the object and its `IsZero` proof. With zero morphisms,
the unique maps to and from that object are the existing zero morphisms.
-/

@[expose] public section

open CategoryTheory Limits

/-- Build executable biproduct data from a supplied product. Mathlib constructs the
injections and coproduct maps from the product's universal property. -/
abbrev CategoryTheory.Limits.BinaryBiproductData.mkOfProduct
    {C : Type*} [Category C] [Preadditive C] (P Q : C)
    (pt : C) (fst : pt ⟶ P) (snd : pt ⟶ Q) (pair : ∀ X, (X ⟶ P) → (X ⟶ Q) → (X ⟶ pt))
    (pair_fst : ∀ X (f : X ⟶ P) (g : X ⟶ Q), pair X f g ≫ fst = f)
    (pair_snd : ∀ X (f : X ⟶ P) (g : X ⟶ Q), pair X f g ≫ snd = g)
    (pair_eta : ∀ X (h : X ⟶ pt), pair X (h ≫ fst) (h ≫ snd) = h) :
    BinaryBiproductData P Q :=
  let h := BinaryFan.IsLimit.mk (BinaryFan.mk fst snd) (pair _)
    (pair_fst _) (pair_snd _) (fun _ _ m hf hg => by
      rw [← hf, ← hg]
      exact (pair_eta _ m).symm)
  ⟨BinaryBicone.ofLimitCone h, binaryBiconeIsBilimitOfLimitConeOfIsLimit h⟩

section computable_biproduct

/-- Chosen binary biproduct data keeps its objects and structure maps executable. -/
class ComputableBinaryBiproduct (C : Type*) [Category C] [HasZeroMorphisms C] where
  /-- Explicit object, maps, and universal properties for each pair. -/
  computableBinaryBiproductData (P Q : C) : BinaryBiproductData P Q

open ComputableBinaryBiproduct

variable {C : Type*} [Category C] [HasZeroMorphisms C] [ComputableBinaryBiproduct C] (X Y : C)

/--
If C has computable biproducts, it also has noncomputable biproducts.
-/
instance : HasBinaryBiproducts C where
  has_binary_biproduct P Q := ⟨⟨computableBinaryBiproductData P Q⟩⟩

/-- The chosen bicone exposes the maps used to assemble finite sums. -/
abbrev cbicone : BinaryBicone X Y := (computableBinaryBiproductData X Y).bicone

/-- The chosen bicone satisfies both universal properties, certifying finite-sum construction. -/
def isBilimit_cbicone : (cbicone X Y).IsBilimit := (computableBinaryBiproductData X Y).isBilimit

/--
Computable version of `CategoryTheory.Limits.biprod`.
-/
def cbiprod : C := (cbicone X Y).pt

@[inherit_doc] infixl:65 " ⊞ᶜ " => cbiprod

/-- Project an explicit binary sum onto its left summand. -/
abbrev cbiprod.fst {X Y : C} : X ⊞ᶜ Y ⟶ X := (computableBinaryBiproductData X Y).bicone.fst
/-- Project an explicit binary sum onto its right summand. -/
abbrev cbiprod.snd {X Y : C} : X ⊞ᶜ Y ⟶ Y := (computableBinaryBiproductData X Y).bicone.snd
/-- Include the left summand in an explicit binary sum. -/
abbrev cbiprod.inl {X Y : C} : X ⟶ X ⊞ᶜ Y := (computableBinaryBiproductData X Y).bicone.inl
/-- Include the right summand in an explicit binary sum. -/
abbrev cbiprod.inr {X Y : C} : Y ⟶ X ⊞ᶜ Y := (computableBinaryBiproductData X Y).bicone.inr

/-- The left injection followed by the left projection is the identity. -/
@[reassoc (attr := simp)]
theorem cbiprod.inl_fst {X Y : C} :
    (cbiprod.inl : X ⟶ X ⊞ᶜ Y) ≫ cbiprod.fst = 𝟙 X := (cbicone X Y).inl_fst

/-- The left injection followed by the right projection is zero. -/
@[reassoc (attr := simp)]
theorem cbiprod.inl_snd {X Y : C} :
    (cbiprod.inl : X ⟶ X ⊞ᶜ Y) ≫ cbiprod.snd = 0 := (cbicone X Y).inl_snd

/-- The right injection followed by the left projection is zero. -/
@[reassoc (attr := simp)]
theorem cbiprod.inr_fst {X Y : C} :
    (cbiprod.inr : Y ⟶ X ⊞ᶜ Y) ≫ cbiprod.fst = 0 := (cbicone X Y).inr_fst

/-- The right injection followed by the right projection is the identity. -/
@[reassoc (attr := simp)]
theorem cbiprod.inr_snd {X Y : C} :
    (cbiprod.inr : Y ⟶ X ⊞ᶜ Y) ≫ cbiprod.snd = 𝟙 Y := (cbicone X Y).inr_snd

end computable_biproduct

section explicit_zero

/-- A chosen zero object. In a category with zero morphisms, its unique incoming and outgoing
maps are the zero morphisms, so no additional morphism data is needed. -/
class HasExplicitZeroObject (C : Type*) [Category C] where
  /-- The explicit object used for empty biproducts. -/
  zero : C
  /-- The chosen object is both initial and terminal. -/
  isZero : IsZero zero

notation "𝟎" => HasExplicitZeroObject.zero

variable {C : Type*} [Category C] [HasExplicitZeroObject C]

/-- Certify the explicit zero object when constructing support bounds for categorical complexes. -/
theorem isZero_explicitZero : IsZero (𝟎 : C) := HasExplicitZeroObject.isZero

/-- Forget the explicit choice when Mathlib only needs existence of a zero object. -/
instance : HasZeroObject C where
  zero := ⟨𝟎, isZero_explicitZero⟩

end explicit_zero

/-- Evaluate a finite list of summands by an executable left fold, starting at the chosen zero. -/
def List.cbiprod {C : Type*} [Category C] [HasZeroMorphisms C] [ComputableBinaryBiproduct C]
  [HasExplicitZeroObject C] : List C → C := foldl (· ⊞ᶜ ·) 𝟎

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [Preadditive C]
  [ComputableBinaryBiproduct C] [HasExplicitZeroObject C]

/-- A computable bicone formed by adjoining the summands from left to right. -/
def finCBicone : {n : ℕ} → (f : Fin n → C) → Bicone f
  | 0, f => {
      pt := 𝟎
      π i := Fin.elim0 i
      ι i := Fin.elim0 i
      ι_π i := Fin.elim0 i }
  | n + 1, f =>
      let b := finCBicone (fun i => f i.castSucc)
      {
        pt := b.pt ⊞ᶜ f (Fin.last n)
        π := Fin.lastCases cbiprod.snd (fun i => cbiprod.fst ≫ b.π i)
        ι := Fin.lastCases cbiprod.inr (fun i => b.ι i ≫ cbiprod.inl)
        ι_π := by
          classical
          intro i j
          induction i using Fin.lastCases <;> induction j using Fin.lastCases
          · simp only [Fin.lastCases_last, cbiprod.inr_snd, ↓reduceDIte, eqToHom_refl]
          · simp only [Fin.lastCases_last, Fin.lastCases_castSucc,
              cbiprod.inr_fst_assoc, zero_comp, (Ne.symm (Fin.castSucc_ne_last _)), ↓reduceDIte]
          · simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Category.assoc,
              cbiprod.inl_snd, comp_zero, Fin.castSucc_ne_last, ↓reduceDIte]
          · simp only [Fin.lastCases_castSucc, Category.assoc, cbiprod.inl_fst_assoc,
              Fin.castSucc_inj]
            simp only [b.ι_π]
            split_ifs <;> rfl }

/-- The computable finite bicone resolves the identity as the sum of its projections. -/
theorem finCBicone_total {n : ℕ} (f : Fin n → C) :
    ∑ i, (finCBicone f).π i ≫ (finCBicone f).ι i = 𝟙 (finCBicone f).pt := by
  induction n with
  | zero =>
    simp only [finCBicone, Fin.sum_univ_zero]
    exact ((IsZero.iff_id_eq_zero _).mp isZero_explicitZero).symm
  | succ n ih =>
    simp only [finCBicone, Fin.sum_univ_castSucc, Fin.lastCases_castSucc, Fin.lastCases_last]
    simp_rw [← Category.assoc]
    erw [← Preadditive.sum_comp (C := C) Finset.univ]
    simp_rw [Category.assoc]
    erw [← Preadditive.comp_sum (C := C) Finset.univ]
    rw [ih, Category.comp_id]
    exact IsBilimit.binary_total (isBilimit_cbicone _ _)

/-- The finite bicone has the same underlying object as the left fold of its summands. -/
theorem finCBicone_pt {n : ℕ} (f : Fin n → C) :
    (finCBicone f).pt = (List.ofFn f).cbiprod := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finCBicone, List.ofFn_succ_last, List.cbiprod, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    rw [ih]
    rfl

end CategoryTheory.Limits
